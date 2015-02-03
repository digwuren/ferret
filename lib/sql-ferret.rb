require 'json'
require 'ostruct'
require 'set'
require 'time'
require 'ugh'
require 'yaml'

class Ferret
  module Constants
    QSF_MULTICOL  = 0x01
    QSF_MULTIROW  = 0x02
  end

  attr_reader :schema

  # If the caller can guarantee that this [[Ferret]] instance
  # is never accessed from multiple threads at once, it can
  # turn off using the internal mutex by passing [[use_mutex:
  # false]] for a small performance increase.
  def initialize schema_source, sqlite = nil, use_mutex: true
    raise 'type mismatch' unless schema_source.is_a? String
    super()
    @schema = Ferret::Schema.new(schema_source)
    @sqlite = sqlite
    # Guards access to [[@sqlite]] and
    # [[@sqlite_locked]].
    @sync_mutex = use_mutex ? Mutex.new : nil
    # Are we currently in a transaction?  (This lets us
    # implement [[Ferret#transaction]] reëntrantly.)
    @sqlite_locked = false
    return
  end

  def change table_name, **changes
    ugh? attempted: 'ferret-change' do
      table = @schema[table_name] or
          ugh 'unknown-table', table: table_name
      sql = table.sql_to_change changes.keys.map(&:to_s)
      _sync{@sqlite.execute sql, **changes}
    end
    return
  end

  def insert table_name, **changes
    ugh? attempted: 'ferret-insert' do
      table = @schema[table_name] or
          ugh 'unknown-table', table: table_name
      sql = table.sql_to_insert changes.keys.map(&:to_s)
      _sync do
        @sqlite.execute sql, **changes
        return @sqlite.last_insert_row_id
      end
    end
  end

  def transaction &thunk
    # Note that [[_sync]] is reentrant, too.
    _sync do
      # If we get to this point, the only 'concurrent' access
      # might come from our very own thread -- that is, a
      # subroutine down the execution stack from present.  This
      # means that we can now access [[@sqlite_locked]] as
      # though we were in a single-threading environment, and
      # thus use it as a flag for 'this thread has already
      # acquired the SQLite-level lock so there's no need to
      # engage it again'.  (SQLite's transaction mechanism on
      # its own is not reentrant.)
      if @sqlite_locked then
        return yield
      else
        return @sqlite.transaction do
          begin
            @sqlite_locked = true
            return yield
          ensure
            @sqlite_locked = false
          end
        end
      end
    end
  end

  def _sync &thunk
    if @sync_mutex.nil? or @sync_mutex.owned? then
      return yield
    else
      @sync_mutex.synchronize &thunk
    end
  end
  private :_sync

  def go raw_expr, *inputs, **changes, &thunk
    expr = Ferret::Expression_Parser.new(raw_expr, @schema).expr

    ugh? expr: raw_expr do
      ugh? attempted: 'ferret-go' do
        if inputs.length > expr.exemplars.length then
          ugh 'too-many-exemplars-given',
              expected: expr.exemplars.length,
              given: inputs.length
        elsif inputs.length < expr.exemplars.length then
          ugh 'not-enough-exemplars-given',
              expected: expr.exemplars.length,
              given: inputs.length
        end
      end

      if thunk and ![:select, :select_distinct].
          include? expr.type then
        ugh 'superfluous-thunk-supplied',
            explanation: 'query-not-a-select'
      end

      case expr.type
      when :select, :select_distinct then
        ugh? attempted: 'ferret-select' do
          ugh 'superfluous-changes' \
              unless changes.empty?

          ast = expr.select

          # At least for now, all the parameters behave as
          # simple ANDed filter rules.
          inputs_imply_single_row = false
          coll = Ferret::Parameter_Collector.new
          expr.exemplars.zip(inputs).each_with_index do
              |(exemplar_spec, input), seq_no|
            test, selects_one_p = coll.feed input, exemplar_spec
            inputs_imply_single_row |= selects_one_p
            ast.sql.gsub! /\[test\s+#{seq_no}\]/, test
          end

          # Let's now compose the framework of executing the
          # query from [[proc]]:s.

          # [[tuple_preparer]] takes a tuple of raw values
          # fetched from SQL and prepares it into a deliverable
          # object.
          tuple_preparer = if ast.shape & QSF_MULTICOL == 0 then
            # A single column was requested.  The deliverable
            # object is the piece of data from this column.
            proc do |row|
              Ferret.interpret ast.outputs.values.first,
                  row.first
            end
          else
            # Multiple columns were requested (or one column in
            # multicolumn mode).  The deliverable object is an
            # [[OpenStruct]] mapping field names to data from
            # these fields.
            proc do |row|
              output = OpenStruct.new
              raise 'assertion failed' \
                  unless row.length == ast.outputs.size
              # Note that we're relying on modern Ruby's
              # [[Hash]]'s retention of key order here.
              ast.outputs.to_a.each_with_index do
                  |(name, interpretation), i|
                output[name] =
                    Ferret.interpret interpretation, row[i]
              end
              output
            end
          end

          # [[query_executor]] takes a [[proc]], executes the
          # query, and calls [[proc]] with each tuple prepared
          # by [[tuple_preparer]].
          query_executor = proc do |&result_handler|
            @sqlite.execute ast.sql, **coll do |row|
              result_handler.call tuple_preparer.call(row)
            end
          end

          # [[processor]] executes the query and delivers
          # results either by yielding to [[thunk]] if it has
          # been given or by returning them if not, taking into
          # account the query's shape.
          if thunk then
            # A thunk was supplied -- we'll just pass prepared
            # rows to it.
            processor = proc do
              query_executor.call &thunk
            end
          else
            # Why [[and]] here?  Well, the shape flag tells us
            # whether the query can translate one input to more
            # than one, and [[inputs_imply_single_row]] tells us
            # whether there are more than one input values that
            # thus get translated.  We can only know that the
            # result is a single-row table if both of these
            # preconditions are satisfied.
            if (ast.shape & QSF_MULTIROW == 0) and
                inputs_imply_single_row then
              # A single row was requested (implicitly, by using
              # a unique field as an exemplar).  We'll return
              # this row, or [[nil]] if nothing was found.
              processor = lambda do
                query_executor.call do |output|
                  return output
                end
                return nil
              end
            else
              # Many rows were requested.  We'll collect them to
              # a list and return it.
              processor = proc do
                results = []
                query_executor.call do |output|
                  results.push output
                end
                return results
              end
            end
          end

          _sync &processor
        end

      when :update then
        ugh? attempted: 'ferret-update' do
          ugh 'missing-changes' \
              if changes.empty?

          changed_table = expr.stages.last.table
          sql = "update #{changed_table.name} set "
          changes.keys.each_with_index do |fn, i|
            field = changed_table[fn.to_s]
            ugh 'unknown-field', field: fn,
                    table: changed_table.name,
                    role: 'changed-field' \
                unless field
            sql << ", " unless i.zero?
            sql << "#{field.name} = :#{fn}"
          end

          if expr.stages.length > 1 then
            ast = expr.select
            sql << " where " <<
                expr.stages.last.stalk.ref.name <<
                " in (#{ast.sql})"
          else
            # Special case: the criteria and the update live in
            # a single table, so we won't need to do any joining
            # or subquerying.
            unless expr.exemplars.empty? then
              sql << " " << expr.where_clause
            end
          end

          # We're going to pass the changes to
          # [[SQLite::Database#execute]] in a [[Hash]].
          # Unfortunately, the Ruby interface of SQLite does not
          # support mixing numbered and named arguments.  As a
          # workaround, we'll pass the etalon as a named
          # argument whose name is a number.  This is also
          # convenient because it avoids clashes with any other
          # named parameters -- those are necessarily column
          # names, and column names can not be numbers.
          coll = Ferret::Parameter_Collector.new
          expr.exemplars.zip(inputs).each_with_index do
              |(exemplar_spec, input), seq_no|
            test, selects_one_p = coll.feed input, exemplar_spec
            sql.gsub! /\[test\s+#{seq_no}\]/, test
          end

          _sync do
            @sqlite.execute sql, **coll, **changes
            return @sqlite.changes
          end
        end

      when :delete then
        ugh? attempted: 'ferret-delete' do
          ugh 'superfluous-changes' \
              unless changes.empty?

          affected_table = expr.stages.last.table
          sql = "delete from #{affected_table.name} "

          if expr.stages.length > 1 then
            ast = expr.select
            sql << " where " <<
                expr.stages.last.stalk.ref.name <<
                " in (#{ast.sql})"
          else
            # Special case: the criteria live in the affected
            # table, so we won't need to do any joining or
            # subquerying.
            unless expr.exemplars.empty? then
              sql << " " << expr.where_clause
            end
          end

          coll = Ferret::Parameter_Collector.new
          expr.exemplars.zip(inputs).each_with_index do
              |(exemplar_spec, input), seq_no|
            test, selects_one_p = coll.feed input, exemplar_spec
            sql.gsub! /\[test\s+#{seq_no}\]/, test
          end

          _sync do
            @sqlite.execute sql, **coll
            return @sqlite.changes
          end
        end

      else
        raise 'assertion failed'
      end
    end
  end

  include Constants

  def pragma_user_version
    _sync do
      return @sqlite.get_first_value 'pragma user_version'
    end
  end

  def pragma_user_version= new_version
    raise 'type mismatch' unless new_version.is_a? Integer
    _sync do
      @sqlite.execute 'pragma user_version = ?', new_version
    end
    return new_version
  end

  def create_table name
    ugh? attempted: 'ferret-create-table' do
      _sync do
        @sqlite.execute sql_to_create_table(name)
      end
    end
    return
  end

  def self::interpret interpretation, value
    # If a [[null]] came from the database, we'll interpret it
    # as a [[nil]].
    return nil if value.nil?
    ugh? interpretation: interpretation.to_s,
        input: value.inspect do
      case interpretation
        when nil then
          return value
        when :unix_time, :subsecond_unix_time then
          ugh 'interpreted-value-type-error',
                  input: value.inspect,
                  expected: 'Numeric' \
              unless value.is_a? Numeric
          return Time.at(value)
        when :iso8601 then
          ugh 'interpreted-value-type-error',
                  input: value.inspect,
                  expected: 'String' \
              unless value.is_a? String
          return Time.xmlschema(value)
        when :json, :pretty_json then
          ugh 'interpreted-value-type-error',
                  input: value.inspect,
                  expected: 'String' \
              unless value.is_a? String
          return JSON.parse(value)
        when :yaml then
          ugh 'interpreted-value-type-error',
                  input: value.inspect,
                  expected: 'String' \
              unless value.is_a? String
          return YAML.load(value)
        when :ruby_marshal then
          ugh 'interpreted-value-type-error',
                  input: value.inspect,
                  expected: 'String' \
              unless value.is_a? String
          return Marshal.load(value)
        when :packed_hex then
          ugh 'interpreted-value-type-error',
                  input: value.inspect,
                  expected: 'String' \
              unless value.is_a? String
          ugh 'invalid-hex-data',
                  input: value \
              unless value =~ /\A[\dabcdef]*\Z/
          ugh 'odd-length-hex-data',
                  input: value \
              unless value.length % 2 == 0
          return [value].pack('H*')
        else
          raise 'assertion failed'
      end
    end
  end

  def self::deterpret interpretation, object
    # Note that we're not handling [[nil]] any specially.  If
    # this field permits [[null]] values, it's the caller's --
    # who lives somewhere in the query execution wrapper of
    # Ferret -- to handle [[nil]], and if it doesn't, passing
    # [[nil]] to [[deterpret]] is either an error or, in case of
    # YAML, requires special escaping.
    case interpretation
      when nil then
        return object
      when :unix_time then
        ugh 'deterpreted-value-type-error',
                input: object.inspect,
                expected: 'Time' \
            unless object.is_a? Time
        return object.to_i
      when :subsecond_unix_time then
        ugh 'deterpreted-value-type-error',
                input: object.inspect,
                expected: 'Time' \
            unless object.is_a? Time
        return object.to_f
      when :iso8601 then
        ugh 'deterpreted-value-type-error',
                input: object.inspect,
                expected: 'Time' \
            unless object.is_a? Time
        return object.xmlschema
      when :json then
        return JSON.generate(object)
      when :pretty_json then
        return JSON.pretty_generate(object)
      when :yaml then
        return YAML.dump(object)
      when :ruby_marshal then
        return Marshal.dump(value)
      when :packed_hex then
        ugh 'deterpreted-value-type-error',
                input: object.inspect,
                expected: 'String' \
            unless object.is_a? String
        return object.unpack('H*').first
      else
        raise 'assertion failed'
    end
  end
end

class Ferret::Alias_Generator
  def initialize used_ids
    super()
    @used_ids = Set.new used_ids
    @counter = 0
    return
  end

  def create prefix
    begin
      @counter += 1
      candidate = prefix + @counter.to_s
    end while @used_ids.include? candidate
    @used_ids.add candidate
    return candidate
  end

  def available? id
    return !@used_ids.include?(id)
  end

  def reserve id
    if @used_ids.include? id then
      ugh 'already-reserved', identifier: id
    end
    @used_ids.add id
    return id
  end
end

class Ferret::Schema
  def initialize schema_source
    raise 'type mismatch' unless schema_source.is_a? String
    super()
    @tables = {} # keyed by forced-lowercase names
    lineno = 0
    curtable = nil
    relocs = [] # a list of [[Proc]]:s
    @used_ids = Set.new
        # so we can avoid clashes when generating aliases;
        # forced downcase
    schema_source.each_line do |line|
      line.strip!
      lineno += 1
      ugh? context: 'parsing-ferret-schema',
          input: line,
          lineno: lineno do
        if line.empty? or line[0] == ?# then
          next
        elsif line =~ /^\[\s*(\w+)\s*\]\s*(#|$)/ then
          name = $1
          dname = name.downcase
          ugh 'duplicate table name', table: name \
              if @tables.has_key? dname
          curtable = @tables[dname] = Ferret::Table.new name
          @used_ids.add dname
        elsif line =~ /^(\w+)\s*:\s*/ then
          name, spec = $1, $'
          # Note that [[add_field]] will check the field's name
          # for uniquity.
          curtable.add_field(
              Ferret::Field.new(curtable, name, spec) do |thunk|
                relocs.push thunk
              end)
          @used_ids.add name.downcase
        else
          ugh 'unparseable-line'
        end
      end
    end
    # Now that we have loaded everything, we can resolve the
    # pointers.
    @tables.each_value do |table|
      ugh 'table-without-columns',
              table: table.name \
          unless table.has_columns?
    end
    relocs.each do |thunk|
      thunk.call self
    end
    return
  end

  def alias_generator
    return Ferret::Alias_Generator.new(@used_ids)
  end

  def [] name
    return @tables[name.downcase]
  end

  def tables
    return @tables.values
  end

  def sql_to_create_table name
    table = self[name]
    unless table then
      ugh 'unknown-table',
          table: name
    end
    return table.sql_to_create
  end
end

class Ferret::Table
  attr_reader :name
  def initialize name
    raise 'type mismatch' unless name.is_a? String
    super()
    @name = name
    @fields = {} # keyed by forced-lowercase names
    return
  end

  def [] name
    return @fields[name.downcase]
  end

  def empty?
    return @fields.empty?
  end

  def columns
    return @fields.values.select(&:column?)
  end

  def has_columns?
    return @fields.values.any?(&:column?)
  end

  # FIXME: move to the section for data model
  attr_reader :primary_key

  # [[Table#add_field]] is how new [[Field]]:s get added to a
  # [[Table]] as it gets parsed from a Ferret schema.  Thus, we
  # check for field name duplication and primary key clashes
  # here.  This is also a convenient place to set up
  # [[Table@primary_key]], too, as well as to check against a
  # table having been declared with multiple primary keys.
  def add_field field
    raise 'type mismatch' unless field.is_a? Ferret::Field
    raise 'assertion failed' \
        unless field.table.object_id == self.object_id
    dname = field.name.downcase
    ugh? table: @name do
      ugh 'duplicate-field', field: field.name \
          if @fields.has_key? dname
      if field.primary_key? then
        if @primary_key then
          ugh 'primary-key-clash',
              key1: @primary_key.name,
              key2: field.name
        end
        @primary_key = field
      end
    end
    @fields[dname] = field
    return field
  end

  def sql_to_change given_column_names
    key_column = sole_unique_column_among given_column_names

    given_columns = resolve_column_names given_column_names

    sql = "insert or replace into " + @name +
        "(" + columns.map(&:name).join(', ') + ") "

    ag = Ferret::Alias_Generator.new [@name, *@fields.keys]
    old_alias, new_alias = %w{old new}.map do |prefix|
      ag.available?(prefix) ?
          ag.reserve(prefix) :
          ag.create(prefix)
    end

    # Specify which field values are new and which ones are to
    # be retained (or initialised from defaults)
    sql << "select " << columns.map{|column| '%s.%s' % [
      given_columns.include?(column) ? new_alias : old_alias,
      column.name,
    ]}.join(', ')

    # Encode the changes as a subquery
    sql << " from (select " << given_column_names.map{|fn|
        ":#{fn} as #{fn}"}.join(', ') << ")"

    # Left-join the subquery against the preëxisting table
    sql << (" as %{new} left join %{table} as %{old} " +
        "on %{new}.%{key} = %{old}.%{key}") % {
      :old => old_alias,
      :new => new_alias,
      :key => key_column.name,
      :table => @name,
    }

    return sql
  end

  # Given a list of column names, figure out which of them is
  # the one and only unique (or primary key) field for this
  # table.  Ugh if any of them is not a field name; if any field
  # is mentioned multiple times; if multiple [[unique]] fields
  # are mentioned; or if no [[unique]] fields are mentioned.
  def sole_unique_column_among column_names
    ugh? table: @name do
      given_columns = resolve_column_names column_names
      unique_column = nil
      given_columns.each do |column|
        if column.unique? then
          if unique_column then
            ugh 'unique-column-conflict',
                field1: unique_column.name,
                field2: column.name
          end
          unique_column = column
        end
      end
      ugh 'no-unique-column-given',
              fields: given_columns.map(&:name).join(', '),
              known_unique_fields:
                  @fields.values.select(&:unique?).
                      map(&:name).join(', ') \
          unless unique_column
      return unique_column
    end
  end

  def sql_to_insert given_column_names
    ugh? table: @name do
      # We have to check this, lest we generate broken SQL.
      ugh 'inserting-null-tuple' \
          if given_column_names.empty?

      given_columns = resolve_column_names given_column_names

      # Check that all the mandatory fields are given
      @fields.each_value do |field|
        next if field.optional? or field.default
        next if given_columns.include? field
        # SQLite can autopopulate the [[integer primary key]]
        # field.
        next if field.primary_key? and field.type == 'integer'
        ugh 'mandatory-value-missing',
            table: @name,
            column: field.name,
            given_columns: given_columns.map(&:name).join(' ')
      end

      return "insert into " +
          "#{@name}(#{given_columns.map(&:name).join ', '}) " +
          "values(:#{given_column_names.join ', :'})"
    end
  end

  def resolve_column_names names
    results = []
    names.each do |fn|
      raise 'type mismatch' \
          unless fn.is_a? String
      field = @fields[fn.downcase]
      ugh 'unknown-field', field: fn,
              known_fields: @fields.values.map(&:name).
                  join(', ') \
          unless field
      ugh 'not-a-column', field: field.name \
          unless field.column?
      ugh 'duplicate-field', field: field.name \
          if results.include? field
      results.push field
    end
    return results
  end

  def sql_to_create
    # No trailing semicolon.
    return "create table #{name} (\n  " +
        @fields.values.select(&:column?).
            map(&:sql_to_declare).join(",\n  ") +
        ")"
  end
end

class Ferret::Lexical_Ruleset
  attr_reader :multichar

  def initialize simple: [],
      intertoken: [],
      multichar: []

    raise 'duck type mismatch' \
        unless intertoken.respond_to? :include?
    raise 'duck type mismatch' \
        unless simple.respond_to? :include?
    raise 'duck type mismatch' \
        unless multichar.respond_to? :include?
    super()
    @intertoken = intertoken
    @simple = simple
    @multichar = multichar
    return
  end

  def intertoken? c
    return @intertoken.include? c
  end

  def simple_particle? c
    return @simple.include? c
  end

  def id_starter? c
    return [(?A .. ?Z), (?a .. ?z), [?_]].
        any?{|s| s.include? c}
  end

  def id_continuer? c
    return [(?A .. ?Z), (?a .. ?z), (?0 .. ?9), [?_]].
        any?{|s| s.include? c}
  end
end

Ferret::LEXICAL_RULESET = Ferret::Lexical_Ruleset.new(
    simple: ",:*()'\\<>",
    multichar: %w{-> <-> <= >=},
    intertoken: " \t\n\r\f")

class Ferret::Scanner
  def initialize expr
    raise 'type mismatch' unless expr.is_a? String
    super()
    @expr = expr
    @lex = Ferret::LEXICAL_RULESET

    @offset_ahead = 0
    @token_ahead = nil
    @offset_atail = nil
    @offset_behind = nil
    return
  end

  def _skip_intertoken_space
    loop do
      break if @offset_ahead >= @expr.length
      break unless @lex.intertoken? @expr[@offset_ahead]
      @offset_ahead += 1
    end
    return
  end
  private :_skip_intertoken_space

  def peek_token
    return @token_ahead if @token_ahead

    # Note that [[peek_token]] advances [[@offset_ahead]] to
    # skip over preceding intertoken space but no further.
    # Instead, it'll store the end offset of the peeked token
    # in [[@offset_atail]].
    _skip_intertoken_space

    # check for eof
    if @offset_ahead >= @expr.length then
      @offset_atail = @offset_ahead
      return @token_ahead = nil
    end

    # check for an identifier
    if @lex.id_starter? @expr[@offset_ahead] then
      @offset_atail = @offset_ahead
      loop do
        @offset_atail += 1
        break unless @lex.id_continuer? @expr[@offset_atail]
      end
      return @token_ahead =
          @expr[@offset_ahead ... @offset_atail]
    end

    # check for multi-char particles
    @lex.multichar.each do |etalon|
      if @expr[@offset_ahead, etalon.length] == etalon then
        @offset_atail = @offset_ahead + etalon.length
        return @token_ahead = etalon.to_sym
      end
    end

    # check for single-char particles
    if @lex.simple_particle? @expr[@offset_ahead] then
      @offset_atail = @offset_ahead + 1
      return @token_ahead = @expr[@offset_ahead].chr.to_sym
    end

    # give up
    ugh 'ferret-lexical-error',
        input: @expr,
        offset: @offset_ahead,
        lookahead: @expr[@offset_ahead, 10],
        lookbehind: @expr[
            [@offset_ahead - 10, 0].max ... @offset_ahead]
  end

  def expected! expectation, **extra
    # We'll call [[peek_token]] in advance so that
    # [[@offset_ahead]] would point exactly at the next token.
    tok = peek_token
    ugh('ferret-parse-error',
        expected: expectation,
        got: (tok || '*eof*').to_s,
        input: @expr,
        offset: @offset_ahead,
        **extra)
  end

  def _consume_token_ahead
    raise 'assertion failed' unless @offset_atail
    @offset_behind = @offset_ahead
    @offset_ahead = @offset_atail
    @token_ahead = nil
    @offset_atail = nil
    return
  end
  private :_consume_token_ahead

  def get_optional_id
    tok = peek_token
    if tok.is_a? String then
      _consume_token_ahead
      return block_given? ? yield(tok) : tok
    else
      return nil
    end
  end

  def get_optional_escaped_id expectation
    escaped_p = pass? :'\\'
    if escaped_p then
      return true, get_id(expectation)
    elsif id = get_optional_id then
      return false, id
    else
      return nil
    end
  end

  def get_id expectation
    return (get_optional_id or expected! expectation)
  end

  def pass? etalon
    tok = peek_token
    if tok == etalon then
      _consume_token_ahead
      return true
    else
      return false
    end
  end

  def pass etalon
    pass? etalon or expected! etalon
    return
  end

  def last_token_offset
    return @offset_behind
  end

  def next_token_offset
    _skip_intertoken_space \
        unless @token_ahead
    return @offset_ahead
  end

  def expected_eof!
    expected! '*eof*' unless next_token_offset >= @expr.length
    return
  end
end

class Ferret::Expression
  attr_reader :stages
  attr_reader :selectees
  attr_reader :exemplars
  attr_accessor :multicolumn
  attr_accessor :type

  def initialize
    super()
    @stages = [Ferret::Stage.new(nil, nil, :left)]
    @selectees = []
    @exemplars = []
    @multicolumn = false
    @type = :select # the default
    return
  end

  def assign_stage_qualifiers ag
    raise 'type mismatch' \
        unless ag.is_a? Ferret::Alias_Generator
    table_visit_counts = Hash.new 0 # name => count
    @stages.each_with_index do |stage, i|
      table_visit_counts[stage.table.name] += 1
    end

    # The tables that we visited more than once need
    # distinguishing names.
    @stages.each do |stage|
      stage.qualifier =
          if table_visit_counts[stage.table.name] > 1 then
            ag.create stage.table.name[0]
          else
            stage.table.name
          end
    end
    return
  end

  def from_clause
    clause = "from "
    @stages.each_with_index do |stage, i|
      # In case of a non-query expression -- a modification --,
      # the last stage is empty and mustn't be joined.  It then
      # serves only the purpose of holding the last stalk.
      break if i == @stages.length - 1 and modification?

      unless i.zero? then
        clause << " #{stage.join_type} join "
      end

      clause << stage.table.name << " as " << stage.qualifier

      unless i.zero? then
        clause << " on %s.%s = %s.%s" % [
            stage.parent.qualifier,
                (stage.stalk.haunt || stage.stalk).name,
            stage.qualifier, stage.stalk.ref.name,
        ]
      end
    end
    return clause
  end

  def where_clause
    raise 'assertion failed' if @exemplars.empty?
    clause = "where "
    @exemplars.each_with_index do |exemplar, i|
      clause << " and " unless i.zero?
      # The qualifier is only necessary if the clause has more
      # than one stage.
      if @stages.length > 1 then
        # In the navigational model, the (primary) filter always
        # lives in the zeroth stage.
        clause << @stages[0].qualifier << "."
      end
      clause << exemplar.column.name << " [test #{i}]"
    end
    return clause
  end

  # Prepare a [[select]] statement as an
  # [[Annotated_SQL_Template]].  If this expression represents a
  # query statement, the result will cover the whole query.  If
  # it represents an update statement, the result will cover the
  # subquery that determines key value(s) of records in the last
  # table to update.
  def select
    qualifiers_needed =
        @stages.length != (modification? ? 2 : 1)
    sql_selectees = @selectees.map do |selectee|
      (qualifiers_needed ?
              selectee.stage.qualifier + "." : "") +
          (selectee.field.haunt || selectee.field).name
    end.join(', ')

    outputs = {}
    @selectees.each do |selectee|
      outputs[selectee.output_name.to_sym] =
          selectee.interpretation
    end

    sql = "select"
    sql << " distinct" if @type == :select_distinct
    sql << " " << sql_selectees << " " << from_clause

    sql << " " << where_clause unless @exemplars.empty?

    # Determine the shape of the table
    shape = 0
    shape |= QSF_MULTICOL if @multicolumn
    # If no [[unique]] exemplar field is specified or if any of
    # the joins is performed along a ghost field (i.e.,
    # possibly a 1->n reference), our result will have multiple
    # rows.
    shape |= QSF_MULTIROW \
        unless @exemplars.any?{|ex| ex.column.unique?} and
            !@stages[1 .. -1].any?{|stage| stage.stalk.ghost?}

    return Ferret::Annotated_SQL_Template.new(sql,
        outputs, shape)
  end

  include Ferret::Constants

  def modification?
    case @type
      when :select, :select_distinct then
        return false
      when :update, :insert, :delete then
        return true
      else
        raise 'assertion failed'
    end
  end
end

class Ferret::Expression_Parser
  attr_reader :expr

  def initialize raw_expr, schema
    super()
    @raw_expr = raw_expr
    @schema = schema

    @expr = Ferret::Expression.new
    @scanner = Ferret::Scanner.new @raw_expr

    @first_star_offset = nil

    first_table_name = @scanner.get_id 'table-name'
    @expr.stages[0].table = @schema[first_table_name] or
        ugh 'unknown-table',
             table: first_table_name,
             offset: @scanner.last_token_offset,
             expr: @raw_expr

    @scanner.pass :':'

    parenthesised = @scanner.pass? :'('
    loop do
      exemplar_escaped, exemplar_column_name =
          @scanner.get_optional_escaped_id 'column-expected'
      if exemplar_column_name then
        exemplar_column =
            @expr.stages[0].table[exemplar_column_name] or
                ugh 'unknown-field',
                    field: exemplar_column_name,
                    table: @expr.stages[0].table.name,
                    role: 'key-field',
                    offset: @scanner.last_token_offset,
                    expr: @raw_expr
        # the key column must be a column, not a ghost field
        unless exemplar_column.column? then
          ugh 'not-a-column', field: exemplar_column.name,
              table: @expr.stages[0].table.name,
              offset: @scanner.last_token_offset,
              expr: @raw_expr
        end
        exemplar_interpretation = exemplar_escaped ?
            nil : exemplar_column.interpretation
        key_output_name =
            parse_optional_output_name_override ||
                exemplar_column_name
        @expr.exemplars.push Ferret::Exemplar.new(
            exemplar_column, exemplar_interpretation)
        @expr.selectees.push Ferret::Selectee.new(
            @expr.stages[0], exemplar_column,
            key_output_name, exemplar_interpretation)
      end
      break unless parenthesised and @scanner.pass? :','
    end
    @scanner.pass :')' if parenthesised

    if @scanner.pass? :':' then
      # Colon without dereference: we should expect a fetch
      # verb.
      @expr.type = parse_fetch_verb
    else
      @scanner.pass :'->'

      if @scanner.pass? :':' then
        # Colon past dereference: we should expect an update
        # verb.
        @expr.type = parse_update_verb
      else
        # Note that [[parse_stage]] can change [[@expr.type]]
        # if it meets the [[-> :]].
        parse_stage @expr.stages.last,
            parens: false
      end
    end

    if @expr.modification? then
      if @first_star_offset then
        ugh 'star-in-modification',
            offset: @first_star_offset,
            expr: @raw_expr
      end
    end

    @scanner.expected_eof!

    if @expr.modification? then
      ugh 'multiple-columns-selected-in-modification' \
          if @expr.multicolumn
    end

    unless @expr.multicolumn then
      # In single-column expressions, only the very last
      # selectee is actually selected.
      @expr.selectees[0 ... -1] = []
    end

    @expr.assign_stage_qualifiers @schema.alias_generator
    return
  end

  def start_subsequent_stage parent, stalk, join_type
    raise 'type mismatch' \
        unless parent.is_a? Ferret::Stage
    raise 'type mismatch' \
        unless stalk.is_a? Ferret::Field
    raise 'assertion failed' \
        unless [:left, :inner].include? join_type

    # Note that we don't have the field's offset.  But the
    # caller might.
    unless stalk.ref then
      ugh 'unable-to-dereference', field: field.name
    end

    @expr.stages.push Ferret::Stage.new(
        parent, stalk, join_type)
    return
  end

  def parse_stage stage, parens: false
    starred = false
    stage_empty = true
    loop do
      field_escaped, field_name =
          @scanner.get_optional_escaped_id 'field-expected'
      if field_name then
        field_offset = @scanner.last_token_offset

        raise 'assertion failed' unless stage.table

        field = stage.table[field_name] or
            ugh 'unknown-field', field: field_name,
                expr: @raw_expr,
                offset: field_offset

        field_output_name =
            parse_optional_output_name_override ||
                field_name

        # Has this column, or its name, been used already?
        (0 ... @expr.selectees.length).reverse_each do |i|
          selectee = @expr.selectees[i]
          if (selectee.stage == stage and
                  selectee.field == field) or
              selectee.output_name == field_output_name then
            # Possible conflict detected.
            if selectee.star? then
              # The previous selectee was implicit, added due
              # to star expansion.  We'll just discard it, for
              # explicit fields take precedence.
              @expr.selectees.delete_at i
            else
              ugh 'duplicate-field-in-stage',
                  field: field.name,
                  output_name: field_output_name,
                  expr: @raw_expr,
                  offset: field_offset
            end
          end
        end
        @expr.selectees.push Ferret::Selectee.new(
            stage, field,
            field_output_name, field_escaped ?
                nil : field.interpretation)
        stage_empty = false
        if @scanner.pass? :'(' then
          join_type = parse_optional_join_arrow or
              expected!('join-arrow',
                  candidates: '-> <->')
          # If something goes wrong trying to start a new
          # stage, it must be the last field's fault.
          # ([[start_subsequent_stage]] won't attach the
          # offset to the ugh on its own just because it
          # doesn't _have_ the offset.)
          ugh? offset: field_offset do
            start_subsequent_stage stage, field, join_type
          end
          parse_stage @expr.stages.last,
              parens: true
          @scanner.pass :')'
        else
          if !parens and @scanner.pass? :':' then
            @expr.type = parse_fetch_verb
            break
          end
          if join_type = parse_optional_join_arrow then
            ugh? offset: field_offset do
              start_subsequent_stage stage, field, join_type
            end
            if !parens and @scanner.pass? :':' then
              @expr.type = parse_update_verb
            else
              parse_stage @expr.stages.last,
                  parens: parens
            end
            break
          end
        end
      elsif @scanner.pass? :'*' then
        @first_star_offset ||= @scanner.last_token_offset
        # only one star per stage
        @scanner.expected! 'field-name' if starred
        starred = true
        @expr.multicolumn = true

        stage.table.columns.each do |column|
          # We'll skip columns that have been selected (at
          # this stage) already, or columns whose names have
          # already been used.
          next if @expr.selectees.any? do |selectee|
            (selectee.stage == stage and
                    selectee.column == column) or
                selectee.output_name == column.name
          end
          @expr.selectees.push Ferret::Selectee.new(
              stage, column,
              column.name, column.interpretation,
              true)
        end

        # Note that [[->]] can not appear immediately
        # following a [[*]].
        break
      else
        if stage_empty then
          @scanner.expected! 'field-name'
        end
        break
      end

      if @scanner.pass? :',' then
        @expr.multicolumn = true
      else
        break
      end
    end
    return
  end

  def parse_optional_output_name_override
    if @scanner.pass? :"'" then
      override = @scanner.get_id 'output-name-override'
      @scanner.pass :"'"
      return override
    else
      return nil
    end
  end

  def parse_optional_join_arrow
    return :left if @scanner.pass? :'->'
    return :inner if @scanner.pass? :'<->'
    return nil
  end

  def parse_fetch_verb
    verb = @scanner.get_id 'fetch-verb'
    case verb
      when 'select' then
        return @scanner.pass?('distinct') ?
            :select_distinct : :select
      when 'distinct' then
        return :select_distinct
      else
        ugh 'unknown-fetch-verb',
            got: verb,
            input: @expr,
            offset: @scanner.last_token_offset
    end
  end

  def parse_update_verb
    verb = @scanner.get_id 'update-verb'
    case verb
      when 'update', 'set' then
        return :update
      when 'delete' then
        return :delete
      else
        ugh 'unknown-update-verb',
            got: verb,
            input: @expr,
            offset: @scanner.last_token_offset
    end
  end
end

class Ferret::Stage
  attr_reader :parent
  attr_reader :stalk
  attr_reader :join_type

  attr_accessor :table
  attr_accessor :qualifier

  def initialize parent, stalk, join_type
    raise 'type mismatch' \
        unless parent.nil? or parent.is_a? Ferret::Stage
    raise 'type mismatch' \
        unless parent.nil? ?
            stalk.nil? : stalk.is_a?(Ferret::Field)
    raise 'assertion failed' \
        unless [:left, :inner].include? join_type
    super()
    @parent = parent
    @stalk = stalk
    @join_type = join_type

    # If we have a stalk, it identifies this stage's table.
    # If not (which only happens for the very first stage),
    # the parser will use [[table=]] to set the stage's table
    # a bit later.
    @table = stalk && stalk.ref.table
    @qualifier = nil
    return
  end
end

class Ferret::Field
  def inspect
    result = "#<Ferret::Field #{@table.name}.#{name}: "
    if primary_key? then
      result << 'primary key '
    else
      result << 'optional ' if optional?
      result << 'unique ' if unique?
    end
    if reference? then
      result << 'unconstrained ' if unconstrained?
      result << "ghost #{@haunt.name} " if ghost?
      result << 'ref %s(%s)' % [ref.table.name, ref.name]
    else
      result << (interpretation || type).to_s
    end
    # Note that [[default]] is an unsanitised, unprocessed
    # string extracted from the schema.  In pathological cases,
    # it can potentially contain the [[>]] character.
    result << " = #{default}" if default
    result << '>'
  end

  attr_reader :table

  attr_reader :name

  attr_reader :type

  attr_reader :interpretation

  def unique?
    return (@flags & (FF_PRIMARY_KEY | FF_EXPL_UNIQUE)) != 0
  end

  def optional?
    return (@flags & FF_OPTIONAL) != 0
  end

  def primary_key?
    return (@flags & FF_PRIMARY_KEY) != 0
  end

  def unconstrained?
    return (@flags & FF_UNCONSTRAINED) != 0
  end

  def reference?
    return (@flags & FF_REFERENCE) != 0
  end

  def ghost?
    return (@flags & FF_GHOST) != 0
  end

  def column?
    return (@flags & FF_GHOST) == 0
  end

  attr_reader :haunt

  attr_reader :default

  attr_reader :ref

  # Note that the parser does not look up the referred and
  # haunted columns, for at the parsing time, not all the
  # columns are yet available so trying to look up forward
  # references would spuriously fail.  Instead, it creates
  # 'relocation thunks' and [[yield]]:s them to the caller, who
  # must arrange to have them called (in the same order as they
  # were [[yield]]:ed) after the whole schema has been loaded
  # and which will perform these lookups and fill in the
  # corresponding slots in the structure.
  def initialize table, name, spec, &thunk
    raise 'type mismatch' unless table.is_a? Ferret::Table
    raise 'type mismatch' unless name.is_a? String
    raise 'type mismatch' unless spec.is_a? String
    super()
    @table = table
    @name = name
    unless spec.strip =~ %r{\A
        (
        | (?<primary_key> \b primary \s+ key \s* ,)
        | (?<unique> \b unique \b)
        | (?<optional> \b optional \b)
        | \b ghost \b \s* (?<haunt> \b \w+ \b)
        )\s*
        ( (?<type> \b \w+ \b)
        | (?<unconstrained> \b unconstrained \b \s*)?
          \b ref \b \s* (?<ref_table> \w+)
            ( \s* \( \s* (?<ref_field> \w+) \s* \) )?
        )
        ( \s* = \s* (?<default> [^\s].*) )?
        \Z}x then
      ugh 'invalid-field-specification',
          input: spec
    end

    unless $~['haunt'] then
      # Do we know the type?
      if $~['type'] and !%w{
          integer real varchar text blob iso8601
          unix_time subsecond_unix_time
          json pretty_json yaml
          ruby_marshal packed_hex}.include? $~['type'] then
        ugh 'unknown-type', type: $~['type']
      end
    else
      # The regex above is a bit too permissive.
      if $~['type'] or $~['unconstrained'] or $~['default'] then
        ugh 'invalid-field-specification',
            input: spec
      end
    end

    if $~['primary_key'] and
        ($~['ref_table'] or $~['default']) then
      ugh 'invalid-field-specification',
          input: spec
    end

    @flags = 0
    @flags |= FF_PRIMARY_KEY if $~['primary_key']
    @flags |= FF_EXPL_UNIQUE if $~['unique']
    @flags |= FF_OPTIONAL if $~['optional']

    # The current [[$~]] is unlikely to survive until the
    # relocation thunk gets called, so we'll have to copy
    # [[ref_table]] and [[ref_field]] out of it, into local
    # variables.
    if ref_table_name = $~['ref_table'] then
      @flags |= FF_REFERENCE
      ref_field_name = $~['ref_field']
      yield(proc do |schema|
        raise 'assertion failed' if @ref
        ref_table = schema[ref_table_name]
        ugh 'unknown-table', table: ref_table_name \
            unless ref_table
        ugh? referring_field: @name,
            referring_field_table: @table.name do
          if ref_field_name then
            @ref = ref_table[ref_field_name] or
                ugh 'unknown-field', field: ref_field_name,
                    table: ref_table.name,
                    significance: 'referred'
          else
            @ref = ref_table.primary_key or
                ugh 'no-primary-key', table: ref_table.name,
                    significance: 'referred'
          end
          ugh 'not-a-column', field: @ref.name,
                  table: ref.table.name,
                  significance: 'referred' \
              unless @ref.column?
        end
        @type = @ref.type
      end)
    else
      @type = $~['type']
    end

    if haunt = $~['haunt'] then
      @flags |= FF_GHOST
      yield(proc do |schema|
        ugh? significance: 'relied-on-by-ghost-field',
            ghost_field: @name do
          @haunt = @table[haunt]
          unless @haunt then
            ugh 'unknown-field', field: haunt
          end
          unless @haunt.column? then
            ugh 'not-a-column', field: @haunt.name
          end
          @type ||= @haunt.type
          unless @haunt.type == @type then
            ugh 'ghost-field-type-mismatch',
                field: @name,
                table: @table.name,
                type: @type.downcase,
                haunted_column: @haunt.name,
                haunted_column_type: @haunt.type.downcase
          end
        end
      end)
    end

    @flags |= FF_UNCONSTRAINED if $~['unconstrained']
    @default = $~['default']

    if @type then
        # [[@type]] can be [[nil]] if it's a reference field.
        # Then, the type and interpretation will be later copied
        # from the referred column.
      case @type.downcase
        when 'iso8601', 'json' then
          @interpretation = @type.downcase.to_sym
          @type = 'varchar'
        when 'yaml', 'pretty_json' then
          @interpretation = @type.downcase.to_sym
          @type = 'text'
        when 'ruby_marshal' then
          @interpretation = @type.downcase.to_sym
          @type = 'blob'
        when 'unix_time' then
          @interpretation = @type.downcase.to_sym
          @type = 'integer'
        when 'subsecond_unix_time' then
          @interpretation = @type.downcase.to_sym
          @type = 'real'
        else
          @interpretation = nil
      end
    end

    return
  end

  # [[Ferret::Field]] flags
  FF_PRIMARY_KEY    = 0x01
  FF_EXPL_UNIQUE    = 0x02
  FF_OPTIONAL       = 0x04
  FF_UNCONSTRAINED  = 0x08
  FF_REFERENCE      = 0x10
  FF_GHOST          = 0x20

  def sql_to_declare
    sql = "#@name #@type"
    if primary_key? then
      sql << " primary key"
    else
      sql << " unique" if unique?
      sql << " not null" unless optional?
      sql << " default #@default" if default
    end
    if reference? and !unconstrained? then
      sql << "\n    references %s(%s)" %
          [@ref.table.name, @ref.name]
    end
    return sql
  end
end

# [[sql]] is a [[String]] of the SQL template together with
# placeholders.  [[outputs]] is [[nil]] if this SQL is not a
# query, or a [[Hash]] containing name->interpretation
# mappings (in the order the values are [[select]]:ed by this
# SQL statement) if it is.  [[shape]] describes the expected
# result set that would result, assuming all the inputs are
# single values.
Ferret::Annotated_SQL_Template =
    Struct.new :sql, :outputs, :shape

class Ferret::Selectee
  attr_reader :stage
  attr_reader :field
  attr_reader :output_name
  attr_reader :interpretation

  def initialize stage, field,
      output_name, interpretation,
      star_p = false
    raise 'type mismatch' unless field.is_a? Ferret::Field
    raise 'type mismatch' unless output_name.is_a? String
    super()
    @stage = stage
    @field = field
    @output_name = output_name
    @interpretation = interpretation
    @star_p = star_p
    return
  end

  def star?
    return @star_p
  end
end

class Ferret::Exemplar
  attr_reader :column
  attr_reader :interpretation

  def initialize column, interpretation
    raise 'type mismatch' unless column.is_a? Ferret::Field
    raise 'assertion failed' unless column.column?
    raise 'type mismatch' \
        unless interpretation.nil? \
            or interpretation.is_a? Symbol
    super()
    @column = column
    @interpretation = interpretation
    return
  end
end

class Ferret::Parameter_Collector < Array
  # [[parameter]] can be a plain value, a collection
  # ([[Enumerator]]) of values, or a [[nil]].
  def feed parameter, exemplar_spec
    raise 'type mismatch' \
        unless exemplar_spec.is_a? Ferret::Exemplar
    if parameter.nil? and exemplar_spec.column.optional? then
      test = "is " + _feed(nil)
      selects_one_p = false
    else
      *exemplar_values = *parameter # force to array
      exemplar_values.map! do |value|
        Ferret.deterpret exemplar_spec.interpretation, value
      end
      if exemplar_values.length != 1 then
        test = "in ("
        exemplar_values.each_with_index do |value, i|
          test << ", " unless i.zero?
          test << _feed(value)
        end
        test << ")"
        selects_one_p = false
      else
        test = "= " + _feed(exemplar_values.first)
        selects_one_p = exemplar_spec.column.unique?
      end
    end
    return test, selects_one_p
  end

  # Add the given [[parameter]] to this collector and return a
  # string containing its placeholder, in the form of colon
  # followed by a sequential number (0-based).
  def _feed parameter
    placeholder = length
    push parameter
    return ":#{placeholder}"
  end
  private :_feed

  def to_hash
    h = {}
    each_with_index do |parameter, i|
      h[i.to_s.to_sym] = parameter
    end
    return h
  end
end
