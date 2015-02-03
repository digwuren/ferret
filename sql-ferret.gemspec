Gem::Specification.new do |s|
  s.name = 'sql-ferret'
  s.version = '0.4.0'
  s.date = '2015-02-03'
  s.homepage = 'https://github.com/digwuren/ferret'
  s.summary = 'Navigational database style wrapper around SQLite'
  s.author = 'Andres Soolo'
  s.email = 'dig@mirky.net'
  s.files = File.read('Manifest.txt').split(/\n/)
  s.license = 'GPL-3'
  s.description = <<EOD
The SQL Ferret provides a navigational database style wrapper around SQLite.

EXPERIMENTAL!  The API and both DSLs are subject to change!
EOD
  s.has_rdoc = false
  s.add_runtime_dependency 'ugh', '~> 1.0.0'
end
