(lang dune 3.7)

(name Cobb)

(generate_opam_files true)

(source
 (github Pat-Lafon/Cobb))

(authors "Patrick LaFontaine")

(maintainers "Patrick LaFontaine")

(license "MIT")

(documentation https://url/to/documentation)

(package
 (name Cobb)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  dune
  (ocaml
   (>= "5.1.0"))
  (pomap
   (= "4.1.1"))
  (core
   (<= "v0.17.1"))
  (core_unix
   (<= "v0.17.0"))
  (dolog
   (<= "6.0.0"))
  (ocolor
   (<= "1.3.1"))
  (qcheck
   (<= "0.21.3"))
  (z3
   (= "4.15.1"))
  (yojson
   (<= "1.7.0"))
  (ocamlformat
   (= "0.26.1"))
  (ocaml-lsp-server
   (= "1.17.0"))
  (async
   (<= "v0.17.0")))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
