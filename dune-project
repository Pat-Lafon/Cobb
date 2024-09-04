(lang dune 3.9)

(name Cobb)

(generate_opam_files true)

(source
 (github Pat-Lafon/Cobb))

(authors "Patrick LaFontaine")

(maintainers "Patrick LaFontaine")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name Cobb)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  dune
  (ocaml
   (= "4.14.0"))
  (pomap
   (= "4.1.1"))
  (core
   (<= "v0.16.2"))
  (core_unix
   (<= "v0.16.0"))
  (dolog
   (<= "6.0.0"))
  (ocolor
   (<= "1.3.1"))
  (qcheck
   (<= "0.21.3"))
  (z3
   (<= "4.13.0"))
  (yojson
   (<= "1.7.0"))
  (ocamlformat
   (= "0.26.1"))
  (ocaml-lsp-server
   (= "1.15.1")))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
