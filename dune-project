(lang dune 3.12)

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
   (= "5.1.0"))
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
   (<= "4.12.4"))
  (yojson
   (<= "1.7.0"))
  (ocamlformat
   (and
    :dev
    (<= "0.26.1")))
  (ocaml-lsp-server
   (and
    :dev
    (<= "1.17"))))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
