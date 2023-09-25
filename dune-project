(lang dune 3.9)

(name Cobb)

(generate_opam_files true)

(source
 (github Pat-Lafon/Cobb))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name Cobb)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
     dune
    (ocaml            (= "4.14.0"))
    (core             (<= "v0.16.1"))
    (core_unix        (<= "v0.16.0"))
    (dolog            (<= "6.0.0"))
    (ocolor           (<= "1.3.1"))
    (qcheck           (<= "0.21.2"))
    (z3               (<= "4.12.2-1"))
    (ocamlformat      (and :dev (<= "0.26.1")))
    (ocaml-lsp-server (and :dev (<= "1.16.2"))))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
