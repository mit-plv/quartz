(lang dune 3.21)
(using rocq 0.11)

(generate_opam_files true)
(name quartz)
(version 0.0.1)

(package
 (name quartz)
 (synopsis "")
 (depends 
  (rocq-core (>= 9.0))
  (rocq-stdlib (>= 9.1.0))
 )
)
