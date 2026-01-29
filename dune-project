(lang dune 3.19)
(using coq 0.8)

(generate_opam_files true)
(name quartz)
(version 0.0.1)

(package
 (name quartz)
 (synopsis "")
 (depends 
  (coq (>= 9.0))
  (coq-stdpp (>= 1.11.0))
  (coq-stdpp-bitvector (>= 1.11.0))
  (rocq-stdlib (>= 9.0.0))
 )
)

(warnings (deprecated_coq_lang_lt_08 disabled))
