(lang dune 3.19)
(using coq 0.8)
(using menhir 2.0)

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
  (coq-record-update (>= 0.3.4))
  (rocq-stdlib (>= 9.0.0))
 )
)

(warnings (deprecated_coq_lang_lt_08 disabled))
