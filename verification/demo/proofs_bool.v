From VC Require Export specs.

Lemma make_bool_true_proof : semax_body Vprog Gprog f_make_Coq_Init_Datatypes_bool_true make_bool_true_spec.
Proof. 
  start_function. 
  forward.
  Exists (repZ 0). entailer!. 
  cbv. intuition (try congruence) . admit. 
Admitted.
