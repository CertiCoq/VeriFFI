Require Import VeriFFI.examples.uint63nat.prog.
Require Import ZArith.
Require Import Psatz.
Require Import VeriFFI.examples.uint63nat.specs.

Definition description_S := @desc _ S _. 

(* Lemma body_uint63_from_nat_spec :
  semax_body Vprog Gprog
             f_uint63_from_nat
             uint63_from_nat_spec.
Proof.
    start_function. 
    forward. replace (match p with
    | repZ y => odd_Z2val y
    | repOut p0 => GC_Pointer2val p0
    | repNode v => vertex_address g v
    end) with (rep_type_val g p) by reflexivity. 
    forward.
    (* TODO: forward_loop *)
    forward_loop.

    (* Issue report.
    TODO: What does this error tell me? Where should I look? *)
    forward_call (gv, g, p, n, roots, sh, ti, outlier, t_info). 
    forward_while ( EX   (m : nat) p',
        PROP ( is_in_graph g (n - m)%nat p';        
              nat_has_tag_prop (n - m)%nat (nat_get_desc (n-m)%nat))
        LOCAL (temp _t (Vint (Int.repr (Z.of_nat (ctor_tag (nat_get_desc (n - m))))));
        temp _i (Vlong (Int64.repr (Int.signed (Int.repr (Z.of_nat m))))); temp _temp (rep_type_val g p');
        temp _n (rep_type_val g p))  SEP (full_gc g t_info roots outlier ti sh)
    ). 
    - (* Before the loop. *)
      Exists 0%nat.  Exists p. 
      assert ((n -0)%nat = n)  as -> by lia; eauto. 
      entailer!. 
    - (* Condition *)
      entailer!. 
    - (* During the loop. *)
      forward.  autorewrite with norm.
      (* Todo: With HRE. *)
      assert (exists nm', S nm' = (n - m)%nat) as (nm'&eq_nm') by admit. 
      forward_call (gv, g, p', (nm'; tt), roots, sh, ti, outlier, f_info, t_info). 
      { rewrite <- eq_nm' in H1. apply H1. }
      Intros p_nm'.
      autorewrite with norm in *. 
      forward.
      { entailer!. admit. } (* structural stuff, should be easy *)
      forward_call (gv, g, p_nm', nm', roots, sh, ti, outlier, f_info, t_info).
         + sep_apply wand_frame_elim'; entailer!.
         +  admit. (* with H2 - same unfolding problem... *)
         + forward.
           autorewrite with norm. 
           Exists (S m, p_nm').
           entailer!. 
           split3. 
           * (* with H2 - same unfolding problem... *)
             admit. 
           * assert (nm' = n - S m)%nat as -> by lia. eauto.
           * split. 
            --  repeat f_equal. lia.
            -- f_equal. f_equal. admit. (*  autorewrite with norm.  lia.  *)
    - (* After the loop. *)
      assert (n = m)%nat by admit. subst.
      forward.
      { entailer!. }
      entailer!.  
      Search Int64.shl.
      autorewrite with norm.
      f_equal. unfold encode_Z. 
      Search Int64.shl Int64.one. unfold encode_Z in H. unfold Int64.max_signed in H. 
      autorewrite with norm. 
      Search Int64.shl. 
      rewrite Int64.shl_mul_two_p. autorewrite with norm. unfold two_p. 
      unfold two_power_pos. 
      rewrite !Int.signed_repr; try rep_lia. 
      f_equal. 
      split; try rep_lia. unfold max_signed in *. unfold Int.max_signed. clear - H. simpl in *.
      Locate "*".
      Search Z.mul.
      rewrite Z.mul_comm in H. 
      Search Z.le Z.mul.

      (* Todo: Work on postcondition. *)
     admit.
Admitted. *)


Lemma body_uint63_to_nat_spec :
  semax_body Vprog Gprog
             f_uint63_to_nat
             uint63_to_nat_spec.
Proof. 
  start_function.
  forward. unfold full_gc. Intros. 
  forward_call (gv, g). 
   assert ( Vlong (Int64.shru (Int64.repr (encode_Z (Z.of_nat n))) (Int64.repr (Int.unsigned (Int.repr 1)))) = Vlong (Int64.repr  (Z.of_nat n)))  as ->.
    { unfold encode_Z. 
    autorewrite with norm. Search Int64.shru . rewrite Int64.shru_div_two_p. 
    unfold two_p.  Search Int64.unsigned Int64.repr. simpl. 
    
    admit. (* TODO *)  } 
  (*   Print bool_type. *)

  forward_while 
  (EX v : rep_type, EX m : nat, EX g' : graph, EX (t_info : GCGraph.thread_info),
  PROP (is_in_graph g' m v; (m <= n)%nat; Z.of_nat (n - m) < headroom t_info; 
  gc_graph_iso g roots g' roots)
   LOCAL (temp _temp (rep_type_val g' v);
   temp _i (Vlong (Int64.repr (Z.of_nat (n - m))));
   temp _tinfo ti; temp _t (Vlong (Int64.repr (Z.of_nat n))))
   SEP (full_gc g' t_info roots outlier ti sh)
  ). 

  - (* Before the while *)
    Intros v. Exists v. Exists 0%nat. Exists g. Exists t_info. entailer!. 
    + split.
      * apply gc_graph_iso_refl.
      * repeat f_equal. lia.
    +  unfold full_gc. entailer!. 
  - (* Valid condition  *)
    entailer!. 
  - (* During the loop *)
    assert (n - m <> 0)%nat.
    {  destruct (n-m)%nat eqn:EQ_mn; eauto. 
      simpl in HRE. normalize in HRE. 
      Print typed_true. unfold typed_true in HRE. simpl in HRE. 
      unfold Int64.zero in HRE. unfold Int64.eq in HRE. 
      if_tac in HRE; eauto. simpl in HRE. congruence.
    }
    forward_call (gv, g', [v], (m%nat; tt) , roots, sh, ti, outlier, f_info, t_info0). 
    { (* Requiring to unfold - TODO: Generate example file for Joomy. *)
       admit. }
    Intros v'.  destruct v' as ((v'&g'')&ti').
    unfold fst, snd in *. 
     forward. 
     Exists (v', S m, g'', ti').
     entailer!. 
    split; eauto. 
     + eapply gc_graph_iso_trans; eauto.  
     + repeat f_equal.  lia.  
  - forward. 
    { unfold full_gc. entailer!.  }
  
    Exists v. Exists g'. Exists t_info0.
    entailer!. 

    enough (n- m = 0)%nat. 
    { assert (n = m) by lia. subst. eauto. }
    red in HRE.  
    unfold strict_bool_val in HRE. simpl in HRE. 
unfold Int64.zero in HRE. 
    Search (Int64.eq (Int64.repr _) (Int64.repr _)).
    clear -HRE.

    destruct (n-m)%nat eqn:EQ_mn; eauto. 
    simpl in HRE. normalize in HRE. 
    unfold typed_false in HRE. simpl in HRE. 
    unfold Int64.eq in HRE. if_tac in HRE; simpl in *; try congruence. 
    revert H6. Search Int64.unsigned Int64.zero. 
    rewrite Int64.unsigned_zero. 
  admit. 
Admitted.



