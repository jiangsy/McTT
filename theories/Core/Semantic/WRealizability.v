From Coq Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.WCong Require Import Definitions Lemmas.
From Mctt.Core.Semantic Require Export NbE WPER.
Import Domain_Notations.

Lemma per_nat_then_per_top : forall {n m},
    {{ Dom n ≈≈ m ∈ per_nat }} ->
    {{ Dom ⇓ ℕ n ≈≈ ⇓ ℕ m ∈ per_top }}.
Proof with solve [destruct_conjs; do 2 eexists; repeat split; mauto 3].
  induction 1; simpl in *; intros s;
    try specialize (IHper_nat s);
    try specialize (H s)...
Qed.

#[export]
Hint Resolve per_nat_then_per_top : mctt.

(* This version almost works, but cannot guarantee the readback of type annotations *)
Lemma realize_per_univ_elem_gen_ver_ref : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ b ∈ per_top_typ }}
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - (* subtyp_lowering ? *)
    subst.
    dependent destruction H3. subst. subst.
    invert_per_univ_elem H4. rewrite H4.
    eexists.
    basic_per_univ_elem_econstructor; eauto. reflexivity.
  - subst. dependent destruction H3.
    invert_per_univ_elem H4. rewrite H4 in H5.
    destruct_all.
    destruct_by_head per_univ.
    assert (per_univ_elem j' R' d d') by mauto 3.
    specialize (H2 _ _ _ H3).
    destruct_conjs.
    intro s.
    specialize (H2 s). destruct_all.
    exists C, C'. repeat split; mauto.
  - mauto... 
  - progressive_inversion. intros.
    rewrite H. econstructor; auto.
  - dependent destruction H0.
    dependent destruction H1.
    eapply per_nat_then_per_top; mauto.
    rewrite <- H. auto. 
  - destruct_all.
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H3; mauto 3; saturate_refl; mauto.
    }
    specialize (H1 _ _ H5). destruct_rel_mod_eval.
    destruct_conjs.
    specialize (H4 s) as [? []].
    specialize (H8 (S s)) as [? []].
    destruct_conjs...
  - dependent destruction H3. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_all.
    rewrite H10. intros. 
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel }}. {
      eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
      saturate_refl. auto.
    }
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
    }
    destruct_rel_mod_eval. simplify_evals.
    econstructor; mauto 3.
    eapply H31; mauto 3.
    + transitivity a'1. 
      eapply H4; mauto 3.
      eapply per_subtyp_refl; eauto.
    + saturate_refl. auto.
    + assert {{ Dom ⇓ a'0 c0 ≈≈ ⇓ a' c'0 ∈ per_top }}.
      eapply H15; eauto.
      intros s.
      specialize (H8 s).
      specialize (H21 s). destruct_all...
  - dependent destruction H3. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_conjs.
    intros s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H14; mauto 3; saturate_refl; mauto.
    }
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
      eapply H14; mauto 3; saturate_refl; mauto.
    }
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel) (A:=a); mauto 3.
      saturate_refl. mauto.
    }
    handle_per_univ_elem_irrel.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H19; auto.
    }
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    simplify_evals.
    assert (exists WA WA', {{ Rtyp a0 in s ↘ WA }} /\ {{ Rtyp a' in s ↘ WA' }}) 
      by admit.
    destruct_all.
    assert (per_top d{{{ ⇓ a2 fa0 }}} d{{{ ⇓ a'5 f'a' }}}). {
      eapply H38; mauto 3.
      transitivity a'0. eapply per_subtyp_refl; symmetry; mauto 3.
      transitivity a'2; auto.
      eapply H4 with (c:= d{{{ ⇑! a' s }}} ); mauto 3.
      etransitivity; [symmetry|]; mauto 3.
      eapply per_subtyp_refl; mauto 3.
      etransitivity; [|symmetry]; mauto 3.
    }
    specialize (H28 (S s)). destruct_all.
    do 2 eexists; repeat split; econstructor; mauto 3.
  - intro s. 
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all...
  - progressive_inversion.
    rewrite H10. econstructor; auto.
  - intros s. progressive_inversion.
    subst.
    rewrite H10 in H3. dependent destruction H3.
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all... 
Admitted.

Lemma realize_per_univ_elem_gen_ver7 : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    ( {{ Dom a ≈≈ b ∈ per_top_typ }}
         /\ (forall {a'}, {{ Sub a <: a' at i }} ->
                {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
         /\ (forall {a'}, {{ Sub a' <: a at i }} ->
                {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
        )
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' c c' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ a' c' ∈ R' }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with try (solve [try (try (do 2 eexists; split); econstructor); mauto]).
    intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + subst...
    + subst. invert_per_univ_elem H5.
      rewrite H5. econstructor.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + invert_per_univ_elem H5. 
      rewrite H6. eexists.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + subst. invert_per_univ_elem H5. 
      apply_relation_equivalence.
      destruct_all. 
      assert (per_univ_elem j' R' d d') by mauto 3.
      specialize (H2 _ _ _ H0). destruct_all.
      intro s.
      specialize (H1 s). destruct_all...

  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + invert_per_univ_elem H1; intuition.
    + invert_per_univ_elem H1; intuition.
    + invert_per_univ_elem H1; intuition.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H).
    + destruct_all.
      intro s.
      assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
        eapply H4; mauto 3; saturate_refl; mauto.
      }
      specialize (H1 _ _ H9).
      destruct_all.
      destruct_rel_mod_eval.
      destruct_conjs.
      specialize (H5 s) as [? []].
      specialize (H12 (S s)) as [? []].
      destruct_conjs...
    + destruct_all.
      invert_per_univ_elem H6.
      invert_per_univ_elem H15.
      handle_per_univ_elem_irrel.
      intro s.

      assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a'0 s ∈ in_rel0 }}. {
        eapply H10; mauto 3.
      }

      assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a'0 s ∈ in_rel1 }}. {
        eapply per_elem_subtyping; mauto 3.
      }
      assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a'0 s ∈ in_rel }} by intuition.
      destruct_all.
      destruct_rel_mod_eval.
      specialize (H1 _ _ H14). destruct_all. destruct H1.
      simplify_evals.
      do 2 eexists; repeat split.
      econstructor; mauto 3.
      destruct_conjs.
    (* + admit.
    + admit.
    + admit.
    + admit.
    + admit. *)
         (* match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
  18 : {
    dependent destruction H3. 
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        destruct_all.
        rewrite H10. intros.
        handle_per_univ_elem_irrel. 
        assert {{ Dom c0 ≈≈ c'0 ∈ in_rel }}. {
          eapply per_elem_subtyping with (R:=in_rel0) (A:=a'0); mauto 3;
          saturate_refl; auto.
          rewrite H20. auto.
        }
        destruct_rel_mod_eval. simplify_evals.
        econstructor; mauto 3.
        eapply H29; mauto 3.
        + transitivity a'1. 
          eapply H4; mauto 3.
          eapply per_subtyp_refl; eauto.
        + saturate_refl. auto.
        + assert {{ Dom ⇓ a'0 c0 ≈≈ ⇓ a' c'0 ∈ per_top }}.
          eapply H17; eauto.
          intros s.
          specialize (H8 s).
          specialize (H21 s). destruct_all...
  } *)
  (* - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H); intuition.
    + intro s.
      specialize (H s). destruct_all...
    + intros s.
      specialize (H s).
      specialize (H1 s).
      destruct_all...
    + intros s.
      specialize (H s).
      specialize (H1 s).
      destruct_all...
    + invert_per_univ_elem H2.
      intuition.
    + rewrite H0 in H2.
      dependent destruction H2.
      intro s.
      specialize (H s).
      specialize (H1 s).
      specialize (H2 s).
      destruct_all...
    + invert_per_univ_elem H2.
      rewrite H3 in H4. 
      dependent destruction H4.
      intro s.
      specialize (H s).
      specialize (H1 s).
      specialize (H2 s).
      specialize (H4 s).
      destruct_all... *)
Admitted.


(* the same case seems false (?), it lifts a type to a too high universe *)
Lemma realize_per_univ_elem_gen_ver6 : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ b ∈ per_top_typ }}
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' c c' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ a' c' ∈ R' }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ a' d' ∈ per_top }}).
Proof.
Admitted.


(* Lemma realize_per_univ_elem_gen_ver5 : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    ( {{ Dom a ≈≈ b ∈ per_top_typ }}
         /\ (forall {a'}, {{ Sub a <: a' at i }} ->
                {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
         /\ (forall {a'}, {{ Sub a' <: a at i }} ->
                {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
        )
    /\ (forall {a' c c'}, 
         {{ Sub a' <: a at i }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> 
         {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R }} /\ 
         (forall {R'}, {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} -> {{ Dom ⇑ a' c ≈≈ ⇑ a' c' ∈ R' }}))
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a'}, 
         {{ Sub a <: a' at i }} ->
         (forall {d d'}, {{ Dom d ≈≈ d' ∈ R }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }})
         /\ (forall {d d' R'}, 
          {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
          {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ a' d' ∈ per_top }})
       )
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with try (solve [try (try (do 2 eexists; split); econstructor); mauto]).
    intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + subst...
    + subst. rewrite H1. econstructor.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + invert_per_univ_elem H5. 
      rewrite H6. eexists.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + invert_per_univ_elem H5. 
      rewrite H6. eexists.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + rewrite H1 in H6. destruct H6.
      apply H2 in H6. destruct_all.
      intros s.
      specialize (H6 s). destruct_all.  
      do 2 eexists; repeat split; mauto 3.
    + invert_per_univ_elem H5. rewrite H6 in H5.
      destruct_all. subst.
      destruct_by_head per_univ.
      assert (per_univ_elem j' R' d d') by mauto 3.
      specialize (H2 _ _ _ H0).
      destruct_conjs.
      intro s.
      specialize (H2 s). destruct_all.
      exists C, C'. repeat split; mauto. *)

(* Lemma realize_per_univ_elem_gen_ver4 : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    ( {{ Dom a ≈≈ b ∈ per_top_typ }}
         /\ (forall {a'}, {{ Sub a <: a' at i }} ->
                {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
         /\ (forall {a'}, {{ Sub a' <: a at i }} ->
                {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
        )
    /\ (forall {a' c c' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R }})
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' d d'}, 
         {{ Sub a <: a' at i }} ->
         {{ Dom d ≈≈ d' ∈ R }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with try (solve [try (try (do 2 eexists; split); econstructor); mauto]).
    intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + subst...
    + subst. rewrite H1. econstructor.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + invert_per_univ_elem H5. 
      rewrite H6. eexists.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + rewrite H1 in H5. destruct H5.
      apply H2 in H5. destruct_all.
      intros s.
      specialize (H5 s). destruct_all.  
      do 2 eexists; repeat split; mauto 3.
    + invert_per_univ_elem H5. rewrite H6 in H5.
      destruct_all. subst.
      destruct_by_head per_univ.
      assert (per_univ_elem j' R' d d') by mauto 3.
      specialize (H2 _ _ _ H0).
      destruct_conjs.
      intro s.
      specialize (H2 s). destruct_all.
      exists C, C'. repeat split; mauto.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + rewrite H...
    + invert_per_univ_elem H1; intuition.
    + apply per_nat_then_per_top; intuition. 
    + invert_per_univ_elem H1; intuition.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H).
    + destruct_all.
      intro s.
      assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
        eapply H4; mauto 3; saturate_refl; mauto.
      }
      specialize (H1 _ _ H10).
      destruct_all.
      destruct_rel_mod_eval.
      destruct_conjs.
      specialize (H5 s) as [? []].
      specialize (H13 (S s)) as [? []].
      destruct_conjs...
    + destruct_all.
      admit.
      (* invert_per_univ_elem H6.
      invert_per_univ_elem H16.
      handle_per_univ_elem_irrel.
      intro s.
      assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a' s ∈ in_rel }}. {
        eapply H9; mauto 3; saturate_refl; mauto.
      }
      assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a'0 s ∈ in_rel }} by (saturate_refl; auto).
      clear H15.
      specialize (H1 _ _ H16).
        destruct_all.
      destruct_rel_mod_eval.
      destruct_conjs. *)
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
         (* match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
  18 : {
    dependent destruction H3. 
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        destruct_all.
        rewrite H10. intros.
        handle_per_univ_elem_irrel. 
        assert {{ Dom c0 ≈≈ c'0 ∈ in_rel }}. {
          eapply per_elem_subtyping with (R:=in_rel0) (A:=a'0); mauto 3;
          saturate_refl; auto.
          rewrite H20. auto.
        }
        destruct_rel_mod_eval. simplify_evals.
        econstructor; mauto 3.
        eapply H29; mauto 3.
        + transitivity a'1. 
          eapply H4; mauto 3.
          eapply per_subtyp_refl; eauto.
        + saturate_refl. auto.
        + assert {{ Dom ⇓ a'0 c0 ≈≈ ⇓ a' c'0 ∈ per_top }}.
          eapply H17; eauto.
          intros s.
          specialize (H8 s).
          specialize (H21 s). destruct_all...
  } *)
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H); intuition.
    + intro s.
      specialize (H s). destruct_all...
    + intros s.
      specialize (H s).
      specialize (H1 s).
      destruct_all...
    + intros s.
      specialize (H s).
      specialize (H1 s).
      destruct_all...
    + invert_per_univ_elem H2.
      intuition.
    + rewrite H0 in H2.
      dependent destruction H2.
      intro s.
      specialize (H s).
      specialize (H1 s).
      specialize (H2 s).
      destruct_all...
    + invert_per_univ_elem H2.
      rewrite H3 in H4. 
      dependent destruction H4.
      intro s.
      specialize (H s).
      specialize (H1 s).
      specialize (H2 s).
      specialize (H4 s).
      destruct_all...
Admitted. *)

(* Lemma realize_per_univ_elem_gen_ver3 : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    ( {{ Dom a ≈≈ b ∈ per_top_typ }}
      /\ (forall {a'}, {{ Sub a <: a' at i }} ->
            {{ Dom a' ≈≈ a' ∈ per_top_typ }} )
    )
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with try (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind.
  - repeat split; intros;
    apply_relation_equivalence; mauto.
    + subst... 
    + dependent destruction H3...
    + subst.
      dependent destruction H3. subst. subst.
      invert_per_univ_elem H4. rewrite H4.
      eexists.
      basic_per_univ_elem_econstructor; eauto. reflexivity.
    + subst. dependent destruction H3.
      invert_per_univ_elem H4. rewrite H4 in H5.
      destruct_all.
      destruct_by_head per_univ.
      assert (per_univ_elem j' R' d d') by mauto 3.
      specialize (H2 _ _ _ H3).
      destruct_conjs.
      intro s.
      specialize (H2 s). destruct_all.
      exists C, C'. repeat split; mauto.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + progressive_inversion. intros.
      rewrite H0. econstructor; auto.
    + invert_per_univ_elem H1. 
      eapply per_nat_then_per_top; mauto.
      rewrite <- H0. auto. 
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + destruct_all.
      intro s.
      assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
        eapply H4; mauto 3; saturate_refl; mauto.
      }
      specialize (H1 _ _ H7). destruct_rel_mod_eval.
      destruct_conjs. 
      specialize (H5 s) as [? []].
      specialize (H10 (S s)) as [? []].
      destruct_conjs...
    + destruct_all.
     invert_per_univ_elem H6.
      invert_per_univ_elem H13.
      intros s. 
      assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a'0 s ∈ in_rel0 }}. {
        eapply var_per_bot.
        eapply H9; mauto 3. admit.
      }
    admit.
    + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_all.
      rewrite H11. intros. 
      assert {{ Dom c0 ≈≈ c'0 ∈ in_rel }}. {
        eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
        saturate_refl. auto.
      }
      assert {{ Dom c0 ≈≈ c'0 ∈ in_rel1 }}. {
        eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
      }
      destruct_rel_mod_eval. simplify_evals.
      econstructor; mauto 3.
      eapply H33; mauto 3.
      * transitivity a'1. 
        eapply H5; mauto 3.
        eapply per_subtyp_refl; eauto.
      * saturate_refl. auto.
      * assert {{ Dom ⇓ a'0 c0 ≈≈ ⇓ a' c'0 ∈ per_top }}.
        eapply H16; eauto.
        intros s.
        specialize (H9 s).
        specialize (H23 s). destruct_all...
    + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_conjs.
      intros s.
      assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
        eapply H15; mauto 3; saturate_refl; mauto.
      }
      assert {{ Dom ⇑! a0 s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
        eapply H15; mauto 3; saturate_refl; mauto.
      }
      assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
        eapply per_elem_subtyping with (R:=in_rel) (A:=a); mauto 3.
        saturate_refl. mauto.
      }
      handle_per_univ_elem_irrel.
      assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
        eapply H21; auto.
      }
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      assert (exists WA WA', {{ Rtyp a0 in s ↘ WA }} /\ {{ Rtyp a' in s ↘ WA' }}) by admit.
      destruct_all.
      assert (per_top d{{{ ⇓ a2 fa0 }}} d{{{ ⇓ a'5 f'a' }}}). {
        eapply H39; mauto 3.
        transitivity a'0. eapply per_subtyp_refl; symmetry; mauto 3.
        transitivity a'2; auto.
        eapply H5 with (c:= d{{{ ⇑! a' s }}} ); mauto 3.
        etransitivity; [symmetry|]; mauto 3.
        eapply per_subtyp_refl; mauto 3.
        etransitivity; [|symmetry]; mauto 3.
      }
      specialize (H29 (S s)). destruct_all.
      do 2 eexists; repeat split; econstructor; mauto 3.
  - repeat split; intros; 
      match_by_head per_subtyp ltac:(fun H => directed dependent destruction H)...
    + intro s.
      specialize (H s). destruct_all...
    + intro s.
      specialize (H1 s). destruct_all...
    + progressive_inversion.
      rewrite H10. econstructor; auto.
    + intros s. progressive_inversion.
      subst.
      rewrite H10 in H3. dependent destruction H3.
      (on_all_hyp: fun H => specialize (H s)). 
      destruct_all... 
Admitted. *)

(* This version reverse the subtyping order of a and *)
(* Lemma realize_per_univ_elem_gen_ver1 : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ b ∈ per_top_typ }}
    /\ (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' d d'}, 
          {{ Sub a' <: a at i }} ->
          {{ Dom d ≈≈ d' ∈ R }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - (* subtyp_lowering ? *)
    subst.
    dependent destruction H3. subst. subst.
    invert_per_univ_elem H4. rewrite H4.
    eexists.
    basic_per_univ_elem_econstructor; eauto. reflexivity.
  - subst. 
    progressive_inversion. subst.
    destruct_by_head per_univ.
    specialize (H2 _ _ _ H0).
    destruct_conjs.
    intro s.
    specialize (H2 s). destruct_all.
    exists C, C'. repeat split; mauto.
  - mauto...
  - progressive_inversion. intros.
    rewrite H. econstructor; auto.
  - dependent destruction H0.
    eapply per_nat_then_per_top; auto.
  - destruct_all.
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H3; mauto 3; saturate_refl; mauto.
    }
    specialize (H1 _ _ H5). destruct_rel_mod_eval.
    destruct_conjs.
    specialize (H4 s) as [? []].
    specialize (H8 (S s)) as [? []].
    destruct_conjs...
  - dependent destruction H3. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_all.
    rewrite H10. intros. 
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel }}. {
      eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
      saturate_refl. auto.
    }
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
    }
    destruct_rel_mod_eval. simplify_evals.
    econstructor; mauto 3.
    eapply H31; mauto 3.
    + admit.
    + saturate_refl; mauto.
    + assert {{ Dom ⇓ a'0 c0 ≈≈ ⇓ a' c'0 ∈ per_top }}.
      eapply H15; auto.
      admit.
  - dependent destruction H3. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_conjs.
    intros s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H12; mauto 3; saturate_refl; mauto.
    }
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
      eapply H12; mauto 3; saturate_refl; mauto.
    }
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel) (A:=a); mauto 3.
      saturate_refl. mauto.
    }
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    simplify_evals.
    do 2 eexists; repeat split; econstructor; mauto 3.
  - intro s. 
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all...
  - progressive_inversion.
    rewrite H10. econstructor; auto.
  - intros s. progressive_inversion.
    subst.
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all...
Admitted. *)

(* how to strengthen the lemma? 
  (1) by polarity?;
  (2) both subtyping direction? 
  (3) exist R' {{ Dom ⇑ a' c ≈≈ ⇑ b' c' ∈ R' }}), which can be decided by a'/b', not just a,b *)
Lemma realize_per_univ_elem_gen : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ b ∈ per_top_typ }}
    /\ (forall {a' b' c c'}, 
         {{ Sub a' <: a at i }} -> {{ Sub b' <: b at i }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b' c' ∈ R }})
    /\ (forall {a' b' d d'}, 
          {{ Sub a <: a' at i }} -> {{ Sub b <: b' at i }} ->
          {{ Dom d ≈≈ d' ∈ R }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b' d' ∈ per_top }}).
Proof with (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - (* subtyp_lowering ? *)
    subst.
    progressive_inversion. subst.
    eexists.
    basic_per_univ_elem_econstructor; eauto. reflexivity.
  - subst. 
    progressive_inversion. subst.
    destruct_by_head per_univ.
    specialize (H2 _ _ _ H0).
    destruct_conjs.
    intro s.
    specialize (H2 s). destruct_all.
    exists C, C'. repeat split; mauto.
  (* Nat *)
  - mauto...
  - progressive_inversion. intros.
    admit.
  (* Pi *)
  - destruct_all.
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H3; mauto 3; saturate_refl;
      eapply per_subtyp_refl; eauto.
    }
    specialize (H1 _ _ H5). destruct_rel_mod_eval.
    destruct_conjs.
    specialize (H4 s) as [? []].
    specialize (H8 (S s)) as [? []].
    destruct_conjs...
  - (* progress_inversion or destruct_by_head per_subtyp gives weird results *)
    dependent destruction H3.
    dependent destruction H7.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros. 
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel0 }}. {
      eapply per_elem_subtyping with (R:=in_rel) (B:=a); mauto 3.
      admit.

    }
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel) (B:=a0); mauto 3.
      admit.

    }
    (* after switch the direction, this case is problemtic 
       as we cannot lower relate c0 c'0 in lower universe
    *)
    admit.
  - dependent destruction H3.
    dependent destruction H7.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_all.
    intros s.
    assert {{ Dom ⇑! a'0 s ≈≈ ⇑! a'1 s ∈ in_rel }}. {
      eapply H20; mauto 3; saturate_refl.
    }
    admit.
  - intro s. 
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all...
  - intros s. progressive_inversion. subst.
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all...
  (* - destruct IHHunivelem as [? []].
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H9 (S s)) as [? []].
    specialize (H2 s) as [? []]...
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough ({{ Dom c ⇓ a c0 ≈≈ c' ⇓ a' c0' ∈ per_bot }}) by eauto.
    intro s.
    specialize (H3 s) as [? []].
    specialize (H5 _ _ equiv_c0_c0' s) as [? []]...
  - destruct_conjs.
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    match goal with
    | _: {{ $| ^?f0 & ⇑! a s |↘ ^_ }},
        _: {{ $| ^?f0' & ⇑! a' s |↘ ^_ }},
          _: {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↘ ^?b0 }},
            _: {{ ⟦ B' ⟧ ρ' ↦ ⇑! a' s ↘ ^?b0' }} |- _ =>
        rename f0 into f;
        rename f0' into f';
        rename b0 into b;
        rename b0' into b'
    end.
    assert {{ Dom ⇓ b fa ≈≈ ⇓ b' f'a' ∈ per_top }} by eauto.
    specialize (H2 s) as [? []].
    specialize (H16 (S s)) as [? []]...
  - intro s.
    (on_all_hyp: fun H => destruct (H s) as [? []])...
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s) as [? []])... *)
Admitted.

Corollary per_univ_then_per_top_typ : forall {i a a' R},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ a' ∈ per_top_typ }}.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_univ_then_per_top_typ : mctt.

Corollary per_bot_then_per_elem : forall {i a a' R c c'},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Corollary per_elem_then_per_top : forall {i a a' R b b'},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom b ≈≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mctt.

Lemma per_ctx_then_per_env_initial_env : forall {Γ Γ' env_rel},
    {{ EF Γ ≈≈ Γ' ∈ per_ctx_env ↘ env_rel }} ->
    exists ρ ρ', initial_env Γ ρ /\ initial_env Γ' ρ' /\ {{ Dom ρ ≈≈ ρ' ∈ env_rel }}.
Proof.
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    eexists.
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
Qed.

Lemma var_per_elem : forall {a b i R} n,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom ⇑! a n ≈≈ ⇑! b n ∈ R }}.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.

(** cannot induction on subtyping. probably need a weaker notion of PER
   that subsumers subtyping. *)
Lemma realize_per_sub_elem_gen : forall {i a a' R},
    {{ Sub a <: a' at i }} ->
    {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    (forall {c c'}, {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈≈ ⇓ a' b' ∈ per_top }}).
Proof.
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem; repeat split; intros;
    apply_relation_equivalence; mauto.
Abort.