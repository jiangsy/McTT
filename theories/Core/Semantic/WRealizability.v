From Coq Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.WCong Require Import Definitions.
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

Lemma realize_per_univ_elem_gen : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ b ∈ per_top_typ }}
    /\ (forall {a' b' c c'}, 
         {{ Sub a <: a' at i }} -> {{ Sub b <: b' at i }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b' c' ∈ R }})
    /\ (forall {a' b' d d'}, 
          {{ Sub a' <: a at i }} -> {{ Sub b' <: b at i }} ->
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
    (* after switch the direction, this case is problemtic 
       as we cannot lower relate c0 c'0 in lower universe
    *)
    admit.
  - dependent destruction H3.
    dependent destruction H7.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_all.
    intros s.
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a1 s ∈ in_rel }}. {
      eapply H20; mauto 3; saturate_refl.
    }
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a1 s ∈ in_rel0 }}. {
      eapply per_elem_subtyping with (R:=in_rel); eauto.
      saturate_refl. auto.
      admit.
    }
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a1 s ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel); eauto.
      saturate_refl. auto.
      admit.
    }
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a1 s ∈ in_rel2 }}. {
      eapply per_elem_subtyping with (R:=in_rel); eauto.
      saturate_refl. auto.
      admit.
    }
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    simplify_evals.
    do 2 eexists. repeat split.
    eapply H40 with (a':=a4) in H43; mauto.

    admit. admit. admit.
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