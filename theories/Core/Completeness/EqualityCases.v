From Coq Require Import Morphisms_Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import ContextCases LogicalRelation SubstitutionCases SubtypingCases TermStructureCases UniverseCases VariableCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations.


Lemma rel_exp_eq_cong : forall {Γ i A A' M1 M1' M2 M2'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ ⊨ Eq A M1 M2 ≈ Eq A' M1' M2' : Type@i }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1 HM1 HM2.
  destruct_conjs.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  intros.
  destruct_rel_by_assumption env_relΓ H2. 
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  deex. handle_per_univ_elem_irrel.
  econstructor; mauto 3.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
Qed.
#[export]
Hint Resolve rel_exp_eq_cong : mctt.

Lemma valid_exp_eq : forall {Γ i A M1 M2},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ Eq A M1 M2 : Type@i }}.
Proof. mauto. Qed.

#[export]
Hint Resolve valid_exp_eq : mctt.

Lemma rel_exp_refl_cong : forall {Γ i A A' M M'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ refl A M ≈ refl A' M' : Eq A M M }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1 HM.
  destruct_conjs.
  invert_rel_exp HM.
  eexists_rel_exp.
  intros.
  saturate_refl_for env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_rel_typ.
  destruct_by_head rel_exp.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; split; econstructor; mauto 4.
  - per_univ_elem_econstructor; mauto 3;
      try (etransitivity; [| symmetry]; eassumption);
      try reflexivity.
  - econstructor; saturate_refl; mauto 3.
    symmetry; mauto 3.
Qed.
#[export]
Hint Resolve rel_exp_refl_cong : mctt.

Lemma rel_exp_eq_sub : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Γ ⊨ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] HA HM1 HM2.
  destruct_conjs.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_eq_sub : mctt.

Lemma rel_exp_refl_sub : forall {Γ σ Δ i A M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M : A }} ->
    {{ Γ ⊨ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] HA HM.
  destruct_conjs.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; split; econstructor; mauto 3.
  - per_univ_elem_econstructor; mauto 3; try solve_refl.
  - saturate_refl.
    econstructor; intuition.
Qed.

#[export]
Hint Resolve rel_exp_refl_sub : mctt.

Lemma rel_exp_eqrec_wf_Awk : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ A[Wk] : Type@i }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1. destruct_conjs.
  assert {{ ⊨ Γ, A }} by mauto.
  assert {{ Γ, A ⊨s Wk : Γ }} by mauto 3.
  assert {{ Γ, A ⊨ A[Wk] : Type@i[Wk] }} by mauto.
  mauto 4.
Qed.

Lemma rel_exp_eqrec_wf_EqAwkwk : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊨ Eq A[Wk∘Wk] #1 #0 : Type@i }}.
Proof.
  intros * HA.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_of_typ_inversion1 in HA as [env_relΓ].
  destruct_conjs.
  assert {{ ⊨ Γ, A }} by mauto.
  assert {{ Γ, A ⊨s Wk : Γ }} by mauto 3.
  assert {{ ⊨ Γ, A, A[Wk] }} by mauto.
  assert {{ Γ, A, A[Wk] ⊨s Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊨ #0 : A[Wk][Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #0 : A[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #1 : A[Wk][Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #1 : A[Wk∘Wk] }} by mauto 3.
  mauto 4.
Qed.

Lemma rel_exp_eqrec_per_ctx_env_gen : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    exists env_relΓ, (
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} /\ 
        exists elem_relA, (
          (forall (ρ ρ' : env) (equiv_ρ_ρ' : env_relΓ ρ ρ'), rel_typ i A ρ A ρ' (elem_relA ρ ρ' equiv_ρ_ρ')) /\
            {{EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ cons_per_ctx_env env_relΓ elem_relA}} /\
              exists elem_relAwk, (
                forall (ρ ρ' : env) (equiv_ρ_ρ' : (cons_per_ctx_env env_relΓ elem_relA) ρ ρ'), rel_typ i {{{ A[Wk] }}} ρ {{{ A[Wk] }}} ρ' (elem_relAwk ρ ρ' equiv_ρ_ρ')
              )
        )
    ).
Proof.
  intros * HA.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA. destruct_conjs.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  eexists; split; mauto.
  eexists; split; mauto.
  split.
  econstructor; mauto 3; try reflexivity; typeclasses eauto.
  invert_rel_exp_of_typ HA'. destruct_conjs.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  assert (x0 <~> cons_per_ctx_env x elem_relA) by admit.
  (* setoid_rewrite H3 in elem_relA'.
  exists elem_relA'. intros.
  invert_per_ctx_envs. 
  handle_per_ctx_env_irrel.
  destruct_by_head cons_per_ctx_env.
  (on_all_hyp: destruct_rel_by_assumption x).
  apply_relation_equivalence.
  assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}}). {
    setoid_rewrite <- H3. auto.
  }
  (on_all_hyp: destruct_rel_by_assumption tail_rel).
  handle_per_ctx_env_irrel. mauto.
  handle_per_univ_elem_irrel.
  econstructor; mauto. mauto. exact H5.
  eapply mk_cons_per_ctx_env with (equiv_ρ_drop_ρ'_drop:=equiv_ρ_drop_ρ'_drop). 
  setoid_rewrite <- H8.
  apply_relation_equivalence.
  mauto. handle_per_ctx_env_irrel. mauto. eapply H2. simpl in *.
 mauto. eapply H2. *)
  (* exists (cons_per_ctx_env x elem_relA). 
  intros.
  handle_per_ctx_env_irrel. eapply H2. Unshelve. mauto 3. *)
Abort.

Lemma rel_exp_eqrec_sub : forall {Γ σ Δ i A M1 M2 j B BR N},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Δ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ ⊨ N : Eq A M1 M2 }} ->
    {{ Γ ⊨ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ]
         ≈ eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end
        : B[σ,,M1[σ],,M2[σ],,N[σ]] }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] HA HM1 HM2 HB HBR HN.
  destruct_conjs.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  destruct_conjs.
  pose (env_relΔA := cons_per_ctx_env env_relΔ elem_relA).
  assert {{ EF Δ, A ≈ Δ, A ∈ per_ctx_env ↘ env_relΔA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  pose (env_relΔAA := cons_per_ctx_env env_relΔA elem_relA').
  assert {{ EF Δ, A, A[Wk] ≈ Δ, A, A[Wk] ∈ per_ctx_env ↘ env_relΔAA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HEq.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relEq]; shelve_unifiable; [eassumption |]).
  pose (env_relΔAAEq := cons_per_ctx_env env_relΔAA elem_relEq).
  assert {{ EF Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΔAAEq }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp HN.
  invert_rel_exp HB.
  invert_rel_exp HBR.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  match_by_head per_eq ltac:(fun H => destruct H).
  - rename ρ1 into ρσ. rename ρ0 into ρ'σ.
    rename m0 into m1'. rename m3 into m2'.
    assert {{ Dom ρσ ↦ n ≈ ρ'σ ↦ n' ∈ env_relΔA }} by (unfold env_relΔA; mauto 3).
    assert {{ Dom ρσ ↦ m1 ≈ ρ'σ ↦ m1' ∈ env_relΔA }} by (unfold env_relΔA; mauto 3).
    (on_all_hyp: destruct_rel_by_assumption env_relΔA).
    simplify_evals.
    handle_per_univ_elem_irrel.
    assert {{ Dom ρσ ↦ n ↦ n ≈ ρ'σ ↦ n' ↦ n' ∈ env_relΔAA }} by (unfold env_relΔAA; unshelve eexists; intuition).
    assert {{ Dom ρσ ↦ m1 ↦ m2 ≈ ρ'σ ↦ m1' ↦ m2' ∈ env_relΔAA }} by (unfold env_relΔAA; unshelve eexists; intuition).
    (on_all_hyp: destruct_rel_by_assumption env_relΔAA).
    simplify_evals.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    (* assert {{ Dom ρσ ↦ n ↦ n ↦ refl n ≈ ρ'σ ↦ n' ↦ n' ↦ refl n' ∈ env_relΔAAEq }} as HrelΔAAEq by (unshelve eexists; simpl; intuition). *)
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ refl n ≈ ρ'σ ↦ m1' ↦ m2' ↦ refl n' ∈ env_relΔAAEq }} as HrelΔAAEq' by admit.
    apply_relation_equivalence.
    (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
    destruct_conjs.
    destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    simplify_evals.
    rename m10 into br.
    rename m'0 into br'.
    handle_per_ctx_env_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    deex. eexists; split. 
    + eapply mk_rel_mod_eval with (a:=m11) (a':=m').
      econstructor; mauto.
      econstructor; mauto.
      econstructor; mauto.
      econstructor; mauto.
      mauto.
    + econstructor. mauto.
      econstructor; mauto.
      simpl in *.
      assert (per_univ_elem j R' m6 m8) by admit.
      handle_per_univ_elem_irrel. mauto.
  - admit.
Admitted.

#[export]
Hint Resolve rel_exp_eqrec_sub : mctt.

Lemma rel_exp_eqrec_cong : forall {Γ i A A' M1 M1' M2 M2' j B B' BR BR' N N'},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B ≈ B' : Type@j }} ->
    {{ Γ, A ⊨ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ N ≈ N' : Eq A M1 M2 }} ->
    {{ Γ ⊨ eqrec N as Eq A M1 M2 return B | refl -> BR end
         ≈ eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end
        : B[Id,,M1,,M2,,N] }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1
    HM1 HM2 HAA' HM1M1' HM2M2' HBB' HBRBR' HNN'.
  (* a similar rel_exp_of_sub_id_zero_inversion to HBR? *)
  destruct_conjs.
  invert_rel_exp_of_typ HAA'.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  invert_rel_exp HNN'.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  deex.
  destruct_by_head per_eq.
  match_by_head per_eq ltac:(fun H => destruct H).
  handle_per_univ_elem_irrel.
  (* shall we encapsulate the case analysis as eval_natrec_rel, since no induction is 
    needed here? *)
  - eexists; split. 2: {
    econstructor; mauto 3.
    econstructor; mauto.
    econstructor; mauto. admit.
    admit. }
    admit.
  - eexists; split. 2: {
    econstructor. econstructor. 5:eapply eval_eqrec_neut; mauto 3.
    all : mauto 3.
    handle_per_univ_elem_irrel. all : admit. }
    admit.
Admitted.

#[export]
Hint Resolve rel_exp_eqrec_cong : mctt.

Lemma rel_exp_eqrec_beta : forall {Γ i A M j B BR},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Γ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ eqrec refl A M as Eq A M M return B | refl -> BR end
         ≈ BR[Id,,M]
        : B[Id,,M,,M,,refl A M] }}.
Proof.
  (* Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j is not necessary *)
  intros * HA HM _ HBR.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA.
  rename x into env_relΓ.
  destruct_conjs.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM.
  pose (env_relΓA := cons_per_ctx_env env_relΓ elem_relA).
  assert {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_relΓA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  pose (env_relΓAA := cons_per_ctx_env env_relΓA elem_relA').
  assert {{ EF Γ, A, A[Wk] ≈ Γ, A, A[Wk] ∈ per_ctx_env ↘ env_relΓAA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HEq.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relEq]; shelve_unifiable; [eassumption |]).
  pose (env_relΓAAEq := cons_per_ctx_env env_relΓAA elem_relEq).
  assert {{ EF Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΓAAEq }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp HBR.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  match_by_head per_eq ltac:(fun H => destruct H).
  assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
  (on_all_hyp: destruct_rel_by_assumption env_relΓA).
  simplify_evals.
  handle_per_univ_elem_irrel.
  assert {{ Dom ρ ↦ m ↦ m ≈ ρ' ↦ m' ↦ m' ∈ env_relΓAA }} by (unfold env_relΓAA; unshelve eexists; intuition).
  (on_all_hyp: destruct_rel_by_assumption env_relΓAA).
  simplify_evals.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  destruct_conjs.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  simplify_evals.
  handle_per_univ_elem_irrel.
  assert ({{ ⟦ B[Id,,M,,M,,refl A M] ⟧ ρ ↘ m0 }}) by (econstructor; mauto 5).
  assert ({{ ⟦ B[Id,,M,,M,,refl A M] ⟧ ρ' ↘ m2 }}) by (econstructor; mauto 5).
  eexists; split; mauto 3. econstructor; mauto 3. 
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve rel_exp_eqrec_beta : mctt.
