From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.WCompleteness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import WRealizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic.WCong Require Import Definitions Lemmas.
From Mctt.Core.Syntactic Require Export SystemOpt Corollaries CtxSub.
Import Domain_Notations.


Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W W', nbe Γ M A W /\ nbe Γ M' A W' /\ {{ ⊢nf W ≈≈ W' }}.
Proof with mautosolve.
  intros * [env_relΓ]%completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈≈ ρ' ∈ env_relΓ }}) as [ρ] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? [? [? []]]]; shelve_unifiable; mauto 3.
  exists x, x0; repeat split; mauto 3.
Qed.

Lemma completeness_ty : forall {Γ i A A'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    exists W W', nbe_ty Γ A W /\ nbe_ty Γ A' W' /\ {{ ⊢nf W ≈≈ W' }}  .
Proof.
  intros. apply completeness in H as [W [W' []]]; mauto 3.
  destruct_all.
  apply nbe_type_to_nbe_ty in H.
  apply nbe_type_to_nbe_ty in H0.
  do 2 eexists; repeat split; mauto 3.
Qed.

Reserved Notation "Γ ⊢anf A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom nf, A' custom nf).

Inductive algo_subtyping_nf : ctx -> nf -> nf -> Prop :=
| asnf_refl : forall Γ M N,
    not_univ_pi M ->
    {{ ⊢nf M ≈≈ N }} ->
    {{ Γ ⊢anf M ⊆ N }}
| asnf_univ : forall Γ i j,
    i <= j ->
    {{ Γ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall Γ (A B A' B' B'' : nf),
    {{ Γ ⊢anf A' ⊆ A }} ->
    nbe_ty {{{ Γ , ^(A' : exp) }}} B B'' ->
    {{ Γ , ^(A' : exp) ⊢anf B' ⊆ B' }} ->
    {{ Γ ⊢anf Π A B ⊆ Π A' B' }}
where "Γ ⊢anf M ⊆ N" := (algo_subtyping_nf Γ M N) (in custom judg) : type_scope.


Lemma completeness_subtyp : forall {Γ A A'},
    {{ Γ ⊢ A ⊆ A' }} ->
      exists W W', nbe_ty Γ A W /\ nbe_ty Γ A' W' /\ {{ ⊢snf W ⊆ W' }}.
Proof.
  intros * HA.
  eapply completeness_fundamental_subtyp in HA as [env_relΓ].
  destruct_conjs.
  assert (exists ρ ρ', initial_env Γ ρ /\  initial_env Γ ρ' /\ {{ Dom ρ ≈≈ ρ' ∈ env_relΓ }}) as [ρ] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => epose proof (per_univ_then_per_top_typ H (length Γ)); destruct_all).
  functional_read_rewrite_clear. clear_dups.
  do 2 eexists.
  repeat split; only 1-2: econstructor; try eassumption.
  - eapply wrealize_persub_gen; mauto 3. 
Abort.

(* Lemma completeness_subtyp' : forall {Γ A A'},
    {{ Γ ⊢ A ⊆ A' }} ->
    forall Γ',
      {{ ⊢ Γ' ⊆ Γ }} ->
      exists W W', nbe_ty Γ' A W /\ nbe_ty Γ A' W' /\ {{ ⊢anf W ⊆ W' }}.
Proof.
  intros * HA. induction HA; intros.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted. *)


(* Lemma completeness_subtyp : forall {Γ A A'},
    {{ Γ ⊢ A ⊆ A' }} ->
    forall Γ',
      {{ ⊢ Γ' ⊆ Γ }} ->
      exists W W', nbe_ty Γ' A W /\ nbe_ty Γ A' W' /\ {{ ⊢anf W ⊆ W' }}.
Proof.
  intros * HA ? HG.
  assert {{ Γ' ⊢ A ⊆ A' }} as HA' by mauto 3.
  eapply completeness_fundamental_subtyp in HA as [env_relΓ].
  eapply completeness_fundamental_subtyp in HA' as [env_relΓ'].
  destruct_conjs.
  eapply completeness_fundamental_ctx_subtyp in HG.
  assert (exists ρ ρ', initial_env Γ' ρ /\ initial_env Γ' ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ' }}) as [ρ] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply per_ctx_env_subtyping; mauto 2).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => epose proof (per_univ_then_per_top_typ H (length Γ')); destruct_all).
  functional_read_rewrite_clear. clear_dups.
  do 2 eexists.
  repeat split; only 1-2: econstructor; try eassumption.
  - admit. (* initial_env Γ p, which is false *) (* We need a relation between initial environments of super/sub-context pair *)
  - erewrite <- per_ctx_subtyp_respects_length; mautosolve.
  - admit. (* {{ ⊢anf ~ ?W ⊆ ~ ?W' }} *)
Abort. *)
