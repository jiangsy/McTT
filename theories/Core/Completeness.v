From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt Corollaries.
Import Domain_Notations.

Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof with mautosolve.
  intros * [env_relΓ]%completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? []]; shelve_unifiable...
Qed.

Lemma completeness_ty : forall {Γ i A A'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ A' W.
Proof.
  intros * [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]]%completeness.
  mauto 3.
Qed.

Reserved Notation "⊢anf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ => False
  | _ => True
  end.

Inductive alg_subtyping_nf : nf -> nf -> Prop :=
| asnf_refl : forall M N,
    not_univ_pi M ->
    M = N ->
    {{ ⊢anf M ⊆ N }}
| asnf_univ : forall i j,
    i <= j ->
    {{ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall A B A' B',
    {{ ⊢anf A' ⊆ A }} ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Π A B ⊆ Π A' B' }}
where "⊢anf M ⊆ N" := (alg_subtyping_nf M N) (in custom judg) : type_scope.

From Mctt.Core.Syntactic Require Export CtxSub.

Lemma read_typ_per_subtyp_nf_subtyp : forall {A A' W W' i n},
  {{ Sub A <: A' at i }} ->
  {{ Rtyp A in n ↘ W }} ->
  {{ Rtyp A' in n ↘ W' }} ->
  {{ ⊢anf W ⊆ W' }}.
Proof.
  intros * Hsub Htyp Htyp'.
  gen n W W'. induction Hsub; intros;   
    dir_inversion_by_head read_typ; subst.
  - admit.
  - admit.
  - eapply asnf_univ; eauto.
  - eapply asnf_pi; eauto.
    eapply H1; mauto 3.
    eapply per_bot_then_per_elem; mauto 3.
    (**·this is problematic because a and a' may not be related. 
    to apply IH, our per_subtyp needs adjustments.
    Dom c ≈ c' ∈ in_rel needs to be relaxed to sub_values *)
    admit.
Abort.

Lemma completeness_subtyp : forall {Γ A A'},
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
  - admit. (* initial_env Γ p *) (* We need a relation between initial environments of super/sub-context pair *)
  - erewrite <- per_ctx_subtyp_respects_length; mautosolve.
  - admit. (* {{ ⊢anf ~ ?W ⊆ ~ ?W' }} *) (* We need "realizability" of subtyping *)
Abort.
