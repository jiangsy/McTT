From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Import WeakCong.
From Mctt.Core.Syntactic Require Export SystemOpt Corollaries CtxSub.
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

Generalizable All Variables.

Lemma weak_cong_to_cong : forall {Γ M M' A A' B},
    {{ ⊢ M ≈≈ M' }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M' : A' }} ->
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢ A' ⊆ B }} ->
    {{ Γ ⊢ M ≈ M' : B }}.
Proof.
  intros * H. gen Γ A A' B. induction H; intros; mauto 4.
  - apply wf_succ_inversion in H0.
    apply wf_succ_inversion in H1. destruct_all.
    gen_presups.
    econstructor; [eapply wf_exp_eq_succ_cong | |]; mauto 3.
    eapply IHexp_weak_cong; mauto 3.
  - apply wf_natrec_inversion in H3.
    apply wf_natrec_inversion in H4.
    admit.
  - apply wf_pi_inversion in H1.
    apply wf_pi_inversion in H2. destruct_all.
    admit.
    (* gen_presups.
    eapply IHexp_weak_cong1 with (B:={{{ Type@(max i i0) }}}) in H1; mauto 3.
    eapply IHexp_weak_cong2 with (B:={{{ Type@(max i i0) }}}) in H7; mauto 3.
    eapply wf_exp_eq_conv.
    econstructor; [ eapply wf_exp_eq_pi_cong | | ]; mauto 3 *)
  - admit.
Admitted.

(* Lemma completeness_subcontext : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    forall Γ',
      {{ ⊢ Γ' ⊆ Γ }} ->
      exists W W', nbe_ty Γ' M W /\ nbe_ty Γ M W' /\ {{ ⊢ W ≈≈ W' }}.
Proof.
  intros. induction H; mauto 4.
  - admit.
  - admit.
  - admit.
  - apply IHwf_exp in H0. destruct_all.
    exists (n{{{ succ W }}}), (n{{{ succ W' }}}). split; mauto 4.
    admit. admit.
  (* does not work *)
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
Proof. *)

Lemma read_typ_per_subtyp_nf_subtyp : forall {A A' W W' i n},
  {{ Sub A <: A' at i }} ->
  {{ Rtyp A in n ↘ W }} ->
  {{ Rtyp A' in n ↘ W' }} ->
  {{ ⊢anf W ⊆ W' }}.
Proof.
  intros * Hsub Htyp Htyp'.
  gen n W W'. induction Hsub; intros;   
    dir_inversion_by_head read_typ; subst.
  - (* TODO: does this hold? *) 
    admit.
  - eapply asnf_refl; mauto 3.  
    constructor.
  - eapply asnf_univ; eauto.
  - eapply asnf_pi; eauto.
    eapply H1; mauto 3.
    (* a' <: a -> a' ~== a *)
    (* We need "realizability" of subtyping, instead of the following realization of equivalence *)
    eapply per_bot_then_per_elem; mauto 3.
    admit.
Abort.

Lemma completeness_subtyp : forall {Γ A A'},
    {{ Γ ⊢ A ⊆ A' }} ->
      exists W W', nbe_ty Γ A W /\ nbe_ty Γ A' W' /\ {{ ⊢anf W ⊆ W' }}.
Proof.
  intros * HA.
  eapply completeness_fundamental_subtyp in HA as [env_relΓ].
  destruct_conjs.
  assert (exists ρ ρ', initial_env Γ ρ /\  initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by (eauto using per_ctx_then_per_env_initial_env).
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
  - admit. (* {{ ⊢anf ~ ?W ⊆ ~ ?W' }} *)
Abort.

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
