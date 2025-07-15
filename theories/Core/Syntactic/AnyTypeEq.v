From Coq Require Import Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Lemma any_type_exp_eq_typ_sub : forall Γ σ i A,
    {{ Γ ⊢ Type@i[σ] : A }} ->
    {{ Γ ⊢ Type@i[σ] ≈ Type@i : A }}.
Proof.
  intros * H.
  apply wf_exp_sub_inversion in H as (Δ & A' & Hσ & H & Hsub).
  apply wf_typ_inversion in H.
  assert {{ Γ ⊢ Type@(S i) ⊆ Type@(S i)[σ] }} by mauto 4.
  assert {{ Γ ⊢ Type@(S i) ⊆ A }} by (transitivity {{{ A'[σ] }}}; mauto 3).
  eapply wf_exp_eq_subtyp'; revgoals; mautosolve 2.
Qed.

Lemma any_type_exp_eq_nat_sub : forall Γ σ A,
    {{ Γ ⊢ ℕ[σ] : A }} ->
    {{ Γ ⊢ ℕ[σ] ≈ ℕ : A }}.
Proof.
  intros * H.
  apply wf_exp_sub_inversion in H as (Δ & A' & Hσ & H & Hsub).
  apply wf_nat_inversion in H.
  assert {{ Γ ⊢ Type@0 ⊆ Type@0[σ] }} by mauto 4.
  assert {{ Γ ⊢ Type@0 ⊆ A }} by (transitivity {{{ A'[σ] }}}; mauto 3).
  eapply wf_exp_eq_subtyp'; revgoals; mautosolve 2.
Qed.

Lemma any_type_exp_eq_zero_sub : forall Γ σ A,
    {{ Γ ⊢ zero[σ] : A }} ->
    {{ Γ ⊢ zero[σ] ≈ zero : A }}.
Proof.
  intros * H.
  apply wf_exp_sub_inversion in H as (Δ & A' & Hσ & H & Hsub).
  apply wf_zero_inversion in H.
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mautosolve 4.
  assert {{ Γ ⊢ ℕ ⊆ A }} by (transitivity {{{ A'[σ] }}}; mauto 3).
  eapply wf_exp_eq_subtyp'; revgoals; mautosolve 2.
Qed.

Lemma any_type_exp_eq_succ_sub : forall Γ σ M A,
    {{ Γ ⊢ (succ M)[σ] : A }} ->
    {{ Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : A }}.
Proof.
  intros * H.
  apply wf_exp_sub_inversion in H as (Δ & A' & Hσ & H & Hsub).
  apply wf_succ_inversion in H as (H & Hsub').
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mautosolve 4.
  assert {{ Γ ⊢ ℕ ⊆ A }} by (transitivity {{{ A'[σ] }}}; mauto 3).
  eapply wf_exp_eq_subtyp'; revgoals; mautosolve 2.
Qed.

Lemma any_type_exp_eq_succ_cong : forall Γ M M' A,
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ succ M ≈ succ M' : A }}.
Proof.
  intros * H **.
  apply wf_succ_inversion in H as (H & Hsub').
  eapply wf_exp_eq_subtyp'; revgoals; mautosolve 2.
Qed.

Lemma any_type_exp_eq_natrec_cong : forall Γ M M' A,
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ succ M ≈ succ M' : A }}.
Proof.
  intros * H **.
  apply wf_succ_inversion in H as (H & Hsub').
  eapply wf_exp_eq_subtyp'; revgoals; mautosolve 2.
Qed.
