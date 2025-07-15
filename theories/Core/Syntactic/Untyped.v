From Coq Require Import Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Reserved Notation "⊖ M ≈- M'" (in custom judg at level 80, M custom exp, M' custom exp).
Reserved Notation "⊖ σ ≈-s σ'" (in custom judg at level 80, σ custom exp, σ' custom exp).
Reserved Notation "⊖ A ⊆- A'" (in custom judg at level 80, A custom exp, A' custom exp).

Generalizable All Variables.

Inductive exp_ueq : exp -> exp -> Prop :=
| exp_ueq_typ_sub :
  `( {{ ⊖ Type@i[σ] ≈- Type@i }} )

| exp_ueq_nat_sub :
  `( {{ ⊖ ℕ[σ] ≈- ℕ }} )
| exp_ueq_zero_sub :
  `( {{ ⊖ zero[σ] ≈- zero }} )
| exp_ueq_succ_sub :
  `( {{ ⊖ (succ M)[σ] ≈- succ (M[σ]) }} )
| exp_ueq_succ_cong :
  `( {{ ⊖ M ≈- M' }} ->
     {{ ⊖ succ M ≈- succ M' }} )
| exp_ueq_natrec_cong :
  `( {{ ⊖ A ≈- A' }} ->
     {{ ⊖ MZ ≈- MZ' }} ->
     {{ ⊖ MS ≈- MS' }} ->
     {{ ⊖ M ≈- M' }} ->
     {{ ⊖ rec M return A | zero -> MZ | succ -> MS end ≈- rec M' return A' | zero -> MZ' | succ -> MS' end }} )
| exp_ueq_natrec_sub :
  `( {{ ⊖ rec M return A | zero -> MZ | succ -> MS end[σ] ≈- rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }} )
| exp_ueq_nat_beta_zero :
  `( {{ ⊖ rec zero return A | zero -> MZ | succ -> MS end ≈- MZ }} )
| exp_ueq_nat_beta_succ :
  `( {{ ⊖ rec succ M return A | zero -> MZ | succ -> MS end ≈- MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] }} )

| exp_ueq_pi_sub :
  `( {{ ⊖ (Π A B)[σ] ≈- Π A[σ] B[q σ] }} )
| exp_ueq_pi_cong :
  `( {{ ⊖ A ≈- A' }} ->
     {{ ⊖ B ≈- B' }} ->
     {{ ⊖ Π A B ≈- Π A' B' }} )
| exp_ueq_fn_cong :
  `( {{ ⊖ A ≈- A' }} ->
     {{ ⊖ M ≈- M' }} ->
     {{ ⊖ λ A M ≈- λ A' M' }} )
| exp_ueq_fn_sub :
  `( {{ ⊖ (λ A M)[σ] ≈- λ A[σ] M[q σ] }} )
| exp_ueq_app_cong :
  `( {{ ⊖ M ≈- M' }} ->
     {{ ⊖ N ≈- N' }} ->
     {{ ⊖ M N ≈- M' N' }} )
| exp_ueq_app_sub :
  `( {{ ⊖ (M N)[σ] ≈- M[σ] N[σ] }} )
| exp_ueq_pi_beta :
  `( {{ ⊖ (λ A M) N ≈- M[Id,,N] }} )

| exp_ueq_eq_sub :
  `( {{ ⊖ (Eq A M N)[σ] ≈- Eq A[σ] M[σ] N[σ] }} )
| exp_ueq_refl_sub :
  `( {{ ⊖ (refl A M)[σ] ≈- refl A[σ] M[σ] }} )
| exp_ueq_eqrec_sub :
  `( {{ ⊖ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ]
          ≈- eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end }} )
| exp_ueq_eq_cong :
  `( {{ ⊖ A ≈- A' }} ->
     {{ ⊖ M ≈- M' }} ->
     {{ ⊖ N ≈- N' }} ->
     {{ ⊖ Eq A M N ≈- Eq A' M' N' }})
| exp_ueq_refl_cong :
  `( {{ ⊖ A ≈- A' }} ->
     {{ ⊖ M ≈- M' }} ->
     {{ ⊖ refl A M ≈- refl A' M' }})
| exp_ueq_eqrec_cong :
  `( {{ ⊖ A ≈- A' }} ->
     {{ ⊖ M1 ≈- M1' }} ->
     {{ ⊖ M2 ≈- M2' }} ->
     {{ ⊖ B ≈- B' }} ->
     {{ ⊖ BR ≈- BR' }} ->
     {{ ⊖ N ≈- N' }} ->
     {{ ⊖ eqrec N as Eq A M1 M2 return B | refl -> BR end
          ≈- eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end }} )
| exp_ueq_eqrec_beta :
  `( {{ ⊖ eqrec refl A M as Eq A M M return B | refl -> BR end
          ≈- BR[Id,,M] }} )

| exp_ueq_var :
  `( {{ ⊖ #x ≈- #x }} )
| exp_ueq_var_0_sub :
  `( {{ ⊖ #0[σ,,M] ≈- M }} )
| exp_ueq_var_S_sub :
  `( {{ ⊖ #(S x)[σ,,M] ≈- #x[σ] }} )
| exp_ueq_var_weaken :
  `( {{ ⊖ #x[Wk] ≈- #(S x) }} )
| exp_ueq_sub_cong :
  `( {{ ⊖ M ≈- M' }} ->
     {{ ⊖ σ ≈-s σ' }} ->
     {{ ⊖ M[σ] ≈- M'[σ'] }} )
| exp_ueq_sub_id :
  `( {{ ⊖ M[Id] ≈- M }} )
| exp_ueq_sub_compose :
  `( {{ ⊖ M[σ∘τ] ≈- M[σ][τ] }} )

| exp_ueq_sym :
  `( {{ ⊖ M ≈- M' }} ->
     {{ ⊖ M' ≈- M }} )
| exp_ueq_trans :
  `( {{ ⊖ M ≈- M' }} ->
     {{ ⊖ M' ≈- M'' }} ->
     {{ ⊖ M ≈- M'' }} )
where "⊖ M ≈- M'" := (exp_ueq M M') (in custom judg) : type_scope

with sub_ueq : sub -> sub -> Prop :=
| sub_ueq_id :
  `( {{ ⊖ Id ≈-s Id }} )
| sub_ueq_weaken :
  `( {{ ⊖ Wk ≈-s Wk }} )
| sub_ueq_compose_cong :
  `( {{ ⊖ τ ≈-s τ' }} ->
     {{ ⊖ σ ≈-s σ' }} ->
     {{ ⊖ σ∘τ ≈-s σ'∘τ' }} )
| sub_ueq_extend_cong :
  `( {{ ⊖ σ ≈-s σ' }} ->
     {{ ⊖ M ≈- M' }} ->
     {{ ⊖ σ,,M ≈-s σ',,M' }} )
| sub_ueq_id_compose_right :
  `( {{ ⊖ Id∘σ ≈-s σ }} )
| sub_ueq_id_compose_left :
  `( {{ ⊖ σ∘Id ≈-s σ }} )
| sub_ueq_compose_assoc :
  `( {{ ⊖ (σ∘σ')∘σ'' ≈-s σ∘(σ'∘σ'') }} )
| sub_ueq_extend_compose :
  `( {{ ⊖ (σ,,M)∘τ ≈-s (σ∘τ),,M[τ] }} )
| sub_ueq_p_extend :
  `( {{ ⊖ Wk∘(σ,,M) ≈-s σ }} )
| sub_ueq_extend :
  `( {{ ⊖ σ ≈-s (Wk∘σ),,#0[σ] }} )
| sub_ueq_sym :
  `( {{ ⊖ σ ≈-s σ' }} ->
     {{ ⊖ σ' ≈-s σ }} )
| sub_ueq_trans :
  `( {{ ⊖ σ ≈-s σ' }} ->
     {{ ⊖ σ' ≈-s σ'' }} ->
     {{ ⊖ σ ≈-s σ'' }} )
where "⊖ S1 ≈-s S2" := (sub_ueq S1 S2) (in custom judg) : type_scope.

Inductive usubtyp : typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** We need this extra argument in order to prove the lemmas
      in CtxSub.v independently. We can prove those and
      presupposition lemmas mutually dependently, but that would
      be more messy.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( {{ ⊖ M ≈- M' }} ->
     {{ ⊖ M ⊆- M' }} )
| wf_subtyp_trans :
  `( {{ ⊖ M ⊆- M' }} ->
     {{ ⊖ M' ⊆- M'' }} ->
     {{ ⊖ M ⊆- M'' }} )
| wf_subtyp_univ :
  `( i < j ->
     {{ ⊖ Type@i ⊆- Type@j }} )
| wf_subtyp_pi :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ, A ⊢ B : Type@i }} ->
     {{ Γ, A' ⊢ B' : Type@i }} ->
     {{ Γ, A' ⊢ B ⊆ B' }} ->
     {{ Γ ⊢ Π A B ⊆ Π A' B' }} )
where "⊖ A ⊆- A'" := (usubtyp A A') (in custom judg) : type_scope.


Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_sub_mut_ind := Induction for wf_ctx_sub Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop
with wf_subtyp_mut_ind := Induction for wf_subtyp Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_ctx_sub_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind,
  wf_subtyp_mut_ind.

Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_sub_mut_ind'.

Inductive wf_ctx_eq : ctx -> ctx -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Δ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ⊢ A ≈ A' : Type@i }} ->
     {{ ⊢ Γ, A ≈ Δ, A' }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_ctx_sub wf_exp wf_sub wf_exp_eq wf_sub_eq wf_subtyp ctx_lookup : mctt.

#[export]
Instance wf_exp_eq_PER Γ A : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_PER Γ Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_ctx_eq_Symmetric : Symmetric wf_ctx_eq.
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_subtyp_Transitive Γ : Transitive (wf_subtyp Γ).
Proof.
  hnf; mauto.
Qed.

(** Immediate & Independent Presuppositions *)

Lemma presup_ctx_sub : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_ctx_sub : mctt.

Lemma presup_ctx_sub_left : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_left : mctt.

Lemma presup_ctx_sub_right : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_right : mctt.

Lemma presup_subtyp_right : forall {Γ A B}, {{ Γ ⊢ A ⊆ B }} -> exists i, {{ Γ ⊢ B : Type@i }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Γ A A' M,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_sub_subtyp' : forall Γ Δ Δ' σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢s σ : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_subtyp' : mctt.
#[export]
Remove Hints wf_sub_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Γ A A' M M',
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_subtyp' : mctt.
#[export]
Remove Hints wf_exp_eq_subtyp : mctt.

Lemma wf_sub_eq_subtyp' : forall Γ Δ Δ' σ σ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_subtyp' : mctt.
#[export]
Remove Hints wf_sub_eq_subtyp : mctt.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature eq ==> wf_exp_eq Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ Δ : (wf_sub_eq Γ Δ)
    with signature wf_sub_eq Γ Δ ==> eq ==> iff as wf_sub_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ Δ : (wf_sub_eq Γ Δ)
    with signature eq ==> wf_sub_eq Γ Δ ==> iff as wf_sub_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

#[export]
Hint Rewrite -> wf_exp_eq_typ_sub wf_exp_eq_nat_sub wf_exp_eq_eq_sub using mauto 3 : mctt.

#[export]
Hint Rewrite -> wf_sub_eq_id_compose_right wf_sub_eq_id_compose_left
                  wf_sub_eq_compose_assoc (* prefer right association *)
                  wf_sub_eq_p_extend using mauto 4 : mctt.

#[export]
Hint Rewrite -> wf_exp_eq_sub_id wf_exp_eq_pi_sub using mauto 4 : mctt.

#[export]
Instance wf_exp_eq_per_elem Γ T : PERElem _ (wf_exp Γ T) (wf_exp_eq Γ T).
Proof.
  intros a Ha. mauto.
Qed.


#[export]
Instance wf_sub_eq_per_elem Γ Δ : PERElem _ (wf_sub Γ Δ) (wf_sub_eq Γ Δ).
Proof.
  intros a Ha. mauto.
Qed.
