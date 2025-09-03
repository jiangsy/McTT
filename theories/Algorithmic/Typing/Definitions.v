From Mctt.Algorithmic Require Export IR.
From Mctt.Algorithmic.Subtyping Require Export Definitions.
From Mctt.Core Require Import Base.
Import Syntax_Notations.
Import IR_Notations.

Reserved Notation "Γ '⊢ai' M ⟹ A" (in custom judg at level 80, Γ custom exp, M custom ir, A custom nf).
Reserved Notation "Γ '⊢ai' M ⟸ A" (in custom judg at level 80, Γ custom exp, M custom ir, A custom exp).

Generalizable All Variables.

Inductive alg_type_check : ctx -> typ -> ir -> Prop :=
| atc_ati :
  `( {{ Γ ⊢ai M ⟹ A }} ->
     {{ Γ ⊢a A ⊆ B }} ->
     {{ Γ ⊢ai M ⟸ B }} )
where "Γ '⊢ai' M ⟸ A" := (alg_type_check Γ A M) (in custom judg) : type_scope
with alg_type_infer : ctx -> nf -> ir -> Prop :=
| ati_typ :
  `( {{ Γ ⊢ai Type@i ⟹ Type@(S i) }} )
| ati_nat :
  `( {{ Γ ⊢ai ℕ ⟹ Type@0 }} )
| ati_zero :
  `( {{ Γ ⊢ai zero ⟹ ℕ }} )
| ati_succ :
  `( {{ Γ ⊢ai M ⟸ ℕ }} ->
     {{ Γ ⊢ai succ M ⟹ ℕ }} )
| ati_natrec :
  `( {{ Γ, ℕ ⊢ai A ⟹ Type@i }} ->
     {{ Γ ⊢ai MZ ⟸ A[Id,,zero] }} ->
     {{ Γ, ℕ, ^(A : typ) ⊢ai MS ⟸ A[Wk∘Wk,,succ #1] }} ->
     {{ Γ ⊢ai M ⟸ ℕ }} ->
     nbe_ty Γ {{{ A[Id,,M] }}} B ->
     {{ Γ ⊢ai rec M return A | zero -> MZ | succ -> MS end ⟹ B }} )
| ati_pi :
  `( {{ Γ ⊢ai A ⟹ Type@i }} ->
     {{ Γ, ^(A : typ) ⊢ai B ⟹ Type@j }} ->
     {{ Γ ⊢ai Π A B ⟹ Type@(max i j) }} )
| ati_fn :
  `( {{ Γ ⊢ai A ⟹ Type@i }} ->
     {{ Γ, ^(A : typ) ⊢ai M ⟹ B }} ->
     nbe_ty Γ A C ->
     {{ Γ ⊢ai λ A M ⟹ Π C B }} )
| ati_app :
  `( {{ Γ ⊢ai M ⟹ Π A B }} ->
     {{ Γ ⊢ai N ⟸ A }} ->
     nbe_ty Γ {{{ B[Id,,N] }}} C ->
     {{ Γ ⊢ai M N ⟹ C }} )
| ati_eq :
  `( {{ Γ ⊢ai A ⟹ Type@i }} ->
     {{ Γ ⊢ai M1 ⟸ A }} ->
     {{ Γ ⊢ai M2 ⟸ A }} ->
     {{ Γ ⊢ai Eq A M1 M2 ⟹ Type@i }} )
| ati_refl :
  `( {{ Γ ⊢ai A ⟹ Type@i }} ->
     {{ Γ ⊢ai M ⟸ A }} ->
     nbe_ty Γ A C ->
     nbe Γ M A N ->
     {{ Γ ⊢ai refl A M ⟹ Eq C N N }} )
| ati_eqrec :
  `( {{ Γ ⊢ai A ⟹ Type@i }} ->
     {{ Γ ⊢ai M1 ⟸ A }} ->
     {{ Γ ⊢ai M2 ⟸ A }} ->
     {{ Γ, ^(A : typ), A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ai B ⟹ Type@j }} ->
     {{ Γ, ^(A : typ) ⊢ai BR ⟸ B[Id,,#0,,refl A[Wk] #0] }} ->
     {{ Γ ⊢ai N ⟸ Eq A M1 M2 }} ->
     nbe_ty Γ {{{ B[Id,,M1,,M2,,N] }}} C ->
     {{ Γ ⊢ai eqrec N as Eq A M1 M2 return B | refl -> BR end ⟹ C }} )
| ati_vlookup :
  `( {{ #x : A ∈ Γ }} ->
     nbe_ty Γ A B ->
     {{ Γ ⊢ai #x ⟹ B }} )
| ati_ann :
  `( {{ Γ ⊢ai A ⟹ Type@i }} ->
     {{ Γ ⊢ai M ⟸ A }} ->
     nbe_ty Γ A B ->
     {{ Γ ⊢ai M : A ⟹ B }} )
where "Γ '⊢ai' M ⟹ A" := (alg_type_infer Γ A M) (in custom judg) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer : mctt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.
