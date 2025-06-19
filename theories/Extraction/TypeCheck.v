From Coq Require Import Morphisms_Relations.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Soundness Require Import EqualityCases.
From Mctt.Extraction Require Import NbE PseudoMonadic Subtyping.
From Mctt.Frontend Require Import Elaborator.
Import Domain_Notations.

Section lookup.
  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | |- ~ _ => intro
    | H: {{ ⊢ ^_, ^_ }} |- _ => inversion_clear H
    | H: {{ # _ : ^_ ∈ ⋅ }} |- _ => inversion_clear H
    | H: {{ # (S _) : ^_ ∈ ^_, ^_ }} |- _ => inversion_clear H
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros;
    repeat impl_obl_tac1;
    intuition (mauto 4).

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations lookup G (HG : {{ ⊢ G }}) x : { A | {{ #x : A ∈ G }} } + { forall A, ~ {{ #x : A ∈ G }} } :=
  | {{{ G, A }}}, HG, x with x => {
    | 0 => pureo (exist _ {{{ A[Wk] }}} _)
    | S x' =>
        let*o (exist _ B _) := lookup G _ x' while _ in
        pureo (exist _ {{{ B[Wk] }}} _)
    }
  | {{{ ⋅ }}}, HG, x => inright _.
End lookup.

Section type_check.
  #[derive(equations=no,eliminator=no)]
  Equations get_level_of_type_nf (A : nf) : { i | A = n{{{ Type@i }}} } + { forall i, A <> n{{{ Type@i }}} } :=
  | n{{{ Type@i }}} => pureo (exist _ i _)
  | _               => inright _
  .

  (** Don't forget to use 9th bit of [Extraction Flag] (for example, [Set Extraction Flag 1007.]).
      Otherwise, this function would introduce redundant pair construction/pattern matching. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_subterms_of_pi_nf (A : nf) : { B & { C | A = n{{{ Π B C }}} } } + { forall B C, A <> n{{{ Π B C }}} } :=
  | n{{{ Π B C }}} => pureo (existT _ B (exist _ C _))
  | _              => inright _
  .

  Extraction Inline get_level_of_type_nf get_subterms_of_pi_nf.

  Inductive type_check_order : exp -> Prop :=
  | tc_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order : exp -> Prop :=
  | ti_typ : forall {i}, type_infer_order {{{ Type@i }}}
  | ti_nat : type_infer_order {{{ ℕ }}}
  | ti_zero : type_infer_order {{{ zero }}}
  | ti_succ : forall {M}, type_check_order M -> type_infer_order {{{ succ M }}}
  | ti_natrec : forall {A MZ MS M}, type_check_order M -> type_infer_order A -> type_check_order MZ -> type_check_order MS -> type_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}}
  | ti_pi : forall {A B}, type_infer_order A -> type_infer_order B -> type_infer_order {{{ Π A B }}}
  | ti_fn : forall {A M}, type_infer_order A -> type_infer_order M -> type_infer_order {{{ λ A M }}}
  | ti_app : forall {M N}, type_infer_order M -> type_check_order N -> type_infer_order {{{ M N }}}
  | ti_eq : forall {A M1 M2}, type_infer_order A -> type_check_order M1 -> type_check_order M2 -> type_infer_order {{{ Eq A M1 M2 }}}
  | ti_refl : forall {A M}, type_infer_order A -> type_check_order M -> type_infer_order {{{ refl A M }}}
  | ti_eqrec : forall {N A M1 M2 B BR}, type_check_order N -> type_infer_order A -> type_check_order M1 -> type_check_order M2 -> type_infer_order B -> type_check_order BR -> type_infer_order {{{ eqrec N as Eq A M1 M2 return B | refl -> BR end }}}
  | ti_vlookup : forall {x}, type_infer_order {{{ #x }}}
  .

  #[local]
  Hint Constructors type_check_order type_infer_order : mctt.

  Lemma user_exp_to_type_infer_order : forall M,
      user_exp M ->
      type_infer_order M.
  Proof.
    intros M HM.
    enough (type_check_order M) as [] by eassumption.
    induction HM; progressive_inversion; do 2 constructor; trivial with mctt.
  Qed.

  #[local]
  Ltac clear_defs :=
    repeat lazymatch goal with
      | H: (forall (G : ctx) (A : typ),
               (exists i : nat, {{ G ⊢ A : Type@i }}) ->
               forall M : typ,
                 type_check_order M ->
                 ({ {{ G ⊢a M ⟸ A }} } + { ~ {{ G ⊢a M ⟸ A }} }))
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall (G : ctx) (A : typ),
              (exists i : nat, {{ G ⊢ A : Type @ i }}) -> forall M : typ, type_check_order M -> { {{ G ⊢a M ⟸ A }} } + { ~ {{ G ⊢a M ⟸ A }} })
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall G : ctx,
              {{ ⊢ G }} ->
              forall M : typ,
                type_infer_order M ->
                ({ B : nf | {{ G ⊢a M ⟹ B }} /\ (exists i : nat, {{ G ⊢a ^(nf_to_exp B) ⟹ Type@i }}) } + { forall C : nf, ~ {{ G ⊢a M ⟹ C }} }))
        |- _ =>
          clear H
      | H: (forall G : ctx,
               {{ ⊢ G }} ->
               forall M : typ,
                 type_infer_order M ->
                 ({ B : nf | {{ G ⊢a M ⟹ B }} /\ (exists i : nat, {{ G ⊢a ^(nf_to_exp B) ⟹ Type@i }}) } + { forall C : nf, ~ {{ G ⊢a M ⟹ C }} }))
        |- _ =>
          clear H
    end.

  #[local]
  Ltac impl_obl_tac :=
    clear_defs;
    try match goal with
      | H: type_check_order _ |- _ => progressive_invert H
      end;
    repeat match goal with
      | H: type_infer_order _ |- _ => progressive_invert H
      end;
    destruct_conjs;
    functional_alg_type_infer_rewrite_clear;
    repeat (match goal with
            | |- _ /\ _ => split
            end);
    (try lazymatch goal with
       | |- nbe_ty_order ?G ?A =>
           gen_presups; enough (exists i, {{ G ⊢ A : ^(nf_to_exp (nf_typ i)) }}) as [? [? []]%soundness_ty] by eauto 3 using nbe_ty_order_sound
       | |- nbe_order ?G ?M ?A =>
           gen_presups; enough ({{ G ⊢ M : A }}) as [? []]%soundness by eauto 3 using nbe_ty_order_sound
       | |- exists _, {{ ^?G ⊢ ^?A : ^(a_typ _) }} => enough (exists i, {{ ^G ⊢ ^A : ^n{{{ Type@i }}} }}) by eauto 2
       end);
    (try
       lazymatch goal with
       | |- {{ ⊢ ^?G, ^?A }} =>
           gen_presups;
           assert {{ ⊢ G }} by mauto 3;
           unshelve (eassert {{ G ⊢ A : ^n{{{ Type@_ }}} }}; solve [mauto 3 using alg_type_infer_sound]); solve [constructor]
       | |- {{ ⊢ ^_ }} => gen_presups; mautosolve 3
       | H: {{ ^?G ⊢ ^?A : Type@?i }} |- {{ ^?G ⊢ ^?A : Type@(Nat.max ?i ?j) }} => apply lift_exp_max_left; mautosolve 3
       | H: {{ ^?G ⊢ ^?A : Type@?j }} |- {{ ^?G ⊢ ^?A : Type@(Nat.max ?i ?j) }} => apply lift_exp_max_right; mautosolve 3
       | |- exists _, {{ ^?G ⊢ ^?A : ^(nf_to_exp (nf_typ _)) }} =>
           gen_presups;
           assert {{ ⊢ G }} by mauto 3;
           unshelve (eexists; solve [mauto 3 using alg_type_infer_sound, alg_type_check_sound]); solve [constructor]
       | |- {{ ^_ ⊢ ^_ : ^_ }} => gen_presups; mautosolve 3
       | |- _ -> ~ {{ ^_ ⊢a ^_ ⟸ ^_ }} =>
           let H := fresh "H" in
           intros ? H;
           directed dependent destruction H;
           functional_alg_type_infer_rewrite_clear;
           firstorder
       | |- _ -> (forall A : nf, ~ {{ ^_ ⊢a ^_ ⟹ ^_ }}) =>
           unfold not in *;
           intros;
           progressive_inversion;
           functional_alg_type_infer_rewrite_clear;
           solve [congruence | mautosolve 3]
       | |- type_infer_order _ => eassumption; fail 1
       | |- type_check_order _ => eassumption; fail 1
       | |- subtyping_order ?G ?A ?B =>
           enough (exists i, {{ G ⊢ A : ^n{{{ Type@i }}} }}) as [? [? []]%soundness_ty];
           [ enough (exists j, {{ G ⊢ B : ^n{{{ Type@j }}} }}) as [? [? []]%soundness_ty];
             [solve [econstructor; eauto 4 using nbe_ty_order_sound] |]
           |
           ];
           gen_presups;
           unshelve (eexists; solve [mauto 2 using alg_type_infer_sound]); solve [constructor]
       | _ => try mautosolve 3
       end).

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check G A (HA : (exists i, {{ G ⊢ A : Type@i }})) M (H : type_check_order M) : { {{ G ⊢a M ⟸ A }} } + { ~ {{ G ⊢a M ⟸ A }} } by struct H :=
  | G, A, HA, M, H =>
      let*o->b (exist _ B _) := type_infer G _ M _ while _ in
      let*b _ := subtyping_impl G (B : nf) A _ while _ in
      pureb _
  with type_infer G (HG : {{ ⊢ G }}) M (H : type_infer_order M) : { A : nf | {{ G ⊢a M ⟹ A }} /\ (exists i, {{ G ⊢a A ⟹ Type@i }}) } + { forall A, ~ {{ G ⊢a M ⟹ A }} } by struct H :=
  | G, HG, M, H with M => {
    | {{{ Type@j }}} =>
        pureo (exist _ n{{{ Type@(S j) }}} _)
    | {{{ ℕ }}} =>
        pureo (exist _ n{{{ Type@0 }}} _)
    | {{{ zero }}} =>
        pureo (exist _ n{{{ ℕ }}} _)
    | {{{ succ M' }}} =>
        let*b->o _ := type_check G {{{ ℕ }}} _ M' _ while _ in
        pureo (exist _ n{{{ ℕ }}} _)
    | {{{ rec M' return A' | zero -> MZ | succ -> MS end }}} =>
        let*b->o _ := type_check G {{{ ℕ }}} _ M' _ while _ in
        let*o (exist _ UA' _) := type_infer {{{ G, ℕ }}} _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G {{{ A'[Id,,zero] }}} _ MZ _ while _ in
        let*b->o _ := type_check {{{ G, ℕ, A' }}} {{{ A'[Wk∘Wk,,succ #1] }}} _ MS _ while _ in
        let (A'', _) := nbe_ty_impl G {{{ A'[Id,,M'] }}} _ in
        pureo (exist _ A'' _)
    | {{{ Π B C }}} =>
        let*o (exist _ UB _) := type_infer G _ B _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UB while _ in
        let*o (exist _ UC _) := type_infer {{{ G, B }}} _ C _ while _ in
        let*o (exist _ j _) :=  get_level_of_type_nf UC while _ in
        pureo (exist _ n{{{ Type@(max i j) }}} _)
    | {{{ λ A' M' }}} =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*o (exist _ B' _) := type_infer {{{ G, A' }}} _ M' _ while _ in
        let (A'', _) := nbe_ty_impl G A' _ in
        pureo (exist _ n{{{ Π A'' B' }}} _)
    | {{{ M' N' }}} =>
        let*o (exist _ C _) := type_infer G _ M' _ while _ in
        let*o (existT _ A (exist _ B _)) := get_subterms_of_pi_nf C while _ in
        let*b->o _ := type_check G (A : nf) _ N' _ while _ in
        let (B', _) := nbe_ty_impl G {{{ ^(B : nf)[Id,,N'] }}} _ in
        pureo (exist _ B' _)
    | {{{ Eq A' M1' M2' }}} =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G A' _ M1' _ while _ in
        let*b->o _ := type_check G A' _ M2' _ while _ in
        pureo (exist _ n{{{ Type@i }}} _)
    | {{{ refl A' M' }}} =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G A' _ M' _ while _ in
        let (A'', _) := nbe_ty_impl G A' _ in
        let (M'', _) := nbe_impl G M' A' _ in
        pureo (exist _ n{{{ Eq A'' M'' M'' }}} _)
    | {{{ eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end }}} =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G A' _ M1' _ while _ in
        let*b->o _ := type_check G A' _ M2' _ while _ in
        let*o (exist _ UB' _) := type_infer {{{ G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }}} _ B' _ while _ in
        let*o (exist _ j _) :=  get_level_of_type_nf UB' while _ in
        let*b->o _ := type_check {{{ G, A' }}} {{{ B'[Id,,#0,,refl A'[Wk] #0] }}} _ BR' _ while _ in
        let*b->o _ := type_check G {{{ Eq A' M1' M2' }}} _ N' _ while _ in
        let (B'', _) := nbe_ty_impl G {{{ B'[Id,,M1',,M2',,N'] }}} _ in
        pureo (exist _ B'' _)
    | {{{ #x }}} =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let (A', _) := nbe_ty_impl G A _ in
        pureo (exist _ A' _)
    | _ => inright _
    }
  .

  Next Obligation. (* exists j, {{ G ⊢ A'[Id,,zero] : Type@j }} *)
    impl_obl_tac.
    eexists.
    assert {{ ⊢ G, ℕ }} by mauto 3.
    eassert {{ G, ℕ ⊢ A' : ^n{{{ Type@_ }}} }}; solve [mauto 3 using alg_type_infer_sound].
  Qed.

  Next Obligation. (* exists j, {{ G, ℕ, A' ⊢ A'[Wk∘Wk,,succ #1] : Type@i }} *)
    impl_obl_tac.
    eexists.
    assert {{ ⊢ G, ℕ }} by mauto 3.
    assert {{ G, ℕ ⊢ A' : ^n{{{ Type@i }}} }}; solve [mauto 3 using alg_type_infer_sound].
  Qed.

  Next Obligation. (* nbe_ty_order G {{{ A'[Id,,M'] }}} *)
    impl_obl_tac.
    eexists.
    assert {{ G ⊢ ℕ : Type@0 }} by mauto 2.
    assert {{ ⊢ G, ℕ }} by mauto 2.
    assert {{ G, ℕ ⊢ A' : ^n{{{ Type@i }}} }} by mauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ M' : ℕ }} by mauto 2 using alg_type_check_sound.
    mauto 3 using alg_type_check_sound.
  Qed.

  Next Obligation. (* {{ G ⊢a rec M' return A' | zero -> MZ | succ -> MS end ⟹ A'' }} /\ (exists j, {{ G ⊢a A'' ⟹ Type@j }}) *)
    impl_obl_tac.
    assert {{ G ⊢ ℕ : Type@0 }} by mauto 2.
    assert {{ ⊢ G, ℕ }} by mauto 2.
    assert {{ G, ℕ ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ M' : ℕ }} by eauto 2 using alg_type_check_sound.
    assert {{ G ⊢ A'[Id,,M'] : Type@i }} by mauto 3.
    assert {{ G ⊢ A'[Id,,M'] ≈ A'' : Type@i }} by eauto 2 using soundness_ty'.
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, {{ G ⊢a A'' ⟹ Type@j }} /\ j <= i) as [? []] by (gen_presups; mauto 3).
    eexists; eauto 2.
  Qed.

  Next Obligation. (* {{ G ⊢a Π B C ⟹ Type@(max i j) }} /\ (exists k, {{ G ⊢a Type@(max i j) ⟹ Type@k }}) *)
    impl_obl_tac.
  Qed.

  Next Obligation. (* {{ G ⊢a λ A' M' ⟹ Π A'' B' }} /\ (exists j, {{ G ⊢a Π A'' B' ⟹ Type@j }}) *)
    impl_obl_tac.
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ ⊢ G, A' }} by mauto 2.
    assert {{ G ⊢ A' ≈ A'' : Type@i }} by eauto 2 using soundness_ty'.
    assert {{ G ⊢ A'' : Type@i }} by (gen_presups; mauto 2).
    assert {{ ⊢ G, ^(A'' : exp) }} by mauto 2.
    eassert {{ G, A' ⊢ pat : ^n{{{ Type@_ }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ ⊢ G, A' ≈ G, ^(A'' : exp) }} by mauto 3.
    eassert {{ G, ^(A'' : exp) ⊢ pat : Type@_ }} by mauto 2.
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, {{ G ⊢a A'' ⟹ Type@j }} /\ j <= i) as [? []] by (gen_presups; mauto 2).
    assert (user_exp pat) by trivial using user_exp_nf.
    eassert (exists k, {{ G, ^(A'' : exp) ⊢a pat ⟹ Type@k }} /\ k <= H4) as [? []] by (gen_presups; mauto 2).
    eexists; mauto 2.
  Qed.

  Next Obligation. (* exists i : nat, {{ G ⊢ A : Type@i }} *)
    progressive_inversion.
    impl_obl_tac.
  Qed.

  Next Obligation. (* nbe_ty_order G {{{ s[Id,,N'] }}} *)
    impl_obl_tac.
    progressive_inversion.
    assert {{ G ⊢ A : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ ⊢ G, ^(A : exp) }} by mauto 2.
    assert {{ G, ^(A : exp) ⊢ s : ^n{{{ Type@j }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ N' : A }} by eauto 2 using alg_type_check_sound.
    eexists; mauto 3.
  Qed.

  Next Obligation. (* {{ G ⊢a M' N' ⟹ B' }} /\ (exists i, {{ G ⊢a B' ⟹ Type@i }}) *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    split; [mauto 3 |].
    assert {{ G ⊢ A : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ ⊢ G, ^(A : exp) }} by mauto 2.
    assert {{ G, ^(A : exp) ⊢ s : ^n{{{ Type@j }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢s Id,,N' : G, ^(A : exp) }} by mauto 3 using alg_type_check_sound.
    assert {{ G ⊢ s[Id,,N'] : ^n{{{ Type@j }}} }} by mauto 2.
    assert {{ G ⊢ s[Id,,N'] ≈ B' : Type@j }} by (mauto 2 using soundness_ty').
    assert (user_exp B') by trivial using user_exp_nf.
    assert (exists k, {{ G ⊢a B' ⟹ Type@k }} /\ k <= j) as [? []] by (gen_presups; mauto 2).
    eexists; eauto 2.
  Qed.

  Next Obligation. (* {{ G ⊢a Eq A' M1' M2' ⟹ Type@i }} /\ (exists i0 : nat, {{ G ⊢a Type@i ⟹ Type@i0 }}) *)
    impl_obl_tac.
  Qed.

  Next Obligation. (* nbe_order G M' A' *)
    clear_defs.
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ M' : A' }} as [? []]%soundness by eauto 2 using alg_type_check_sound.
    mauto 3 using nbe_order_sound.
  Qed.

  Next Obligation. (* {{ G ⊢a refl A' M' ⟹ Eq A'' M'' M'' }} /\ (exists i0 : nat, {{ G ⊢a Eq A'' M'' M'' ⟹ Type@i0 }}) *)
    clear_defs.
    split; [mautosolve 3 |].
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ A' ≈ A'' : Type@i }} by eauto 2 using soundness_ty'.
    assert {{ G ⊢ M' : A' }} by eauto 2 using alg_type_check_sound.
    assert {{ G ⊢ A' ≈ A'' : Type@i }} by eauto 2 using soundness_ty'.
    assert {{ G ⊢ M' ≈ M'' : A' }} by eauto 2 using soundness'.
    assert {{ G ⊢ M' ≈ M'' : A'' }} by mauto 2.
    assert {{ G ⊢ Eq A'' M'' M'' : Type@i }} by (gen_presups; mauto 2).
    assert (user_exp n{{{ Eq A'' M'' M'' }}}) by trivial using user_exp_nf.
    assert (exists k, {{ G ⊢a Eq A'' M'' M'' ⟹ Type@k }} /\ k <= i) as [? []] by (gen_presups; mauto 2).
    eexists; eauto 2.
  Qed.

  Next Obligation. (* {{ ⊢ G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} *)
    clear_defs.
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G, A' ⊢s Wk : G }} by mauto 3.
    assert {{ G, A' ⊢ A'[Wk] : Type@i }} by mauto 2.
    assert {{ ⊢ G, A', A'[Wk] }} by mauto 3.
    assert {{ G, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
    mauto 2.
  Qed.

  Next Obligation. (* exists i0 : nat, {{ G, A' ⊢ B'[Id,,#0,,refl A'[Wk] #0] : Type@i0 }} *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G, A' ⊢s Wk : G }} by mauto 3.
    assert {{ G, A' ⊢ A'[Wk] : Type@i }} by mauto 2.
    assert {{ ⊢ G, A', A'[Wk] }} by mauto 3.
    assert {{ G, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
    assert {{ G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 ⊢ B' : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    pose proof (@glu_rel_eq_eqrec_synprop_gen_A G {{{ Id }}} _ _ A' ltac:(mauto 2) ltac:(eassumption)).
    destruct_all.
    assert {{ G, A' ⊢ B'[Id,,#0,,refl A'[Wk] #0] : Type@j }} by mauto 2.
    eauto.
  Qed.

  Next Obligation. (* nbe_ty_order G {{{ B'[Id,,M1',,M2',,N'] }}} *)
    impl_obl_tac.
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ M1' : A' }} by eauto 2 using alg_type_check_sound.
    assert {{ G ⊢ M2' : A' }} by eauto 2 using alg_type_check_sound.
    assert {{ G ⊢ Eq A' M1' M2' : Type@i }} by mauto 2.
    assert {{ G ⊢ N' : Eq A' M1' M2' }} by eauto 2 using alg_type_check_sound.
    assert {{ G, A' ⊢s Wk : G }} by mauto 3.
    assert {{ G, A' ⊢ A'[Wk] : Type@i }} by mauto 2.
    assert {{ ⊢ G, A', A'[Wk] }} by mauto 3.
    assert {{ G, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
    assert {{ G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 ⊢ B' : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ G ⊢s Id,,M1',,M2',,N' : G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} by mauto 2.
    eexists; mauto 2.
  Qed.

  Next Obligation. (* {{ G ⊢a eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end ⟹ B'' }} /\ (exists i0 : nat, {{ G ⊢a B'' ⟹ Type@i0 }}) *)
    impl_obl_tac.
    assert {{ G ⊢ A' : ^n{{{ Type@i }}} }} by eauto 2 using alg_type_infer_sound.
    assert {{ G ⊢ M1' : A' }} by eauto 2 using alg_type_check_sound.
    assert {{ G ⊢ M2' : A' }} by eauto 2 using alg_type_check_sound.
    assert {{ G ⊢ Eq A' M1' M2' : Type@i }} by mauto 2.
    assert {{ G ⊢ N' : Eq A' M1' M2' }} by eauto 2 using alg_type_check_sound.
    assert {{ G, A' ⊢s Wk : G }} by mauto 3.
    assert {{ G, A' ⊢ A'[Wk] : Type@i }} by mauto 2.
    assert {{ ⊢ G, A', A'[Wk] }} by mauto 3.
    assert {{ G, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
    assert {{ G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 ⊢ B' : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ G ⊢s Id,,M1',,M2',,N' : G, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ G ⊢ B'[Id,,M1',,M2',,N'] : Type@j }} by mauto 2.
    assert {{ G ⊢ B'[Id,,M1',,M2',,N'] ≈ B'' : Type@j }} by eauto 2 using soundness_ty'.
    assert (user_exp B'') by eauto 2 using user_exp_nf.
    assert (exists k, {{ G ⊢a B'' ⟹ Type@k }} /\ k <= j) as [? []] by (gen_presups; mauto 2).
    eexists; eauto.
  Qed.

  Next Obligation. (* {{ G ⊢a #x ⟹ A' }} /\ (exists i, {{ G ⊢a A' ⟹ Type@i }}) *)
    impl_obl_tac.
    assert (exists i, {{ G ⊢ A : Type@i }}) as [i] by mauto 2.
    assert {{ G ⊢ A ≈ A' : Type@i }} by (eapply soundness_ty'; eauto 2 using alg_type_check_sound).
    assert (user_exp A') by trivial using user_exp_nf.
    assert (exists j, {{ G ⊢a A' ⟹ Type@j }} /\ j <= i) as [? []] by (gen_presups; mauto 2).
    eexists; eauto 2.
  Qed.

  Extraction Inline type_check_functional type_infer_functional.

  Lemma type_infer_order_soundness : forall G M A,
      {{ G ⊢a M ⟹ A }} ->
      type_infer_order M
  with type_check_order_soundness : forall G M A,
      {{ G ⊢a M ⟸ A }} ->
      type_check_order M.
  Proof.
    - clear type_infer_order_soundness.
      induction 1; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
    - clear type_check_order_soundness.
      induction 1; mauto 3.
  Qed.
End type_check.

#[local]
Hint Resolve type_check_order_soundness type_infer_order_soundness : mctt.

Lemma type_check_complete' : forall G M A (HA : exists i, {{ G ⊢ A : Type@i }}),
    {{ G ⊢a M ⟸ A }} ->
    exists H H', type_check G A HA M H = left H'.
Proof.
  intros ? ? ? [] ?.
  assert (Horder : type_check_order M) by mauto.
  exists Horder.
  dec_complete.
Qed.

Lemma type_infer_complete : forall G M A (HG : {{ ⊢ G }}),
    {{ G ⊢a M ⟹ A }} ->
    exists H H', type_infer G HG M H = inleft (exist _ A H').
Proof.
  intros.
  assert (Horder : type_infer_order M) by mauto.
  exists Horder.
  destruct (type_infer G HG M Horder) as [[? []] |].
  - functional_alg_type_infer_rewrite_clear.
    eexists; reflexivity.
  - contradict H; intuition.
Qed.

Section type_check_closed.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check_closed A (HA : user_exp A) M (HM : user_exp M) : { {{ ⋅ ⊢ M : A }} } + { ~ {{ ⋅ ⊢ M : A }} } :=
  | A, HA, M, HM =>
      let*o->b (exist _ UA _) := type_infer {{{ ⋅ }}} _ A _ while _ in
      let*o->b (exist _ i _) :=  get_level_of_type_nf UA while _ in
      let*b _ := type_check {{{ ⋅ }}} A _ M _ while _ in
      pureb _
  .
  Next Obligation. (* False *)
    assert {{ ⊢ ⋅ }} by mauto 2.
    assert (exists i, {{ ⋅ ⊢ A : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert (exists j, {{ ⋅ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    firstorder.
  Qed.
  Next Obligation. (* False *)
    assert (exists i, {{ ⋅ ⊢ A : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert (exists j, {{ ⋅ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    functional_alg_type_infer_rewrite_clear.
    intuition.
  Qed.
  Next Obligation. (* exists i, {{ ⋅ ⊢ A : Type@i }} *)
    assert {{ ⊢ ⋅ }} by mauto 2.
    assert {{ ⋅ ⊢ A : ^n{{{ Type@i }}} }} by mauto 2 using alg_type_infer_sound.
    simpl in *.
    firstorder.
  Qed.
  Next Obligation. (* {{ ⋅ ⊢ M : A }} *)
    assert {{ ⊢ ⋅ }} by mauto 2.
    assert {{ ⋅ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    simpl in *.
    mauto 3 using alg_type_check_sound.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete : forall A (HA : user_exp A) M (HM : user_exp M),
    {{ ⋅ ⊢ M : A }} ->
    exists H', type_check_closed A HA M HM = left H'.
Proof. intros; dec_complete. Qed.
