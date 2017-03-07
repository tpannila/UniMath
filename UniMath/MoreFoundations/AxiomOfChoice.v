(** * Axiom of choice *)

Require Export UniMath.MoreFoundations.DecidablePropositions.

Local Open Scope logic.

Local Open Scope set.

(** We write these axioms as types rather than as axioms, which would assert them to be true, to
    force them to be mentioned as explicit hypotheses whenever they are used. *)

Definition AxiomOfChoice : hProp := ∀ (X:hSet), ischoicebase X.

Definition AxiomOfChoice_surj : hProp := ∀ (X:hSet) (Y:UU) (f:Y→X), issurjective f ⇒ ∃ g, ∀ x, f (g x) = x.

(** Notice that the equation above is a proposition only because X is a set, which is not required
    in the previous formulation.  The notation for "=" currently in effect uses [eqset] instead of
    [paths].  *)

(** ** Implications between forms of the Axiom of Choice *)

Lemma AC_impl2_issurj (X : hSet) (P : X -> UU) (ne : ∏ x : X, ∥ P x ∥)
  (T := (∑ x, P x)%type) (f := pr1 : T -> X) :
  issurjective f.
Proof.
  intros x.
  use (hinhuniv _ (ne x)).
  intros p.
  use hinhpr.
  use hfiberpair.
  - exact (tpair _ x p).
  - use idpath.
Qed.

Lemma AC_impl2 : AxiomOfChoice <-> AxiomOfChoice_surj.
Proof.
  split.
  - intros AC X Y f surj.
    use (squash_to_prop (AC _ _ surj) (propproperty _)).
    intro s.
    use hinhpr.
    use tpair.
    + exact (λ y, hfiberpr1 f y (s y)).
    + exact (λ y, hfiberpr2 f y (s y)).
  - intros AC X P ne.
    use (hinhuniv _ (AC X _ _ (AC_impl2_issurj X P ne))).
    intros sec. use hinhpr. intros x.
    induction (pr2 sec x). exact (pr2 (pr1 sec x)).
Defined.

(** ** The Axiom of Choice implies the Law of the Excluded Middle  *)

(** This result is covered in the HoTT book, is due to Radu Diaconescu, "Axiom of choice and
    complementation", Proceedings of the American Mathematical Society, 51 (1975) 176–178, and was
    first mentioned on page 4 in F. W. Lawvere, "Toposes, algebraic geometry and logic (Conf.,
    Dalhousie Univ., Halifax, N.S., 1971)", pp. 1–12, Lecture Notes in Math., Vol. 274, Springer,
    Berlin, 1972.

    The idea is to define an equivalence relation E on bool by setting [E true false := P], to use
    AC to split the surjection f from bool to its quotient by E with a function g, and to observe
    that the function [g ∘ f : bool -> bool] is constant iff P, and to observe that being constant is
    decidable, because equality in [bool] is decidable. *)

Definition AC_to_LEM_hrel (AC : AxiomOfChoice) (P : hProp) (ifb := bool_rect (λ _:bool, hProp)) :
  hrel bool := λ x y, ifb (ifb htrue P y) (ifb P htrue y) x.

Lemma AC_to_LEM_hrel_iseqrel (AC : AxiomOfChoice) (P : hProp) (ifb := bool_rect (λ _:bool, hProp)) :
  iseqrel (AC_to_LEM_hrel AC P).
Proof.
  use iseqrelconstr.
  - intros x y z a b. induction x.
    + induction y.
      * induction z; exact b.
      * induction z.
        -- exact tt.
        -- exact a.
    + induction y.
      * induction z.
        -- exact a.
        -- exact tt.
      * induction z; exact b.
  - intros x. induction x; exact tt.
  - intros x y a. induction x; induction y; exact a.
Qed.

Lemma AC_to_LEM_coll (AC : AxiomOfChoice) (P : hProp) (ifb := bool_rect (λ _:bool, hProp))
      (E := eqrelpair (AC_to_LEM_hrel AC P) (AC_to_LEM_hrel_iseqrel AC P))
      (Y := setquotinset E) (f := (setquotpr E : bool → Y) : bool → Y)
      (sec : ∑ g : Y → boolset, ∀ x : Y, f (g x) = x) :
  P <-> (pr1 sec) (f true) = (pr1 sec) (f false).
Proof.
  split.
  - intro p. use maponpaths. use iscompsetquotpr. exact p.
  - intro q.
    assert (r : f true = f false).
    {
      intermediate_path (f ((pr1 sec) (f true))).
      + use pathsinv0. use (pr2 sec).
      + intermediate_path (f ((pr1 sec) (f false))).
        * use maponpaths. use q.
        * use (pr2 sec).
    }
    change (E true false).
    use (invmap (weqpathsinsetquot _ _ _)).
    change (f true = f false).
    exact r.
Qed.

Theorem AC_to_LEM : AxiomOfChoice -> LEM.
Proof.
  intros AC P.
  set (ifb := bool_rect (λ _:bool, hProp)).
  set (R := λ x y, ifb (ifb htrue P y) (ifb P htrue y) x); simpl in R.
  set (e := AC_to_LEM_hrel_iseqrel AC P).
  set (E := eqrelpair (AC_to_LEM_hrel AC P) (AC_to_LEM_hrel_iseqrel AC P)).
  set (Y := setquotinset E).
  set (f := setquotpr E).
  use (squash_to_prop (pr1 AC_impl2 AC Y boolset f (issurjsetquotpr E)) (propproperty _)).
  intro sec.
  (* the equation is decidable, and thus P is decidable, by the lemma above *)
  use (logeq_dec (issymm_logeq _ _ (AC_to_LEM_coll AC P sec))).
  use isdeceqbool.
Defined.

(* end of file *)
