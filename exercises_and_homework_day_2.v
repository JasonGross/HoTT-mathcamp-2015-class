(** * Exploring equality via homotopy and proof assistants - Day 2 - Equality in Coq *)
(** This file contains the exercises for Day 2.  Some are explicitly
    marked as "Homework"; the rest can be done either in class or for
    homework.

    When doing exercises on your own, feel free to skip around; there
    are some interesting puzzles near the bottom (around
    [J_implies_UIP]).

    If you feel like you know exactly how a proof will go, but find it
    painful and tedius to write out the proof terms explicitly, come
    find me.  Coq has a lot of support for automation and taking care
    of things that are easy and verbose, so you don't have to.
    Proving should feel like a game.  If it doesn't, I can probably
    help you with that. *)

(** The following are placeholders; [admit] indicates that something
    should be filled in later. *)
Axiom admit : forall {T}, T.
Axiom admit1 : forall {T}, T.
Axiom admit2 : forall {T}, T.
Axiom admit3 : forall {T}, T.

(** ** Tautologies *)

(** We'll fill in these first few together.  Any ideas for how to to prove something like this? *)

Definition id : forall A, A -> A
  := admit.

Definition modus_ponens : forall P Q, (P -> Q) -> P -> Q
  := admit.

(** N.B. [A -> (B -> C)] and [A -> B -> C] are the same; [->] associates to the right. *)

Definition second_argument : forall A B, A -> (B -> A)
  := admit.

Definition compose : forall A B C, (A -> B) -> (B -> C) -> (A -> C)
  := admit.

(** We can also fill in the functions bit by bit, as follows: *)

Definition compose' : forall A B C, (A -> B) -> (B -> C) -> (A -> C).
Proof.
  refine _.
  refine admit.
Defined.

(** These two are exercises to do individually or with the people
    sitting next to you. *)

Definition introduce_intermediate : forall A B C, (A -> (B -> C)) -> ((A -> B) -> (A -> C))
  := admit.

Definition swap_args : forall A B C, (A -> B -> C) -> (B -> A -> C)
  := admit.

(** Challenge Homework Problems *)

(** Prove that the Law of Excluded Middle implies Double Negation Elimination *)

Definition LEM_implies_DNE
: (forall P, P \/ ~P)
  -> (forall P, ~~P -> P)
  := admit.

(** Prove that Double Negation Elimination implies Peirce's Law *)

Definition DNE_implies_Peirce
: (forall P, ~~P -> P)
  -> (forall P Q : Prop, ((P -> Q) -> P) -> P)
  := admit.

(** Prove that Peirce's Law implies the Law of Excluded Middle *)

Definition Peirce_implies_LEM
: (forall P Q : Prop, ((P -> Q) -> P) -> P)
  -> (forall P, P \/ ~P)
  := admit.

(** ** Judgmental equality. *)

About eq_refl.
About eq.
Print eq.

(** We allow writing [refl] for [eq_refl]. *)

Notation refl := eq_refl.

(** Coq knows some things about equality.  If Coq judges that two
    things are equal, then you can prove them equal by reflexivity,
    with [refl].  For example: *)

Definition one_plus_one_equals_two : 1 + 1 = 2
  := refl.

Definition two_plus_two_equals_four : 2 + 2 = 4
  := refl.

Definition two_times_three_equals_six : 2 * 3 = 6
  := refl.

(** Just so that you don't think Coq believes everything is equal: *)

Fail Definition one_does_not_equal_zero : 1 = 0
  := refl.

(** This gives
<<
The command has indeed failed with message:
=> Error: The term "refl" has type "?30 = ?30"
    while it is expected to have type "1 = 0".
>> *)

(** You can see the "normal form" of something with [Compute]: *)

Compute 1 + 1.

Compute 2 + 2.

Compute 2 * 3.

(** Note that equality is homogenous.  You can ask if a statement is valid using [Check]: *)

Check 1. (* [1] is a number (a [nat]) *)

Check 1 = 1. (* [1 = 1] is a proposition (a [Prop]) *)

Check true. (* [true] is a boolean *)

Fail Check 1 = true. (* [1] is a [nat], and so isn't comparable to [true], which is a [bool] *)

(** We can prove the J-rule by pattern matching. *)

Definition J : forall (A : Type) (x : A) (P : forall (y : A), x = y -> Type),
                 P x refl -> forall (y : A) (H : x = y), P y H
  := admit.

(** [J] also has a computation rule, which holds judgmentally: *)

Definition J_computes : forall (A : Type) (x : A) (P : forall (y : A), x = y -> Type)
                               (k : P x refl),
                          J A x P k x refl = k
  := admit.

(** If you want to not always have to pass all of the arguments to [J]
    explicitly, you can uncomment the following lines, removing the <<
    and >>, to make [A], [x], and [y] be inferred automatically. *)
(**
<<
Arguments J {A} {x} P _ {y} H.
Arguments J_computes {A x} P k.
>> *)

(** First prove this by pattern matching. *)

Definition sym : forall A (x y : A), x = y -> y = x
  := admit.

(** We allow writing [sym p] to mean [sym _ _ _ p] *)

Arguments sym {A x y} p, A x y p.

(** Now prove this by passing arguments to [J]. *)

Definition sym_J : forall A (x y : A), x = y -> y = x
  := admit.

Arguments sym_J {A x y} p, A x y p.

(** First prove this by pattern matching. *)

Definition trans : forall A (x y z : A), x = y -> y = z -> x = z
  := admit.

Arguments trans {A x y z} p q, A x y z p q.

(** Now prove this by passing arguments to [J]. *)

Definition trans_J : forall A (x y z : A), x = y -> y = z -> x = z
  := admit.

Arguments trans_J {A x y z} p q, A x y z p q.

(** First prove this by pattern matching. *)

Definition ap : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := admit.

Arguments ap {A B} f {x y} p, {A B} f x y p, A B f x y p.

(** Now prove this by passing arguments to [J]. *)

Definition ap_J : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := admit.

Arguments ap_J {A B} f {x y} p, {A B} f x y p, A B f x y p.

(** Exercises to do individually, or with the people next to you. *)

(** First prove this by pattern matching. *)

Definition sym_sym : forall A (x y : A) (p : x = y), sym (sym p) = p
  := admit.

Arguments sym_sym {A x y} p, A x y p.

(** Now prove this by filling in arguments to [J] explicitly. *)

Definition sym_sym_J : forall A (x y : A) (p : x = y), sym (sym p) = p
  := admit.

Definition trans_1p : forall A (x y : A) (p : x = y), trans refl p = p
  := admit.

Definition trans_1p_J : forall A (x y : A) (p : x = y), trans refl p = p
  := admit.

Definition trans_p1 : forall A (x y : A) (p : x = y), trans p refl = p
  := admit.

Definition trans_p1_J : forall A (x y : A) (p : x = y), trans p refl = p
  := admit.

Definition sym_refl : forall A (x : A), sym (refl x) = refl x
  := admit.

(** Recall the informal proof from yesterday's homework, which
    "proved" that all proofs of [x = y] are themselves equal:

    The [J] rule says informally that if you have a proof [p] of [x =
    y], it suffices to assume that [y] _is_ [x] (to substitute [x] for
    [y] in what you are trying to prove), and to assume that [p] is
    [refl x] (to substitute [refl x] for [p] in what you are trying to
    prove).  Suppose we have a type [A], two inhabitants [x] and [y]
    of type [A], and two proofs [p] and [q] that [x = y].  By [J], it
    suffices to assume that [y] is [x], that [p] is [refl x], and
    hence it suffices to prove that [refl x = q], where [q] now has
    type [x = x].  To prove this, again by [J], it suffices to assume
    that [x] is [x] (it already is) and that [q] is [refl x], and
    hence it suffices to prove [refl x = refl x].  We can prove this
    by [refl (refl x)].  Thus for any proofs [p] and [q] that [x = y],
    we have [p = q].  Qed.

    Try to formalize this proof in Coq, and see what goes wrong.  It
    may help to use [refine] so that you can construct the proof
    sentence by sentence.  If you are having trouble figuring out how
    to instantiate [J] for a proof of equality [H : x = y], you can
    ask Coq to figure it out for you by running [destruct H.].  You
    can see what it did by typing [Show Proof.] afterwards. *)

Definition J_implies_UIP : forall A (x y : A) (p q : x = y), p = q.
Proof.
  refine _.
  refine admit.
Abort.

(** The rest of these are explicitly Homework; feel free to take a
    break now, or to keep going. *)

(** Recall from yesterday's homework that the [K] rule says: *)

Definition K_rule_type
  := forall A (x : A) (P : x = x -> Type), P refl -> forall (H : x = x), P H.

(** Prove that [K] implies uniqueness of identity proofs.  If you do
    this interactively with [refine], you may find it useful to
    [unfold K_rule_type in *] to see the definition of [K] in your
    goals window. *)

Definition K_implies_UIP : forall (K : K_rule_type),
                           forall A (x y : A) (p q : x = y), p = q
  := admit.

(** Can you prove [K] from [J]?  (Don't worry if you can't figure this one out.) *)

Definition J_implies_K : K_rule_type
  := admit.

(** Can you write down three "different" proofs of transitivity (they
    should all be judgmentally different; [refl] should not prove any
    two of them the same. *)

Definition trans1 : forall A (x y z : A), x = y -> y = z -> x = z
  := admit1.
Definition trans2 : forall A (x y z : A), x = y -> y = z -> x = z
  := admit2.
Definition trans3 : forall A (x y z : A), x = y -> y = z -> x = z
  := admit3.

(** Now we have Coq check that they are not the same; these lines should compile unmodified. *)

Fail Check refl : trans1 = trans2.

Fail Check refl : trans2 = trans3.

Fail Check refl : trans1 = trans3.

(** Now prove that these are all equal (propositionally, but not judgmentally. *)

Definition trans_12 : forall A (x y z : A) (p : x = y) (q : y = z),
                        trans1 A x y z p q = trans2 A x y z p q
  := admit.
Definition trans_23 : forall A (x y z : A) (p : x = y) (q : y = z),
                        trans2 A x y z p q = trans3 A x y z p q
  := admit.

(** We can also prove associativity. *)

Definition trans_assoc : forall A (x y z w : A) (p : x = y) (q : y = z) (r : z = w),
                           trans p (trans q r) = trans (trans p q) r
  := admit.

Definition trans_pV : forall A (x y : A) (p : x = y),
                        trans p (sym p) = refl
  := admit.

Definition trans_Vp : forall A (x y : A) (p : x = y),
                        trans (sym p) p = refl
  := admit.

Definition trans_sym : forall A (x y z : A) (p : x = y) (q : y = z),
                         sym (trans p q) = trans (sym q) (sym p)
  := admit.

(** *** Category theory *)

(** Those of you familiar with category theory might find the
    following properties interesting. *)

(** All exercises in this section are optional homework. *)

(** We can look at [ap] as describing the action on morphisms
    (equality proofs) of any function; the type of morphisms from [x :
    A] to [y : A] is the type [x = y]; the action of [f : A -> B] on a
    morphism [m : x = y] is [ap f m : f x = f y].  We can prove the
    relevant functoriality properties. *)

(** Action on identity: *)

Definition ap_refl : forall {A B} (f : A -> B) x, ap f (refl x) = refl (f x)
  := admit.

(** Action on composition: *)

Definition ap_trans : forall {A B} (f : A -> B) {x y z : A} (p : x = y) (q : y = z),
                           ap f (trans p q) = trans (ap f p) (ap f q)
  := admit.

(** Action on inverses (additional rule for groupoids): *)

Definition ap_sym : forall {A B} (f : A -> B) {x y : A} (p : x = y),
                         ap f (sym p) = sym (ap f p)
  := admit.

(** Furthermore, every function that specifies the action of a natural
    transformation on objects is automatically natural: *)

Definition concat_Ap
: forall {A B} (f g : A -> B)
         (T : forall x, f x = g x),
    forall {x y : A} (m : x = y),
      trans (ap f m) (T y) = trans (T x) (ap g m)
  := admit.

(** *** Further exploration:

1. Can you find and prove a statement relating [sym_sym] to [sym_trans]?

2. Can you find and prove a statement relating [trans] to [ap]?

3. Can you find and prove a statement relating [sym] to [trans_assoc] and [sym_trans] via [ap]?

4. The equality relation on a type forms a weak ω-groupoid (sometimes
   written as a weak ∞-groupoid).  This means that there is structure
   at every level.  The first few levels are given by [refl], [sym],
   and [trans] (level 1); [sym_sym], [sym_trans], [trans_assoc],
   [sym_refl], [trans_1p], [trans_p1], [trans_pV], and [trans_Vp]
   (level 2).  The theorem statements in general are known as the
   Stasheff polyhedra or Stasheff associahedra.  Can you discover more
   of these rules? *)
