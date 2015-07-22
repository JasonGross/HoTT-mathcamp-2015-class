(** * Exploring equality via homotopy and proof assistants - Day 2 - Equality in Coq *)
(** Note: You may use either the lab computers, or your laptop.  Coq
    may not be installed on the Windows computers, you should use the
    Macs.  If the Macs do not have CoqIDE installed, you can go to
    https://coq.inria.fr/coq-85, download CoqIDE_8.5beta2.dmg, open
    it, and run CoqIDE directly, without installing it.

    This file contains the exercises for Day 2.  Some are explicitly
    marked as "Homework"; the rest can be done either in class or for
    homework.

    When doing exercises on your own, feel free to skip around; there
    are some interesting puzzles near the bottom (around
    [J_implies_UIP]).

    If you feel like you know exactly how a proof will go, but find it
    painful and tedious to write out the proof terms explicitly, come
    find me.  Coq has a lot of support for automation and taking care
    of things that are easy and verbose, so you don't have to.
    Proving should feel like a game.  If it doesn't, I can probably
    help you with that.

    N.B. There are many theorem provers out there, e.g., Agda, Idris,
    NuPRL, Otter, Twelf, Isabelle/HOL, Mizar, Metamath *)

(** The following are placeholders; [admit] indicates that something
    should be filled in later. *)
Axiom admit : forall {T}, T.
Axiom admit1 : forall {T}, T.
Axiom admit2 : forall {T}, T.
Axiom admit3 : forall {T}, T.

(** ** Tautologies *)

(** We'll fill in these first few together.  Any ideas for how to to
    prove something like this? *)

Definition id : forall A, A -> A
  := admit.

Definition modus_ponens : forall P Q, (P -> Q) -> P -> Q
  := admit.

(** N.B. [A -> (B -> C)] and [A -> B -> C] are the same; [->] associates to the right. *)

Definition first_argument : forall A B, A -> (B -> A)
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

(** Optional Homework Problems for More Practice *)

Definition second_argument : forall A B, A -> B -> B
  := admit.

Definition id_either : forall A, A -> A -> A
  := admit.

Definition third_argument : forall A B C, A -> B -> C -> C
  := admit.

(** This one is a bit different; one of the arguments has a [forall] *)
Definition explode : forall A B F, (forall C, F -> C) -> (A -> F) -> (A -> B)
  := admit.

(** Challenge Homework Problems *)

(** Come ask me about disjunction and negation during TAU if you are
    interested in playing with these. *)

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

(** Interesting question: Are all proofs of equality themselves equal?
    Keep this in the back of your mind as we define what equality is.
    To do this we need to define two notions of equality: judgmental,
    and propositional.  *)

(** Coq knows some things about equality.  If Coq judges that two
    things are equal (and equally trivially), then you can prove them
    (propositionally) equal by reflexivity, with [refl].  In this
    case, we say that they are also judgmentally equal.  For example:
    *)

(** Propositional equality is denoted as [x = y]. *)

(** Definition of judgmental equality, version 1: intuitively, [x] and
    [y] are judgmentally equal if there is a really stupid, trivial
    proof that [x = y]. *)

(** Definition of judgmental equality, version 2: [x] and [y] are
    judgmentally equal if (Coq says that) [refl] proves [x = y]. *)

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

Fail Definition addition_is_not_judgmentally_commutative : forall x y, x + y = y + x
  := fun x y => refl.

(** You can see the "normal form" of something with [Compute]: *)

Compute 1 + 1.

Compute 2 + 2.

Compute 2 * 3.

(** Definition of judgmental equality, version 3: [x] and [y] are
    judgmentally equal if [Compute] gives you the same normal form for
    [x] and [y].  N.B.  This is equivalent to what Coq is doing
    internally. *)

(** Note that equality is homogeneous; the things you're comparing for
    equality need to already have the same type.  You can ask if a
    statement is valid using [Check]: *)

Check 1. (* [1] is a number (a [nat]) *)

Check 1 = 1. (* [1 = 1] is a proposition (a [Prop]) *)

Check true. (* [true] is a boolean *)

Fail Check 1 = true. (* [1] is a [nat], and so isn't comparable to [true], which is a [bool] *)

(** A note on syntax *)
Definition id' : forall A, A -> A
  := admit.

Definition id'' : forall (A : Type), A -> A
  := admit.

Definition id''' : forall (A : Type) (pf : A), A
  := admit.

(** Pattern matching is case analysis, on things that are defined by
    cases (like, [bool], [nat]).  This is a technical meaning for
    "pattern matching" or "case analysis", namely, "using a [match
    ... with ... end] statement in Coq". *)

Definition is_positive : nat -> bool
  := admit.

Definition is_zero : nat -> bool
  := admit.

Definition If_Then_Else : forall (A : Type) (b : bool) (true_case : A) (false_case : A), A
  := admit.

(** [unit] is a type with one element. *)
Print unit.
(** But [refl] does not prove that all units are equal. *)
Fail Definition all_units_equal : forall x y : unit, x = y
  := fun x y => refl.
(** But we can pattern match *)
Definition all_units_equal : forall x y : unit, x = y
  := admit.

(** Optional Homework for More Practice *)

(** This should send [true] to [false], and [false] to [true]. *)
Definition boolean_negation : bool -> bool
  := admit.

(** This should implement the truth table for "and":
<<
  A B │ A ∧ B
  ────┼──────
  T T │   T
  T F │   F
  F T │   F
  F F │   F
>> *)

Definition boolean_conjunction : bool -> bool -> bool
  := admit.

(** This should implement the truth table for "or":
<<
  A B │ A ∨ B
  ────┼──────
  T T │   T
  T F │   T
  F T │   T
  F F │   F
>> *)

Definition boolean_disjunction : bool -> bool -> bool
  := admit.

(** This should implement the truth table for "xor":
<<
  A B │ A ⊕ B
  ────┼──────
  T T │   F
  T F │   T
  F T │   T
  F F │   F
>> *)

Definition boolean_exclusive_or : bool -> bool -> bool
  := admit.

(** This should implement the truth table for "implication":
<<
  A B │ A → B
  ────┼──────
  T T │   T
  T F │   F
  F T │   T
  F F │   T
>> *)

Definition boolean_implication : bool -> bool -> bool
  := admit.

(** This should implement the truth table for "biconditional":
<<
  A B │ A ↔ B
  ────┼──────
  T T │   T
  T F │   F
  F T │   F
  F F │   T
>> *)

Definition boolean_biconditional : bool -> bool -> bool
  := admit.



(** Recall: Are all proofs of equality themselves equal?  Here we
    define what equality is, i.e., how to use it. *)

(** We can prove the J-rule by pattern matching.  *)

(** We start off with the simpler version, called the "non-dependent"
    version. *)

Definition J_nondep : forall (A : Type) (x : A) (y : A)
                             (H : x = y)
                             (P : A -> Type),
                        P x -> P y
  := admit.

(** If you want to not always have to pass all of the arguments to [J]
    explicitly, you can uncomment the following lines, removing the <<
    and >>, to make [A], [x], and [y] be inferred automatically. *)
(**
<<
Arguments J_nondep {A} {x} {y} H P _.
>> *)

(** Recall the blackboard proof of symmetry, that [x = y -> y = x].
    Someone remind me how it goes. *)

(** First prove this by passing arguments to [J_nondep]. *)

Definition sym_J : forall A (x y : A), x = y -> y = x
  := admit.

Arguments sym_J {A x y} p, A x y p.

(** Now prove this by pattern matching. *)

Definition sym : forall A (x y : A), x = y -> y = x
  := admit.

(** We allow writing [sym p] to mean [sym _ _ _ p] *)

Arguments sym {A x y} p, A x y p.

(** First prove this by passing arguments to [J_nondep]. *)

Definition trans_J : forall A (x y z : A), x = y -> y = z -> x = z
  := admit.

Arguments trans_J {A x y z} p q, A x y z p q.

(** Now prove this by pattern matching. *)

Definition trans : forall A (x y z : A), x = y -> y = z -> x = z
  := admit.

Arguments trans {A x y z} p q, A x y z p q.

(** First prove this by passing arguments to [J_nondep]. *)

Definition ap_J : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := admit.

Arguments ap_J {A B} f {x y} p, {A B} f x y p, A B f x y p.

(** First prove this by pattern matching. *)

Definition ap : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := admit.

Arguments ap {A B} f {x y} p, {A B} f x y p, A B f x y p.

(** Now the version with more bells and whistles, again provable by
    pattern matching. *)

Definition J : forall (A : Type) (x : A) (y : A) (H : x = y)
                      (P : forall (y' : A) (H' : x = y'), Type),
                 P x refl -> P y H
  := admit.

(** [J] also has a computation rule, which holds judgmentally.  We
    start with the rule for [J_nondep]. *)

Definition J_nondep_computes
: forall (A : Type) (x : A)
         (P : A -> Type)
         (k : P x),
    J_nondep A x x refl P k = k
  := admit.

Definition J_computes
: forall (A : Type) (x : A)
         (P : forall (y' : A) (H' : x = y'), Type)
         (k : P x refl),
    J A x x refl P k = k
  := admit.

(** If you want to not always have to pass all of the arguments to [J]
    explicitly, you can uncomment the following lines, removing the <<
    and >>, to make [A], [x], and [y] be inferred automatically. *)
(**
<<
Arguments J {A} {x} {y} H P _.
Arguments J_computes {A x} P k.
Arguments J_non_computes {A x} P k.
>> *)


(** First prove this by passing arguments to [J]. *)

Definition trans_pV_J : forall A (x y : A) (p : x = y),
                          trans_J p (sym_J p) = refl
  := admit.

(** Now prove this by pattern matching. *)

Definition trans_pV : forall A (x y : A) (p : x = y),
                        trans p (sym p) = refl
  := admit.

(** Exercises to do individually, or with the people next to you. *)

(** First prove this by filling in arguments to [J] explicitly. *)

Definition sym_sym_J : forall A (x y : A) (p : x = y), sym_J (sym_J p) = p
  := admit.

Arguments sym_sym_J {A x y} p, A x y p.

(** Now prove this by pattern matching. *)

Definition sym_sym : forall A (x y : A) (p : x = y), sym (sym p) = p
  := admit.

Arguments sym_sym {A x y} p, A x y p.

Definition trans_1p_J : forall A (x y : A) (p : x = y), trans_J refl p = p
  := admit.

Definition trans_1p : forall A (x y : A) (p : x = y), trans refl p = p
  := admit.

Definition trans_p1_J : forall A (x y : A) (p : x = y), trans_J p refl = p
  := admit.

Definition trans_p1 : forall A (x y : A) (p : x = y), trans p refl = p
  := admit.

Definition sym_refl_J : forall A (x : A), sym_J (refl x) = refl x
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
  := forall A (x : A) (H : x = x) (P : x = x -> Type), P refl -> P H.

(** Prove that [K] implies uniqueness of identity proofs.  If you do
    this interactively with [refine], you may find it useful to
    [unfold K_rule_type in *] to see the definition of [K] in your
    goals window. *)

Definition K_implies_UIP : forall (K : K_rule_type),
                           forall A (x y : A) (p q : x = y), p = q
  := admit.

(** Note that it's impossible to prove [K] from [J].  See if you can get any insight into this by attempting to construct a proof. *)

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

    These are completely optional, and moderately challenging.  If you
    are interested, here are some problems that draw interesting
    connections between this material and category theory.

1. Can you find and prove a statement relating [sym_sym] to [sym_trans]?

2. Can you find and prove a statement relating [sym] to [trans_assoc]
   and [sym_trans] via [ap]?

3. The equality relation on a type forms a weak ω-groupoid (sometimes
   written as a weak ∞-groupoid).  This means that there is structure
   at every level.  The first few levels are given by [refl], [sym],
   and [trans] (level 1); [sym_sym], [sym_trans], [trans_assoc],
   [sym_refl], [trans_1p], [trans_p1], [trans_pV], and [trans_Vp]
   (level 2).  The theorem statements in general are known as the
   Stasheff polyhedra or Stasheff associahedra.  Can you discover more
   of these rules? *)
