(** * Exploring equality via homotopy and proof assistants - Day 3 - Equality in Coq *)
(** Note: You may use either the lab computers, or your laptop.  Coq may not be installed on the Windows computers, you should use the Macs.  If the Macs do not have CoqIDE installed, you can go to https://coq.inria.fr/coq-85, download CoqIDE_8.5beta2.dmg, open it, and run CoqIDE directly, without installing it.

  This file contains the exercises for Day 3, which are just the exercises for Day 2, with what we did yesterday filled in.  Some are explicitly marked as "Homework"; the rest can be done either in class or for homework.

  When doing exercises on your own, feel free to skip around; there are some interesting puzzles near the bottom (around [J_implies_UIP]).

  If you feel like you know exactly how a proof will go, but find it painful and tedious to write out the proof terms explicitly, come find me.  Coq has a lot of support for automation and taking care of things that are easy and verbose, so you don't have to. Proving should feel like a game.  If it doesn't, I can probably help you with that.

  N.B. There are many theorem provers out there, e.g., Agda, Idris, NuPRL, Otter, Twelf, Isabelle/HOL, Mizar, Metamath *)

(** The following are placeholders; [admit] indicates that something should be filled in later. *)
Axiom admit : forall {T}, T.
Axiom admit1 : forall {T}, T.
Axiom admit2 : forall {T}, T.
Axiom admit3 : forall {T}, T.

(** ** Tautologies *)

(** We'll fill in these first few together.  Any ideas for how to to prove something like this? *)

Definition id : forall A, A -> A
  := fun A pfA => pfA.

(** We can also write the colon on a line of its own; I set up this file in this way so that I can use a large font in my presentation. *)

Definition modus_ponens
: forall P Q, (P -> Q) -> P -> Q
  := fun P Q P_implies_Q pfP
       => P_implies_Q pfP.

(** N.B. [A -> (B -> C)] and [A -> B -> C] are the same; [->] associates to the right. *)

Definition first_argument
: forall A B, A -> (B -> A)
  := fun A B pfA pfB => pfA.

Definition first_argument'
: forall A B, A -> (B -> A)
  := fun A B pfA => (fun pfB => pfA).

Definition compose
: forall A B C,
    (A -> B) -> (B -> C) -> (A -> C)
  := fun A B C
         A_implies_B B_implies_C
         pfA
       => B_implies_C (A_implies_B pfA).

(** We can also fill in the functions bit by bit, as follows: *)

Definition compose'
: forall A B C,
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  refine (fun A B C => _).
  refine (fun A_implies_B B_implies_C => _).
  refine (fun pfA => _).
  refine (B_implies_C _).
  refine (A_implies_B _).
  refine pfA.
Defined.

(** These two are exercises to do individually or with the people sitting next to you. *)

Definition introduce_intermediate
: forall A B C,
    (A -> (B -> C))
    -> ((A -> B) -> (A -> C)).
Proof.
  refine (fun A B C A_implies_B_implies_C A_implies_B pfA => _).
  refine (A_implies_B_implies_C pfA _).
  refine (A_implies_B pfA).
Defined.

Definition swap_args
: forall A B C,
    (A -> B -> C) -> (B -> A -> C)
  := fun A B C A_implies_B_implies_C pfB pfA => A_implies_B_implies_C pfA pfB.

(** Optional Homework Problems for More Practice *)

Definition second_argument
: forall A B, A -> B -> B
  := fun A B pfA pfB => pfB.

Definition id_either
: forall A, A -> A -> A
  := fun A pfA pfA' => pfA.

Definition third_argument
: forall A B C, A -> B -> C -> C
  := fun A B C pfA pfB pfC => pfC.

(** This one is a bit different; one of the arguments has a [forall] *)
Definition explode
: forall A B F,
    (forall C, F -> C)
    -> (A -> F)
    -> (A -> B)
  := fun A B F explode_F A_implies_F pfA => explode_F B (A_implies_F pfA).

(** Challenge Homework Problems *)

(** Come ask me about disjunction and negation during TAU if you are interested in playing with these. *)

(** Prove that the Law of Excluded Middle implies Double Negation Elimination *)

Definition explode_false : forall P, False -> P
  := fun P absurdity => match absurdity with end.

Definition LEM_implies_DNE
: (forall P, P \/ ~P)
  -> (forall P, ~~P -> P).
Proof.
  refine (fun LEM P nnP => _).
  refine (match LEM P with
            | or_introl pfP => pfP
            | or_intror nP => _
          end).
  unfold not in *.
  refine (explode_false P _).
  refine (nnP nP).
Defined.

(** Prove that Double Negation Elimination implies Peirce's Law *)

Definition DNE_implies_Peirce
: (forall P, ~~P -> P)
  -> (forall P Q : Prop,
        ((P -> Q) -> P) -> P).
Proof.
  refine (fun DNE P Q P_implies_Q__implies_P => _).
  refine (DNE P _).
  refine (fun nP => _).
  refine (let pfP := P_implies_Q__implies_P _ in _).
  { refine (fun pfP => explode_false Q _).
    refine (nP pfP). }
  { refine (nP pfP). }
Defined.

(** Prove that Peirce's Law implies the Law of Excluded Middle *)

Definition Peirce_implies_LEM
: (forall P Q : Prop,
     ((P -> Q) -> P) -> P)
  -> (forall P, P \/ ~P).
Proof.
  refine (fun Peirce P => _).
  refine (Peirce (P \/ ~P) False _).
  refine (fun time_machine => _).
  refine (or_intror _).
  refine (fun pfP => _).
  refine (time_machine (or_introl pfP)).
Defined.

(** ** Judgmental equality. *)

About eq_refl.
About eq.
Print eq.

(** We allow writing [refl] for [eq_refl]. *)

Notation refl := eq_refl.

(** Interesting question: Are all proofs of equality themselves equal? Keep this in the back of your mind as we define what equality is. To do this we need to define two notions of equality: judgmental, and propositional.  *)

(** Coq knows some things about equality.  If Coq judges that two things are equal (and equally trivially), then you can prove them (propositionally) equal by reflexivity, with [refl].  In this case, we say that they are also judgmentally equal.  For example: *)

(** Propositional equality is denoted as [x = y]. *)

(** Definition of judgmental equality, version 1: intuitively, [x] and [y] are judgmentally equal if there is a really stupid, trivial proof that [x = y]. *)

(** Definition of judgmental equality, version 2: [x] and [y] are judgmentally equal if (Coq says that) [refl] proves [x = y]. *)

Definition one_plus_one_equals_two
: 1 + 1 = 2
  := refl.

Definition two_plus_two_equals_four
: 2 + 2 = 4
  := refl.

Definition two_times_three_equals_six
: 2 * 3 = 6
  := refl.

(** Just so that you don't think Coq believes everything is equal: *)

Fail Definition one_does_not_equal_zero
: 1 = 0
  := refl.

(** This gives
<<
The command has indeed failed with message:
=> Error: The term "refl" has type "?30 = ?30"
    while it is expected to have type "1 = 0".
>> *)

Fail Definition addition_is_not_judgmentally_commutative
: forall x y, x + y = y + x
  := fun x y => refl.

(** You can see the "normal form" of something with [Compute]: *)

Compute 1 + 1.

Compute 2 + 2.

Compute 2 * 3.

(** Definition of judgmental equality, version 3: [x] and [y] are judgmentally equal if [Compute] gives you the same normal form for [x] and [y].  N.B.  This is equivalent to what Coq is doing internally. *)

(** Note that equality is homogeneous; the things you're comparing for equality need to already have the same type.  You can ask if a statement is valid using [Check]: *)

Check 1. (* [1] is a number (a [nat]) *)

Check 1 = 1. (* [1 = 1] is a proposition (a [Prop]) *)

Check true. (* [true] is a boolean *)

Fail Check 1 = true. (* [1] is a [nat], and so isn't comparable to [true], which is a [bool] *)

(** A note on syntax *)
Definition id'
: forall A, A -> A
  := fun A pfA => pfA.

Definition id''
: forall (A : Type), A -> A
  := fun A pfA => pfA.

Definition id'''
: forall (A : Type) (pf : A), A
  := fun A pfA => pfA.

(** Pattern matching is case analysis, on things that are defined by cases (like, [bool], [nat]).  This is a technical meaning for "pattern matching" or "case analysis", namely, "using a [match ... with ... end] statement in Coq". *)

Definition is_positive : nat -> bool
  := fun n => match n with
               | 0 => false
               | _ => true
              end.

Definition is_zero : nat -> bool
  := fun n => match n with
               | 0 => true
               | _ => false
              end.

Compute is_zero 0.
Compute is_zero 1.
Compute is_positive 42.
Compute is_positive 20000.

Definition If_Then_Else
: forall (A : Type)
         (b : bool)
         (true_case : A)
         (false_case : A),
    A
  := fun _ b true_true_case false_case
       => match b with
               | true => true_true_case
               | false => false_case
              end.

Compute If_Then_Else nat true 6 7.

(** [unit] is a type with one element. *)
Print unit.
(** But [refl] does not prove that all units are equal. *)
Fail Definition all_units_equal
: forall x y : unit, x = y
  := fun x y => refl.
(** But we can pattern match *)
Definition all_units_equal : forall x y : unit, x = y.
Proof.
  refine (fun x y
          => match x with
               | tt => _
             end).
  refine (match y with
            | tt => _
          end).
  refine refl.
Defined.

(** Optional Homework for More Practice *)

(** This should send [true] to [false], and [false] to [true]. *)
Definition boolean_negation : bool -> bool
  := fun b => match b with
                | true => false
                | false => true
              end.

(** This should implement the truth table for "and":
<<
  A B │ A ∧ B
  ────┼──────
  T T │   T
  T F │   F
  F T │   F
  F F │   F
>> *)

Definition boolean_conjunction
: bool -> bool -> bool
  := fun A B => match A, B with
                  | true, true => true
                  | true, false => false
                  | false, true => false
                  | false, false => false
                end.

(** This should implement the truth table for "or":
<<
  A B │ A ∨ B
  ────┼──────
  T T │   T
  T F │   T
  F T │   T
  F F │   F
>> *)

Definition boolean_disjunction
: bool -> bool -> bool
  := fun A B => match A, B with
                  | true, true => true
                  | true, false => true
                  | false, true => true
                  | false, false => false
                end.

(** This should implement the truth table for "xor":
<<
  A B │ A ⊕ B
  ────┼──────
  T T │   F
  T F │   T
  F T │   T
  F F │   F
>> *)

Definition boolean_exclusive_or
: bool -> bool -> bool
  := fun A B => match A, B with
                  | true, true => false
                  | true, false => true
                  | false, true => true
                  | false, false => false
                end.

(** This should implement the truth table for "implication":
<<
  A B │ A → B
  ────┼──────
  T T │   T
  T F │   F
  F T │   T
  F F │   T
>> *)

Definition boolean_implication
: bool -> bool -> bool
  := fun A B => match A, B with
                  | true, true => true
                  | true, false => false
                  | false, true => true
                  | false, false => true
                end.

(** This should implement the truth table for "biconditional":
<<
  A B │ A ↔ B
  ────┼──────
  T T │   T
  T F │   F
  F T │   F
  F F │   T
>> *)

Definition boolean_biconditional
: bool -> bool -> bool
  := fun A B => match A, B with
                  | true, true => true
                  | true, false => false
                  | false, true => false
                  | false, false => true
                end.



(** Recall: Are all proofs of equality themselves equal?  Here we define what equality is, i.e., how to use it. *)

(** Defining equality:
1. There's a proof "by reflexivity" which proves x = x (for all x)
2. Given x, y, and a proof that x = y, to prove a property of y, it suffices to prove that property of x
 *)

(** We can prove the J-rule by pattern matching.  *)

(** We start off with the simpler version, called the "non-dependent" version. *)

(* A -> B is the same as forall (_ : A), B *)

Definition J_nondep
: forall (A : Type) (x : A) (y : A)
         (H : x = y)
         (P : A -> Type)
         (Px : P x),
      P y
  := fun A x y H P Px
       => match H with
           | refl => Px
          end.

(** If you want to not always have to pass all of the arguments to [J] explicitly, you can uncomment the following lines, removing the << and >>, to make [A], [x], and [y] be inferred automatically. *)
Arguments J_nondep {A} {x} {y} H P _.

(** Recall the blackboard proof of symmetry, that [x = y -> y = x]. Someone remind me how it goes. *)

(**
  * want y = x
    - suffices to prove x = x by J
             (property _ = x)
      * have x = x by reflexivity
*)

(** First prove this by passing arguments to [J_nondep]. *)

(**
These two types are equivalent:
<<
(x = y) -> ((y = z) -> (x = z))
(x = y /\ y = z) -> (x = z)
>>

There are two ways to write the inhabitants of this type:
<<
forall (x : A), B -> C
>>
Here are the ways:
<<
fun (x : A) => ((fun b => c) : B -> C)
fun (x : A) b => (c : C)
>>
*)

Definition sym_J
: forall A (x y : A), (x = y) -> (y = x)
  := fun A x y H
       => J_nondep H (fun y' => y' = x) (refl _).

Arguments sym_J {A x y} p, A x y p.

(** Now prove this by pattern matching. *)

Definition sym
: forall A (x y : A), x = y -> y = x
  := fun A x y H
       => match H with
           | refl => refl
          end.

Definition sym'
: forall A (x y : A), x = y -> y = x
  := fun A x y H
       => match H in (_ = y') return (y' = x) with
           | refl => refl
          end.

(** We allow writing [sym p] to mean [sym _ _ _ p] *)

Arguments sym {A x y} p, A x y p.

(** First prove this by passing arguments to [J_nondep]. *)

(**
Given x = y
Want: y = z -> x = z
(Property _ = z -> x = z)
Suffices to prove x = z -> x = z by J
  *)

Definition trans_J
: forall A (x y z : A),
    x = y -> y = z -> x = z.
Proof.
  refine (fun A x y z H => _).
  refine (J_nondep
           H
           (fun y' => y' = z -> x = z)
           _).
  refine (fun I => I).
Defined.

Arguments trans_J {A x y z} p q, A x y z p q.

(** Now prove this by pattern matching. *)

Definition trans
: forall A (x y z : A),
    x = y -> y = z -> x = z
  := fun A x y z H
     => match H with
          | refl => fun I => I
        end.

Arguments trans {A x y z} p q, A x y z p q.

(** First prove this by passing arguments to [J_nondep]. *)

Definition ap_J
: forall A B (f : A -> B) (x y : A),
    x = y -> f x = f y
  := fun A B f x y H
     => J_nondep H (fun y' => f x = f y') refl.

Arguments ap_J {A B} f {x y} p, {A B} f x y p, A B f x y p.

(** First prove this by pattern matching. *)

Definition ap
: forall A B (f : A -> B) (x y : A),
    x = y -> f x = f y
  := fun A B f x y H
     => match H with
          | refl => refl
        end.

Arguments ap {A B} f {x y} p, {A B} f x y p, A B f x y p.

(** Now the version with more bells and whistles, again provable by pattern matching. *)

(** Defining equality:
1. There's a proof "by reflexivity" which proves x = x (for all x)
2. Given x, y, and a proof _H_ that x = y, to prove a property of _y and H_, it suffices to prove that property of _x and "by reflexivity"_
 *)

Definition J
: forall
    (A : Type) (x : A) (y : A)
    (H : x = y)
    (P : forall (y' : A)
                (H' : x = y'),
           Type),
    P x refl -> P y H.
Proof.
  refine (fun A x y H P => _).
  refine (fun Pxrefl => _).
  refine (match H with
           | refl => Pxrefl
          end).
Defined.

(** [J] also has a computation rule, which holds judgmentally.  We start with the rule for [J_nondep]. *)

Definition J_nondep_computes
: forall (A : Type) (x : A)
         (P : A -> Type)
         (k : P x),
    J_nondep refl P k = k
  := fun A x P k => refl.

Eval compute in J_nondep refl.

Arguments J {A} {x} {y} H P _.

Definition J_computes
: forall (A : Type) (x : A)
         (P : forall (y' : A) (H' : x = y'), Type)
         (k : P x refl),
    J refl P k = k
  := fun A x P k => refl.

(** If you want to not always have to pass all of the arguments to [J] explicitly, you can uncomment the following lines, removing the << and >>, to make [A], [x], and [y] be inferred automatically. *)
Arguments J_computes {A x} P k.
Arguments J_nondep_computes {A x} P k.


(** First prove this by passing arguments to [J]. *)

Definition trans_pV_J
: forall A (x y : A) (H : x = y),
    trans_J H (sym_J H) = refl.
Proof.
  refine (fun A x y H => _).
  refine
   (J H
      (fun y' H'
        => (trans_J H' (sym_J H') = refl x))
      _).
  refine refl.
Defined.

(** Now prove this by pattern matching. *)

Definition trans_pV : forall A (x y : A) (p : x = y),
                        trans p (sym p) = refl.
Proof.
  refine (fun A x y H => _).
  refine
   (match H with
      | refl => _
    end).
  refine refl.
Defined.

(** Exercises to do individually, or with the people next to you. *)

(** First prove this by filling in arguments to [J] explicitly. *)

Definition sym_sym_J
: forall A (x y : A) (H : x = y),
    sym_J (sym_J H) = H
  := fun A x y H => J H (fun y' H' => sym_J (sym_J H') = H') refl.

Arguments sym_sym_J {A x y} H, A x y H.

(** Now prove this by pattern matching. *)

Definition sym_sym
: forall A (x y : A) (H : x = y),
    sym (sym H) = H
  := fun A x y H => match H with refl => refl end.

Arguments sym_sym {A x y} H, A x y H.

Definition trans_1p_J
: forall A (x y : A) (H : x = y),
    trans_J refl H = H
  := fun A x y H => J H (fun y' H' => trans_J refl H' = H') refl.

Definition trans_1p
: forall A (x y : A) (H : x = y),
    trans refl H = H
  := fun A x y H => match H with refl => refl end.

Definition trans_p1_J
: forall A (x y : A) (H : x = y),
    trans_J H refl = H
  := fun A x y H => J H (fun y' H' => trans_J H' refl = H') refl.

Definition trans_p1
: forall A (x y : A) (H : x = y),
    trans H refl = H
  := fun A x y H => match H with refl => refl end.

Definition sym_refl_J
: forall A (x : A),
    sym_J (refl x) = refl x
  := fun A x => refl.

Definition sym_refl
: forall A (x : A),
    sym (refl x) = refl x
  := fun A x => refl.

(** Recall the informal proof from yesterday's homework, which "proved" that all proofs of [x = y] are themselves equal:

  The [J] rule says informally that if you have a proof [p] of [x = y], it suffices to assume that [y] _is_ [x] (to substitute [x] for [y] in what you are trying to prove), and to assume that [p] is [refl x] (to substitute [refl x] for [p] in what you are trying to prove).  Suppose we have a type [A], two inhabitants [x] and [y] of type [A], and two proofs [p] and [q] that [x = y].  By [J], it suffices to assume that [y] is [x], that [p] is [refl x], and hence it suffices to prove that [refl x = q], where [q] now has type [x = x].  To prove this, again by [J], it suffices to assume that [x] is [x] (it already is) and that [q] is [refl x], and hence it suffices to prove [refl x = refl x].  We can prove this by [refl (refl x)].  Thus for any proofs [p] and [q] that [x = y], we have [p = q].  Qed.

  Try to formalize this proof in Coq, and see what goes wrong.  It may help to use [refine] so that you can construct the proof sentence by sentence.  If you are having trouble figuring out how to instantiate [J] for a proof of equality [H : x = y], you can ask Coq to figure it out for you by running [destruct H.].  You can see what it did by typing [Show Proof.] afterwards. *)

Definition J_implies_UIP
: forall A (x y : A) (H0 H1 : x = y), H0 = H1.
Proof.
  (** Suppose we have a type [A], two inhabitants [x] and [y] of type [A], and two proofs [p] and [q] that [x = y]. *)
  refine (fun A x y p => _).
  (** By [J], it suffices to assume that [y] is [x], that [p] is [refl x], and hence it suffices to prove that [refl x = q], where [q] now has type [x = x]. *)
  refine (J p (fun y' p' => forall q : x = y', p' = q) _).
  refine (fun q => _).
  (* To prove this, again by [J], it suffices to assume that [x] is [x] (it already is) and that [q] is [refl x], and hence it suffices to prove [refl x = refl x].  We can prove this by [refl (refl x)]. *)
  Fail refine (J q (fun y' q' => refl = q') _).
  refine admit.
Abort.

(** The rest of these are explicitly Homework; feel free to take a break now, or to keep going. *)

(** Recall from yesterday's homework that the [K] rule says: *)

Definition K_rule_type
  := forall A (x : A) (H : x = x) (P : x = x -> Type), P refl -> P H.

(** Prove that [K] implies uniqueness of identity proofs.  If you do this interactively with [refine], you may find it useful to [unfold K_rule_type in *] to see the definition of [K] in your goals window. *)

Definition K_implies_UIP
: forall (K : K_rule_type) A (x y : A) (H0 H1 : x = y), H0 = H1.
Proof.
  refine (fun K A x y H0 => _).
  unfold K_rule_type in *.
  refine (J H0 (fun y' H0' => forall H1, H0' = H1) _).
  refine (fun H1 => _).
  refine (K _ _ H1 (fun H1' => refl = H1') refl).
Defined.

(** Note that it's impossible to prove [K] from [J].  See if you can get any insight into this by attempting to construct a proof.

  Hint: Think about what these things (and UIP) mean in the paths interpretation of equality, and remember that _all_ of our functions are continuous. *)

Definition J_implies_K : K_rule_type
  := admit.

(** Can you write down three "different" proofs of transitivity (they should all be judgmentally different; [refl] should not prove any two of them the same. *)

Definition trans1
: forall A (x y z : A),
    x = y -> y = z -> x = z.
Proof.
  intros A x y z p q.
  destruct p.
  exact q.
Defined.
Definition trans2
: forall A (x y z : A),
    x = y -> y = z -> x = z.
Proof.
  intros A x y z p q.
  destruct p, q.
  exact refl.
Defined.
Definition trans3
: forall A (x y z : A),
    x = y -> y = z -> x = z.
Proof.
  intros A x y z p q.
  destruct q.
  exact p.
Defined.

(** Now we have Coq check that they are not the same; these lines should compile unmodified. *)

Fail Check refl : trans1 = trans2.

Fail Check refl : trans2 = trans3.

Fail Check refl : trans1 = trans3.

(** Now prove that these are all equal (propositionally, but not judgmentally. *)

Definition trans_12
: forall A (x y z : A) (H0 : x = y) (H1 : y = z),
    trans1 A x y z H0 H1 = trans2 A x y z H0 H1.
Proof.
  intros A x y z H0 H1.
  destruct H0, H1.
  refine refl.
Defined.
Definition trans_23
: forall A (x y z : A) (H0 : x = y) (H1 : y = z),
    trans2 A x y z H0 H1 = trans3 A x y z H0 H1.
Proof.
  intros A x y z H0 H1.
  destruct H0, H1.
  refine refl.
Defined.

(** We can also prove associativity. *)

Definition trans_assoc
: forall A (x y z w : A) (H0 : x = y) (H1 : y = z) (H2 : z = w),
    trans H0 (trans H1 H2) = trans (trans H0 H1) H2.
Proof.
  intros A x y z w H0 H1 H2.
  destruct H0, H1, H2.
  refine refl.
Defined.

Definition trans_Vp
: forall A (x y : A) (H : x = y),
    trans (sym H) H = refl.
Proof.
  refine (fun A x y H => _).
  refine
   (match H with
      | refl => _
    end).
  refine refl.
Defined.

Definition trans_sym
: forall A (x y z : A) (H0 : x = y) (H1 : y = z),
    sym (trans H0 H1) = trans (sym H1) (sym H0).
Proof.
  intros A x y z H0 H1.
  destruct H0, H1.
  refine refl.
Defined.

(** *** Category theory *)

(** Those of you familiar with category theory might find the following properties interesting. *)

(** All exercises in this section are optional homework. *)

(** We can look at [ap] as describing the action on morphisms (equality proofs) of any function; the type of morphisms from [x : A] to [y : A] is the type [x = y]; the action of [f : A -> B] on a morphism [m : x = y] is [ap f m : f x = f y].  We can prove the relevant functoriality properties. *)

(** Action on identity: *)

Definition ap_refl
: forall {A B} (f : A -> B) x,
    ap f (refl x) = refl (f x)
  := fun A B f x => refl.

(** Action on composition: *)

Definition ap_trans
: forall {A B} (f : A -> B) {x y z : A}
         (H0 : x = y) (H1 : y = z),
    ap f (trans H0 H1) = trans (ap f H0) (ap f H1).
Proof.
  intros A B f x y z H0 H1.
  destruct H0, H1.
  refine refl.
Defined.

(** Action on inverses (additional rule for groupoids): *)

Definition ap_sym
: forall {A B} (f : A -> B) {x y : A}
         (H : x = y),
    ap f (sym H) = sym (ap f H).
Proof.
  intros A B f x y H.
  destruct H.
  refine refl.
Defined.

(** Furthermore, every function that specifies the action of a natural transformation on objects is automatically natural: *)

Definition concat_Ap
: forall {A B} (f g : A -> B)
         (T : forall x, f x = g x),
    forall {x y : A} (m : x = y),
      trans (ap f m) (T y) = trans (T x) (ap g m).
Proof.
  intros A B f g T x y m.
  destruct m; simpl.
  case (T x).
  refine refl.
Defined.

(** *** Further exploration:

    These are completely optional, and moderately challenging.  If you are interested, here are some problems that draw interesting connections between this material and category theory.

1. Can you find and prove a statement relating [sym_sym] to [sym_trans]?

2. Can you find and prove a statement relating [sym] to [trans_assoc] and [sym_trans] via [ap]?

3. The equality relation on a type forms a weak ω-groupoid (sometimes written as a weak ∞-groupoid).  This means that there is structure at every level.  The first few levels are given by [refl], [sym], and [trans] (level 1); [sym_sym], [sym_trans], [trans_assoc], [sym_refl], [trans_1p], [trans_p1], [trans_pV], and [trans_Vp] (level 2).  The theorem statements in general are known as the Stasheff polyhedra or Stasheff associahedra.  Can you discover more of these rules? *)
