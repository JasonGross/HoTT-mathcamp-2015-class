(** * Exploring equality via homotopy and proof assistants - Day 3 - Inductive types and their equalities *)
(** This file contains the exercises for Day 3.  Some are explicitly marked as "Homework"; the rest can be done either in class or for homework.

  If the Macs in the computer lab do not have CoqIDE installed, you can go to https://coq.inria.fr/coq-85, download CoqIDE_8.5beta2.dmg, open it, and run CoqIDE directly, without installing it.

  When doing exercises on your own, feel free to skip around; there are some interesting puzzles near the bottom.

  If you feel like you know exactly how a proof will go, but find it painful and tedious to write out the proof terms explicitly, come find me.  Coq has a lot of support for automation and taking care of things that are easy and verbose, so you don't have to. Proving should feel like a game.  If it doesn't, I can probably help you with that.  *)

(** The following are placeholders; [admit] indicates that something should be filled in later. *)

Axiom admit : forall {T}, T.

(** Compatibility between Coq 8.5 and 8.4 *)

Set Asymmetric Patterns.

(* begin hide *)
(** Some filled in exercises from yesterday; feel free to paste more here. *)

Notation refl := eq_refl.
Definition sym : forall A (x y : A), x = y -> y = x := eq_sym.
(** We allow writing [sym p] to mean [sym _ _ _ p] *)
Arguments sym {A x y} p, A x y p.
Definition trans : forall A (x y z : A), x = y -> y = z -> x = z
  := eq_trans.
Arguments trans {A x y z} p q, A x y z p q.
Definition J : forall (A : Type) (x : A) (y : A)
                      (H : x = y)
                      (P : forall (y' : A) (H' : x = y'), Type),
                 P x refl -> P y H
  := fun A x y H P k => match H with
                          | refl => k
                        end.
Arguments J {A} {x} {y} H P _.
Definition ap : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := fun A B f x y p
     => match p with
          | refl => refl
        end.

Arguments ap {A B} f {x y} p, {A B} f x y p, A B f x y p.


(* end hide *)

(** ** Guiding Puzzles *)

(** There are three guiding questions for today:

 1. What are (inductive) types?
 2. What does it mean to say that two inhabitants of a given type are equal?
 3. Where is equality under-specified, and how can we extend the patterns we see to fill in these areas? *)

(** *** Puzzle 1: contractibility of based path spaces *)

(** We use the notation [{ x : T | P x }] to denote the type of pairs [(x; p)] which consist of an inhabitant [x : T] and a proof [p : P x]. *)

Notation "{ x  |  P }" := ({ x : _ & P }) : type_scope.
Notation "{ x : A  |  P }" := ({ x : A & P }) : type_scope.
Notation "( x ; p )" := (existT _ x p).

(** A type is called contractible if there is a (continuous!) function showing that all inhabitants are equal to a particular one. *)

Definition is_contractible : Type -> Type
  := fun A => { center : A | forall y : A, center = y }.

(** Puzzle: The following theorem is provable.  Prove it. *)

Definition contractible_pointed
: forall (A : Type) (y : A),
    is_contractible { x : A | y = x }
  := admit.

(** Note that [x = y :> T] means [x : T], [y : T], and [x = y].  It is the notation for [@eq T x y].  It is how we write $x =_T y$ #<span class="inlinecode">x =<sub>T</sub> y</span># in Coq. *)

(** Since equals are inter-substitutable, we should be able to prove: *)

Definition contractible_to_UIP
: forall (A : Type) (y : A)
         (x : A)
         (p p' : y = x),
    ((x; p) = (x; p') :> { x : A | y = x })
    -> p = p'
  := admit.

(** But it turns out that we can't prove this.  Why not?  Give both a formal, type theoretic reason (what terms don't typecheck?), and a topological reason. *)

(** *** Puzzle 2: understanding the encode-decode method *)

(** Here is a concrete puzzle for the second question:

  To classify the equality of a given type, we give a "code" for each pair of elements.  We must say how to "encode" equality proofs, and how to "decode" codes into equality proofs.  We want this to be an isomorphism, i.e., [encode ∘ decode] and [decode ∘ encode] should both be the identity function.  It turns out that we don't need to know anything about [encode] or [decode] other than their existance to ensure this; we can always adjust [decode] to create an inverse to [encode], as long as a particular property holds of [code].  What is that property?

  More concretely, the puzzle is to fill in the following holes. *)

Section general_classification.

  Definition code_correct_P
  : forall {A : Type} (code : A -> A -> Type), Type
    := admit.

  (** We assume we are given a type, a [code], an [encode], and a [decode].  We introduce the assumptions as we get to definitions that should need them. *)

  Context {A : Type} (code : A -> A -> Type)
          (decode' : forall x y, code x y -> x = y).

  Definition decode
  : forall {x y}, code x y -> x = y
    := admit.

  Context (encode : forall x y, x = y -> code x y).

  Definition deencode
  : forall {x y} (p : x = y),
      decode (encode _ _ p) = p
    := admit.

  (** For this last one, we'll need the correctness property on codes. *)

  Context (code_correct : code_correct_P code).

  Definition endecode
  : forall {x y} (p : code x y),
      encode _ _ (decode p) = p
    := admit.

End general_classification.

(** The following sanity check on the classification should be provable: *)

Section sanity_checks.

  (** [x = y] should be a valid code *)

  Definition eq_is_valid_code
  : forall {A : Type},
      code_correct_P (fun x y : A => x = y)
    := admit.

  (** If you didn't choose a silly correctness property like [code = (fun x y => x = y)], then your proof should generalize to the following: *)

  (** Suppose we are given a valid encoding. *)

  Context {A : Type} (code : A -> A -> Type)
          (encode : forall x y, x = y -> code x y)
          (decode : forall x y, code x y -> x = y)
          (endecode : forall x y (p : code x y), encode _ _ (decode _ _ p) = p)
          (deencode : forall x y (p : x = y), decode _ _ (encode _ _ p) = p).

  (** Then it should satisfy your validity principle. *)

  Definition valid_code_is_valid : code_correct_P code
    := admit.

End sanity_checks.

(** *** Puzzle 3 *)

(** Classify the equalities of types.  That is, fill in the following: *)

Definition Type_code
: forall (x y : Type), Type
  := admit.

Definition Type_encode
: forall {x y : Type}, x = y -> Type_code x y
  := admit.

(** The following are unprovable in Coq, currently.  They are collectively known as the "univalence axiom". *)

Axiom Type_decode
: forall {x y : Type}, Type_code x y -> x = y.
Axiom Type_endecode
: forall {x y : Type} (p : Type_code x y),
    Type_encode (Type_decode p) = p.
Axiom Type_deencode
: forall {x y : Type} (p : x = y),
    Type_decode (Type_encode p) = p.

(** This was all very abstract.  Let's drill down with some exmples. *)

(** ** Inductive Types *)

(** First, we must understand the types which we are classifying the path-spaces of. *)

(** An inductive type is specified by introduction and elimination rules; introduction rules tell you how to create inhabitants (elements) of a type, and elimination rules tell you how to use such inhabitants.  Coq generate eliminations rules automatically, but we will try to come up with the first few without peeking. *)

Inductive unit : Set := tt.

(** Coq has special syntax for [nat], so we don't overwrite it. *)

(** Inductive nat' : Type := ... *)

(** Inductive Empty_set : Type := ... *)

(** Anecdote: Proving [unit -> Empty_set] (i.e., [True -> False]) by recursion on [unit], if we assume that [True = (False -> False)] *)

(** Any that we don't do in class are homework *)

Inductive bool : Type := true | false.

(** A notational helper. *)

Add Printing If bool.

(** Inductive prod (A B : Type) : Type := ... *)

(** Some notational helpers *)

(**
<<
Arguments pair {A B} _ _.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Example prod_1 := (1, 1) : nat * nat.
Example prod_2 := (1, 2) : nat * nat.
Example prod_3 := (true, true) : bool * bool.
Example prod_4 := (1, true) : nat * bool.

(** We use curlie braces so that we don't have to pass the arguments explicitly all the time. *)

Definition fst
: forall {A B}, A * B -> A
:= admit.

Definition snd
: forall {A B}, A * B -> B
:= admit.

>> *)

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

(** Inductive sum (A B : Type) : Type := ... *)

(** Notational helpers *)

(**
<<
Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.
>> *)

Example sum_1 := inl tt : unit + nat.
Example sum_2 := inr 0 : unit + nat.

(** Inductive sigT A (B : A -> Type) : Type := ... *)

(** Notational helpers *)

(**
<<
Arguments sigT {A} B.
Arguments existT {A} B _ _.
Notation "{ a : A  & B }" := (sigT (A:=A) (fun a => B)) : type_scope.
>> *)

Notation "{ a  |  B }" := ({ a : _ & B }) : type_scope.
Notation "{ a : A  |  B }" := ({ a : A & B }) : type_scope.
Notation "( a ; b )" := (existT _ a b).

Example non_dependent_pair_1 :=
  (true; 0) : sigT (fun a : bool => nat).
Example non_dependent_pair_2 :=
  (true; 1) : { a : bool | nat }.
Example non_dependent_pair_3 :=
  (false; 1) : { a : bool | nat }.
Example dependent_pair_1 :=
  (true; 1) : { a : bool | if a then nat else unit }.
Example dependent_pair_2 :=
  (true; 0) : { a : bool | if a then nat else unit }.
Example dependent_pair_3 :=
  (false; tt) : { a : bool | if a then nat else unit }.
Fail Example dependent_pair_4 :=
  (false; 0) : { a : bool | if a then nat else unit }.

(** The projections *)

(**
<<
Definition projT1
: forall {A B}, { a : A | B a } -> A
  := admit.

Definition projT2
: forall {A B} (x : { a : A | B a}), B (projT1 x)
  := admit.
>> *)

(** Notational helpers for the projections *)

Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

(** Inductive option (A : Type) : Type := ... *)

(** Inductive list (A : Type) : Type := ... *)

(** Function types also have intro and elim rules, though they don't have syntactic forms.  Can you describe them? *)

(** Note well: [J] is the eliminator for the equality type. *)

(** *** Provable equalities *)

(** What equalities of types are provable? *)


Definition some_type_equality : unit = unit
  := refl.

Inductive unit1 : Type := tt1.
Inductive unit2 : Type := tt2.

Fail Definition unit1_equals_unit2 : unit1 = unit2
  := refl.



(** Can you prove other ones? *)

(** *** Provable inequalities *)

(** What equalities of types are provably absurd? *)

Definition unit_ne_empty_set
 : unit = Empty_set -> Empty_set.
Proof.
  refine (fun P => _).
  refine (J P (fun x _ => x) _).
  refine tt.
Defined.

Definition true_ne_false
: true = false -> Empty_set.
Proof.
  refine (fun P => _).
  refine (J P (fun f _ => if f then unit else Empty_set) _).
  refine tt.
Defined.

Definition unit_ne_bool
 : bool = unit -> Empty_set.
Proof.
  refine (fun P => _).
  refine (let alleq : forall x y : unit, x = y := _ in _).
  { intros [] [].
    refine refl. }
  refine (J P (fun T _ => (forall x y : T, x = y) -> Empty_set) _ alleq).
  refine (fun alleq_bool => _).
  refine (true_ne_false (alleq_bool true false)).
Defined.


















































(** *** Isomorphisms *)

(** We can define a notion of isomorphism: *)

Class IsIsomorphism {A B} (f : A -> B)
  := { iso_inv : B -> A;
       right_inv : forall x : B, f (iso_inv x) = x;
       left_inv : forall x : A, iso_inv (f x) = x }.

Arguments iso_inv {A B} f {_} _.
Arguments right_inv {A B f _ _}, {A B} f {_} _.
Arguments left_inv {A B f _ _}, {A B} f {_} _.

Record Isomorphic A B
  := { iso_fun : A -> B;
       iso_isiso : IsIsomorphism iso_fun }.

Arguments iso_fun {A B} _ _.

(** Let us use an object of type [Isomorphic] as a function: *)

Coercion iso_fun : Isomorphic >-> Funclass.

(** Tell Coq that the function associated to an [Isomorphic] object is always an isomorphism. *)

Existing Instance iso_isiso.

Notation "A <~=~> B" := (Isomorphic A B) (at level 70).
Notation "A ≅ B" := (Isomorphic A B) (at level 70).

(** We can prove the standard properties about isomorphisms: *)

Definition Isomorphic_refl : forall {A}, A ≅ A
  := admit.

Definition Isomorphic_inverse : forall {A B}, A ≅ B -> B ≅ A
  := admit.

Definition Isomorphic_compose : forall {A B C}, A ≅ B -> B ≅ C -> A ≅ C
  := admit.

(** We would like to prove the last corresponding law: *)

Definition Isomorphic_ap : forall (f : Type -> Type) {A B}, A ≅ B -> f A ≅ f B
  := admit.

(** But it's not provable!  Here's a counter-example: *)

(** Recall the taboo from earlier; we can't prove equality of two identical types defined separately.  But if we could prove [Isomorphic_ap], then we could prove this! *)

Definition iso_unit2_unit1 : unit2 ≅ unit1
  := admit.

Definition taboo1 : unit1 = unit2 :> Type
  := Isomorphic_ap (fun T => T = unit2) iso_unit2_unit1 refl.

(** Ooops!  We'll be coming back to this soon. *)

(** More practice: You can prove the higher groupoid laws about isomorphisms, but it's a bit of a pain. *)

(** Before dealing with the taboo above, let's classify the equality space of isomorphisms. *)

(** ** Equality classification *)

(** We can classify the equality types.  For each type, we come up with a simpler type that represents ("codes for") its equality type.  Then we prove that this type is isomorphic to the given equality type.  The exercises here are all to help understand how the encode-decode method works, to build up to function extensionality and univalence, and, for sigma types, to solve the first puzzle.  We'll do them as needed to explain the method; the rest are (optional) homework.  There are more exercises at the bottom of the file. *)

(** *** [unit] *)

Definition unit_code : forall (x y : unit), Type
  := admit.

(** We use curlie braces to not have to pass the [x] and [y] around all the time. *)

Definition unit_encode : forall {x y : unit}, x = y -> unit_code x y
  := admit.

Definition unit_decode : forall {x y : unit}, unit_code x y -> x = y
  := admit.

Definition unit_endecode : forall {x y} (p : unit_code x y),
                             unit_encode (unit_decode p) = p
  := admit.

Definition unit_deencode : forall {x y} (p : x = y),
                             unit_decode (unit_encode p) = p
  := admit.


Definition unit_iso : forall x y : unit, (x = y) ≅ unit_code x y
  := admit.

(** *** [bool] *)

Definition bool_code : forall (x y : bool), Type
  := admit.

Definition bool_encode : forall {x y : bool}, x = y -> bool_code x y
  := admit.

Definition bool_decode : forall {x y : bool}, bool_code x y -> x = y
  := admit.

Definition bool_endecode : forall {x y : bool} (p : bool_code x y),
                             bool_encode (bool_decode p) = p
  := admit.

Definition bool_deencode : forall {x y : bool} (p : x = y),
                             bool_decode (bool_encode p) = p
  := admit.


(** *** [Empty_set] *)

Definition Empty_set_code : forall (x y : Empty_set), Type
  := admit.

Definition Empty_set_encode : forall {x y : Empty_set},
                                x = y -> Empty_set_code x y
  := admit.

Definition Empty_set_decode : forall {x y : Empty_set},
                                Empty_set_code x y -> x = y
  := admit.

Definition Empty_set_endecode : forall {x y : Empty_set} (p : Empty_set_code x y),
                                  Empty_set_encode (Empty_set_decode p) = p
  := admit.

Definition Empty_set_deencode : forall {x y : Empty_set} (p : x = y),
                                  Empty_set_decode (Empty_set_encode p) = p
  := admit.


(** *** arrow types *)

Definition arrow_code : forall {A B} (f g : A -> B), Type
  := admit.

Definition arrow_encode : forall {A B} {f g : A -> B}, f = g -> arrow_code f g
  := admit.

(** The rest aren't currently provable in Coq; it's the axiom of functional extensionality. *)

Axiom arrow_decode : forall {A B} {f g : A -> B}, arrow_code f g -> f = g.
Axiom arrow_endecode : forall {A B} {f g : A -> B} (p : arrow_code f g),
                         arrow_encode (arrow_decode p) = p.
Axiom arrow_deencode : forall {A B} {f g : A -> B} (p : f = g),
                         arrow_decode (arrow_encode p) = p.

(** *** Pi types (dependent function types) *)

Definition function_code : forall {A B} (f g : forall a : A, B a), Type
  := fun A B f g => forall a, f a = g a.

Definition function_encode : forall {A B} {f g : forall a : A, B a}, f = g -> function_code f g
  := fun A B f g H
       => match H with
           | refl => fun a => refl (f a)
          end.

(** The rest aren't currently provable in Coq; it's the axiom of functional extensionality. *)

Axiom function_decode : forall {A B} {f g : forall a : A, B a}, function_code f g -> f = g.
Axiom function_endecode : forall {A B} {f g : forall a : A, B a} (p : function_code f g),
                            function_encode (function_decode p) = p.
Axiom function_deencode : forall {A B} {f g : forall a : A, B a} (p : f = g),
                            function_decode (function_encode p) = p.



(** *** [sigma] (dependent pairs) *)

(** Homework *)

Definition sigma_code : forall {A B} (x y : { a : A | B a }), Type
  := admit.

Definition sigma_encode : forall {A B} {x y : { a : A | B a }}, x = y -> sigma_code x y
  := admit.

Definition sigma_decode : forall {A B} {x y : { a : A | B a }}, sigma_code x y -> x = y
  := admit.

Definition sigma_endecode : forall {A B} {x y : { a : A | B a }} (p : sigma_code x y),
                             sigma_encode (sigma_decode p) = p
  := admit.

Definition sigma_deencode : forall {A B} {x y : { a : A | B a }} (p : x = y),
                             sigma_decode (sigma_encode p) = p
  := admit.


(** Back to isomorphisms. *)

Definition iso_code : forall {A B} (x y : A ≅ B), Type
  := fun A B x y => (x : A -> B) = (y : A -> B).

Definition iso_encode : forall {A B} {x y : A ≅ B}, x = y -> iso_code x y
  := fun A B x y H => match H with
                       | refl => refl
                      end.

Definition iso_decode : forall {A B} {x y : A ≅ B}, iso_code x y -> x = y
  := admit.

Definition iso_endecode : forall {A B} {x y : A ≅ B} (p : iso_code x y),
                            iso_encode (iso_decode p) = p
  := admit.

Definition iso_deencode : forall {A B} {x y : A ≅ B} (p : x = y),
                            iso_decode (iso_encode p) = p
  := admit.

(** Ooops.  Turns out this isn't provable.  Challenge: Figure out why. *)

(** *** Equivalences *)

(** We can define a slight variation on isomorphisms, called "contractible fibers", which generalizes the notion of injective+surjective.  If you're interested in the various ways of formulating equivalences, Chapter 4 of the HoTT Book (http://homotopytypetheory.org/book/) is an excellent resource. *)

Class Contr (A : Type)
  := { center : A;
       contr : forall y, center = y }.

Arguments center A {_}.

Class IsEquiv {A B} (f : A -> B)
  := Build_IsEquiv : forall b, Contr { a : A | f a = b }.

Record Equiv A B
  := { equiv_fun : A -> B;
       equiv_isequiv : IsEquiv equiv_fun }.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _ _.

(** Let us use an object of type [Equiv] as a function: *)

Coercion equiv_fun : Equiv >-> Funclass.

(** Tell Coq that the function associated to an [Equiv] object is
    always an equivalence. *)

Existing Instance equiv_isequiv.

Notation "A <~> B" := (Equiv A B) (at level 70).
Notation "A ≃ B" := (Equiv A B) (at level 70).

(** We can prove that an equivalence gives us an isomorphism very easily. *)

Definition iso_of_equiv : forall {A B}, A ≃ B -> A ≅ B.
Proof.
  refine admit.
Defined.

(** We can go the other way with more work. *)

(** Optional Homework: Complete this proof. *)

Definition equiv_of_iso : forall {A B}, A ≅ B -> A ≃ B.
Proof.
  refine admit.
Defined.

(** Now, we prove the following helper lemma, which lets us get the right codes for [Equiv].  We again assume functional extensionality. *)

Definition allpath_contr : forall {A} (x y : Contr A), x = y.
Proof.
  refine admit.
Defined.

Definition allpath_isequiv : forall {A B} (f : A -> B) (e1 e2 : IsEquiv f), e1 = e2.
Proof.
  refine admit.
Defined.

Definition equiv_code : forall {A B} (f g : A ≃ B), Type
  := admit.

Definition equiv_encode : forall {A B} {f g : A ≃ B}, f = g -> equiv_code f g
  := admit.

Definition equiv_decode : forall {A B} {f g : A ≃ B}, equiv_code f g -> f = g
  := admit.

Definition equiv_endecode : forall {A B} {f g : A ≃ B} (p : equiv_code f g),
                              equiv_encode (equiv_decode p) = p
  := admit.

Definition equiv_deencode : forall {A B} {f g : A ≃ B} (p : f = g),
                              equiv_decode (equiv_encode p) = p
  := admit.

(** Now that we have a "good" type of isomorphism/equivalence (one with the right equality type), we can go back to the question of [Isomorphic_ap]; Recall that we want to prove:

<<
Definition Isomorphic_ap : forall (f : Type -> Type) {A B}, A ≅ B -> f A ≅ f B.
>> *)

(** We can prove this by axiomatizing the codes for types: *)

Definition Type_code' : forall (x y : Type), Type
  := fun x y => x ≃ y.

Definition Type_encode' : forall {x y : Type}, x = y -> Type_code' x y
  := admit.

(** The following are unprovable in Coq, currently.  They are collectively known as the "univalence axiom". *)

Axiom Type_decode' : forall {x y : Type}, Type_code' x y -> x = y.
Axiom Type_endecode' : forall {x y : Type} (p : Type_code' x y),
                         Type_encode' (Type_decode' p) = p.
Axiom Type_deencode' : forall {x y : Type} (p : x = y),
                         Type_decode' (Type_encode' p) = p.

Definition Univalence : forall {x y : Type}, IsEquiv (@Type_encode' x y)
  := admit.

(** *** Homework: Playing with univalence *)

(** Using univalence, we can prove some things. *)

Definition Empty_set_eq : (Empty_set = Empty_set) = unit :> Type
  := admit.

Definition unit_eq : (unit = unit) = unit :> Type
  := admit.

Definition bool_eq : (bool = bool) = bool :> Type
  := admit.

Definition bool_arrow_bool_eq : (bool -> bool) = (bool * bool)%type
  := admit.

Definition prod_commutes : forall (A B : Type), (A * B = B * A)%type
  := admit.

(** Challenge: Show, without axioms, that univalence implies functional extensionality: *)

Definition univalence_implies_funext
: (forall A B, IsEquiv (@Type_encode' A B))
  -> (forall A B (f g : forall a : A, B a), (forall a, f a = g a) -> f = g)
  := admit.

(** Exercise 2.17 from the HoTT Book (http://homotopytypetheory.org/book/ - don't worry about reading the book):

  Show that if [A ≃ A'] and [B ≃ B'], then [(A * B) ≃ (A' * B')] in two ways: once using univalence, and once without assuming it. *)

Definition equiv_functor_prod_univalence
: (forall A B, IsEquiv (@Type_encode A B))
  -> forall A A' B B',
       A ≃ A' -> B ≃ B' -> (A * B ≃ A' * B')%type
  := admit.

Definition equiv_functor_prod_no_univalence
: forall A A' B B',
    A ≃ A' -> B ≃ B' -> (A * B ≃ A' * B')%type
  := admit.

(** Now prove that these two ways are equal *)

Definition equiv_functor_prod_eq
: forall univalence,
    equiv_functor_prod_univalence univalence = equiv_functor_prod_no_univalence
  := admit.









































(** *** [prod] *)

Definition prod_code : forall {A B} (x y : A * B), Type
  := admit.

Definition prod_encode : forall {A B} {x y : A * B}, x = y -> prod_code x y
  := admit.

Definition prod_decode : forall {A B} {x y : A * B}, prod_code x y -> x = y
  := admit.

Definition prod_endecode : forall {A B} {x y : A * B} (p : prod_code x y),
                             prod_encode (prod_decode p) = p
  := admit.

Definition prod_deencode : forall {A B} {x y : A * B} (p : x = y),
                             prod_decode (prod_encode p) = p
  := admit.


(** *** [sum] *)

Definition sum_code : forall {A B} (x y : A + B), Type
  := admit.

Definition sum_encode : forall {A B} {x y : A + B}, x = y -> sum_code x y
  := admit.

Definition sum_decode : forall {A B} {x y : A + B}, sum_code x y -> x = y
  := admit.

Definition sum_endecode : forall {A B} {x y : A + B} (p : sum_code x y),
                             sum_encode (sum_decode p) = p
  := admit.

Definition sum_deencode : forall {A B} {x y : A + B} (p : x = y),
                             sum_decode (sum_encode p) = p
  := admit.


(** *** [nat] *)

(** Warmup: *)

Definition zero_ne_one : 0 = 1 -> Empty_set
  := admit.

(** Hint for the above: Use [J]. *)

Definition zero_ne_succ : forall n, 0 = S n -> Empty_set
  := admit.

Definition nat_code : forall (x y : nat), Type
  := admit.

Definition nat_encode : forall {x y : nat},
                                x = y -> nat_code x y
  := admit.

Definition nat_decode : forall {x y : nat},
                                nat_code x y -> x = y
  := admit.

Definition nat_endecode : forall {x y : nat} (p : nat_code x y),
                                  nat_encode (nat_decode p) = p
  := admit.

Definition nat_deencode : forall {x y : nat} (p : x = y),
                                  nat_decode (nat_encode p) = p
  := admit.


(** *** [option] *)

Definition option_code : forall {A} (x y : option A), Type
  := admit.

Definition option_encode : forall {A} {x y : option A}, x = y -> option_code x y
  := admit.

Definition option_decode : forall {A} {x y : option A}, option_code x y -> x = y
  := admit.

Definition option_endecode : forall {A} {x y : option A} (p : option_code x y),
                             option_encode (option_decode p) = p
  := admit.

Definition option_deencode : forall {A} {x y : option A} (p : x = y),
                             option_decode (option_encode p) = p
  := admit.


(** *** [list] *)

Definition list_code : forall {A} (x y : list A), Type
  := admit.

Definition list_encode : forall {A} {x y : list A}, x = y -> list_code x y
  := admit.

Definition list_decode : forall {A} {x y : list A}, list_code x y -> x = y
  := admit.

Definition list_endecode : forall {A} {x y : list A} (p : list_code x y),
                             list_encode (list_decode p) = p
  := admit.

Definition list_deencode : forall {A} {x y : list A} (p : x = y),
                             list_decode (list_encode p) = p
  := admit.


(** **** Homework: mere propositions *)

(** Homework; challenging problem *)

(** Recall the definition of contractibility above.  The reason that we can safely call this contractible is that all of the higher structure collapses.  That is, if all inhabitants of [A] are (continuously) equal, then all inhabitants of [x = y] for [x : A] and [y : A] are also equal.  Prove this, as follows. *)

(** First we define what it means for a type to be a "mere proposition", or to satisfy the uniqueness of identity proofs. *)

Definition is_prop : Type -> Type
  := fun A => forall x y : A, x = y.

(** We classify the equality type of propositions. *)

Definition prop_code : forall {A} (allpaths : is_prop A) (x y : A), Type
  := fun A allpaths x y => unit.

Definition prop_encode : forall {A} (allpaths : is_prop A) {x y : A},
                           x = y -> prop_code allpaths x y
  := admit.

Definition prop_decode : forall {A} (allpaths : is_prop A) {x y : A},
                           prop_code allpaths x y -> x = y
  := admit.

Definition prop_endecode : forall {A} (allpaths : is_prop A) {x y : A} (p : prop_code allpaths x y),
                            prop_encode allpaths (prop_decode allpaths p) = p
  := admit.

(** If you find this proof hard, and can't figure out why, think about the proof of [dec_deencode].  If you're still having trouble, look a bit further down for a hint. *)

Definition prop_deencode : forall {A} (allpaths : is_prop A) {x y : A} (p : x = y),
                             prop_decode allpaths (prop_encode allpaths p) = p
  := admit.

(** Hint: you may need to rewrite your [prop_decode] function.  The following lemmas may prove helpful. *)

(** Try to write an "adjuster" for [is_prop] that will always return something equal to [refl] (provably) when handed two judgmentally equal things. *)

Definition adjust_allpaths : forall {A}, is_prop A -> is_prop A
  := admit.

Definition adjust_allpaths_refl : forall {A} (allpaths : is_prop A) x,
                                   adjust_allpaths allpaths x x = refl
  := admit.

(** Now move these lemmas above [prop_decode] and try re-writing the codes so that you expect [prop_deencode] to work. *)

(** *** decidable types *)

(** Homework; challenging problem *)

(** More generally, we can do this for any type with decidable equality. *)

(** First we define what it means for a type to have decidable equality: it means that we have a (continuous!) function from pairs of inhabitants to proofs that either they are equal, or that their equality is absurd. *)

Definition decidable : Type -> Type
  := fun A => forall x y : A, (x = y) + (x = y -> Empty_set).

Definition dec_code : forall {A} (dec : decidable A) (x y : A), Type
  := admit.

Definition dec_encode : forall {A} (dec : decidable A) {x y : A},
                          x = y -> dec_code dec x y
  := admit.

Definition dec_decode : forall {A} (dec : decidable A) {x y : A},
                          dec_code dec x y -> x = y
  := admit.

Definition dec_endecode : forall {A} (dec : decidable A) {x y : A} (p : dec_code dec x y),
                            dec_encode dec (dec_decode dec p) = p
  := admit.

(** If you find this proof hard, and can't figure out why, look a bit further down for a hint. *)

Definition dec_deencode : forall {A} (dec : decidable A) {x y : A} (p : x = y),
                             dec_decode dec (dec_encode dec p) = p
  := admit.

(** Hint: you may need to rewrite your [dec_decode], [dec_code], and [dec_encode] functions, just as you did with [prop_decode].  The following lemmas may prove helpful. *)

(** Try to write an "adjuster" for decidable equality that will always return something equal to [refl] (provably) when handed two equal things. *)

Definition adjust_dec : forall {A}, decidable A -> decidable A
  := admit.

Definition adjust_dec_refl : forall {A} (dec : decidable A) (x : A),
                               adjust_dec dec x x = inl refl
  := admit.

(** Now move these lemmas above [dec_code] and try re-writing the codes so that you expect [dec_deencode] to work. *)

(** *** Pushing Further *)

(** Homework: Generalize the above two proofs to solve "Puzzle 2" far above.  (Don't forget to also do puzzle 1 while you're at it.) *)

(** Homework: Using the solution to Puzzle 2, show that it is sufficient to assume [function_decode] an axiom; the endecode and [deencode] proofs follow from puzzle 2. *)

Definition function_code' : forall {A B} (f g : forall a : A, B a), Type
  := admit.

Definition function_encode' : forall {A B} {f g : forall a : A, B a}, f = g -> function_code' f g
  := admit.

Axiom function_decode' : forall {A B} {f g : forall a : A, B a}, function_code' f g -> f = g.

Definition function_decode_adjusted' : forall {A B} {f g : forall a : A, B a}, function_code' f g -> f = g
  := admit.

Definition function_endecode' : forall {A B} {f g : forall a : A, B a} (p : function_code' f g),
                                  function_encode' (function_decode_adjusted' p) = p
  := admit.
Definition function_deencode' : forall {A B} {f g : forall a : A, B a} (p : f = g),
                                  function_decode_adjusted' (function_encode' p) = p
  := admit.
