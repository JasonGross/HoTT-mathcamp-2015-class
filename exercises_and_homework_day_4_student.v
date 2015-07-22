(** * Exploring equality via homotopy and proof assistants - Day 4 - Equality of types *)
(** This file contains the exercises for Day 4.  Some are explicitly
    marked as "Homework"; the rest can be done either in class or for
    homework.

    When doing exercises on your own, feel free to skip around; there
    are some interesting puzzles near the bottom.

    If you feel like you know exactly how a proof will go, but find it
    painful and tedious to write out the proof terms explicitly, come
    find me.  Coq has a lot of support for automation and taking care
    of things that are easy and verbose, so you don't have to.
    Proving should feel like a game.  If it doesn't, I can probably
    help you with that.

    This file is set up a bit differently from previous days; I want
    you to generate more of the ideas for this one.  So I've left in
    only the stubs at the top for you, without the comments that
    pepper my version of the file.  You should follow along, copying
    the the code as I reveal or type it on the screen, so you can play
    with it to make suggestions.  I'll be releasing my (filled in)
    version of the file after class today, so that you have the
    comments for future reference. *)

(** The following are placeholders; [admit] indicates that something
    should be filled in later. *)

Axiom admit : forall {T}, T.

(** Compatibility between Coq 8.5 and 8.4 *)

Set Asymmetric Patterns.

(* begin hide *)
(** Some filled in exercises from yesterday; feel free to paste more here. *)

Notation refl := eq_refl.
Definition sym : forall A (x y : A), x = y -> y = x
  := fun A x y p
     => match p in (_ = y) return y = x with
          | refl => refl
        end.

(** We allow writing [sym p] to mean [sym _ _ _ p] *)

Arguments sym {A x y} p, A x y p.

Definition trans : forall A (x y z : A), x = y -> y = z -> x = z
  := fun A x y z p
     => match p in (_ = y) return y = z -> x = z with
          | refl => fun q => match q in (_ = z) return x = z with
                               | refl => refl
                             end
        end.

Arguments trans {A x y z} !p !q, A x y z !p !q.

Definition ap : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := fun A B f x y p
     => match p with
          | refl => refl
        end.

Arguments ap {A B} f {x y} p, {A B} f x y p, A B f x y p.

Definition J : forall {A} {x y : A} (H : x = y)
                      (P : forall y, x = y -> Type),
                 P x refl -> P y H
  := fun A x y H P k
     => match H with
          | eq_refl => k
        end.

Definition sym_sym : forall A (x y : A) (p : x = y), sym (sym p) = p
  := fun A x y p
     => match p with
          | refl => refl
        end.

Arguments sym_sym {A x y} p, A x y p.

Definition ap_sym : forall {A B} (f : A -> B) {x y : A} (p : x = y),
                         ap f (sym p) = sym (ap f p)
  := fun A B f x y p
     => match p with
          | refl => refl
        end.

Arguments ap_sym {A B} f {x y} p, A B f x y p.

Definition ap_trans : forall {A B} (f : A -> B) {x y z : A} (p : x = y) (q : y = z),
                           ap f (trans p q) = trans (ap f p) (ap f q)
  := fun A B f x y z p
     => match p with
          | refl => fun q => match q with
                               | refl => refl
                             end
        end.

Arguments ap_trans {A B} f {x y z} p q, A B f x y z p q.

Definition ap_compose : forall {A B C} (f : A -> B) (g : B -> C) {x y : A} (p : x = y),
                           ap g (ap f p) = ap (fun x => g (f x)) p
  := fun A B C f g x y p
     => match p with
          | refl => refl
        end.

Arguments ap_trans {A B} f {x y z} p q, A B f x y z p q.

Definition sym_trans : forall {A} {x y z : A} (p : x = y) (q : y = z),
                           sym (trans p q) = trans (sym q) (sym p)
  := fun A x y z p
     => match p with
          | refl => fun q => match q with
                               | refl => refl
                             end
        end.

Definition trans_1p : forall {A} {x y : A} (p : x = y), trans refl p = p
  := fun A x y p
     => match p with
          | refl => refl
        end.

Definition trans_pp_p : forall {A} {x y z w : A} (p : x = y) (q : y = z) (r : z = w),
                          trans (trans p q) r = trans p (trans q r)
  := fun A x y z w p
     => match p with
          | refl => fun q => match q with
                               | refl => fun r => match r with
                                                    | refl => refl
                                                  end
                             end
        end.

Definition trans_p1 : forall {A} {x y : A} (p : x = y), trans p refl = p
  := fun A x y p
     => match p with
          | refl => refl
        end.

Definition trans_Vp : forall {A} {x y : A} (p : x = y), trans (sym p) p = refl
  := fun A x y p
     => match p with
          | refl => refl
        end.

Definition trans_pV : forall {A} {x y : A} (p : x = y), trans p (sym p) = refl
  := fun A x y p
     => match p with
          | refl => refl
        end.

Definition concat_Ap
: forall {A B} (f g : A -> B)
         (T : forall x, f x = g x),
    forall {x y : A} (m : x = y),
      trans (ap f m) (T y) = trans (T x) (ap g m).
Proof.
  intros A B f g T x y m.
  destruct m; simpl.
  destruct (T x).
  reflexivity.
Defined.

Definition concat_A1p
: forall {A} (f : A -> A)
         (T : forall x, f x = x),
    forall {x y : A} (m : x = y),
      trans (ap f m) (T y) = trans (T x) m.
Proof.
  intros A f T x y m.
  destruct m; simpl.
  destruct (T x).
  reflexivity.
Defined.

Definition concat_Ap1
: forall {A} (f : A -> A)
         (T : forall x, x = f x),
    forall {x y : A} (m : x = y),
      trans m (T y) = trans (T x) (ap f m).
Proof.
  intros A f T x y m.
  destruct m; simpl.
  destruct (T x).
  reflexivity.
Defined.

Definition function_code : forall {A B} (f g : forall a : A, B a), Type
  := fun A B f g => forall a : A, f a = g a.

Definition function_encode : forall {A B} {f g : forall a : A, B a}, f = g -> function_code f g
  := fun A B f g H a
     => match H with
          | refl => refl
        end.

Definition function_encode_sym
: forall {A B f g} (p : f = g) x,
    sym (@function_encode A B f g p x) = function_encode (sym p) x
  := fun A B f g p x
     => match p with
          | refl => refl
        end.

Definition function_encode_trans
: forall {A B f g h} (p : f = g) (q : g = h) x,
    trans (@function_encode A B f g p x)
          (@function_encode A B g h q x)
    = function_encode (trans p q) x
  := fun A B f g h p
     => match p with
          | refl => fun q x => match q with
                                 | refl => refl
                               end
        end.

Definition function_encode_ap : forall {A B C} {f g : A -> B} (p : f = g) (f' : B -> C) x,
                                   ap f' (@function_encode A (fun _ => B) f g p x)
                                   = function_encode (ap (fun f'' x' => f' (f'' x')) p) x
  := fun A B C f g p f' x
     => match p with
          | refl => refl
        end.

Notation sig := sigT.
Notation exist := existT.
Notation "{ x  |  P }" := ({ x : _ & P }) : type_scope.
Notation "{ x : A  |  P }" := ({ x : A & P }) : type_scope.
Notation "( x ; p )" := (existT _ x p).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Definition sigma_code : forall {A B} (x y : { a : A | B a }), Type
  := fun A B x y
     => { p : x.1 = y.1 | J p (fun a _ => B a) x.2 = y.2 }.

Definition sigma_encode : forall {A B} {x y : { a : A | B a }}, x = y -> sigma_code x y
  := fun A B x y p
     => match p with
          | refl => (refl; refl)
        end.

Definition sigma_decode : forall {A B} {x y : { a : A | B a }}, sigma_code x y -> x = y.
Proof.
  refine (fun A B x y
          => match x, y return sigma_code x y -> x = y with
               | (x1; x2), (y1; y2)
                 => fun p => _
             end).
  destruct p as [p q].
  simpl in *.
  destruct q.
  destruct p; simpl.
  exact refl.
Defined.

Definition sigma_endecode : forall {A B} {x y : { a : A | B a }} (p : sigma_code x y),
                             sigma_encode (sigma_decode p) = p.
Proof.
  intros A B x y p.
  destruct x, y, p as [p q]; simpl in *.
  destruct q, p; simpl.
  reflexivity.
Defined.

Definition sigma_deencode : forall {A B} {x y : { a : A | B a }} (p : x = y),
                             sigma_decode (sigma_encode p) = p.
Proof.
  intros A B x y p.
  destruct p, x; simpl.
  reflexivity.
Defined.

Definition is_prop : Type -> Type
  := fun A => forall x y : A, x = y.

(** We classify the equality type of propositions. *)

Definition prop_code : forall {A} (allpaths : is_prop A) (x y : A), Type
  := fun A allpaths x y => unit.

Definition prop_encode : forall {A} (allpaths : is_prop A) {x y : A},
                           x = y -> prop_code allpaths x y
  := fun _ _ _ _ _ => tt.

(** You can fill in the proof here from day 3 *)
Definition prop_decode : forall {A} (allpaths : is_prop A) {x y : A},
                           prop_code allpaths x y -> x = y
  := admit.


Definition prop_deencode : forall {A} (allpaths : is_prop A) {x y : A} (p : x = y),
                             prop_decode allpaths (prop_encode allpaths p) = p
  := admit.

(* end hide *)

(** ** Equality of types *)

(** *** Motivating Puzzle *)

(** Puzzle for the day: classify the equalities of types.  That is,
    fill in the following: *)

Definition Type_code : forall (x y : Type), Type
  := admit.

Definition Type_encode : forall {x y : Type}, x = y -> Type_code x y
  := admit.

(** The following are unprovable in Coq, currently.  They are
    collectively known as the "univalence axiom". *)

Axiom Type_decode : forall {x y : Type}, Type_code x y -> x = y.
Axiom Type_endecode : forall {x y : Type} (p : Type_code x y),
                        Type_encode (Type_decode p) = p.
Axiom Type_deencode : forall {x y : Type} (p : x = y),
                        Type_decode (Type_encode p) = p.

(** *** Provable equalities *)

(** What equalities of types are provable? *)





































(** *** Provable inequalities *)

(** What equalities of types are provably absurd? *)


























(** More generally, when are two types provably different? *)






































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

(** Tell Coq that the function associated to an [Isomorphic] object is
    always an isomorphism. *)

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


(** More practice: You can prove the higher groupoid laws about
    isomorphisms, but it's a bit of a pain. *)










































(** *** Equivalences *)

(** We can define a slight variation on isomorphisms, called
    "contractible fibers", which generalizes the notion of
    injective+surjective.  If you're interested in the various ways of
    formulating equivalences, Chapter 4 of the HoTT Book
    (http://homotopytypetheory.org/book/) is an excellent resource. *)

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

(** We can prove that an equivalence gives us an isomorphism very
    easily. *)

Definition iso_of_equiv : forall {A B}, A ≃ B -> A ≅ B
  := admit.

(** We can go the other way with more work. *)

(** Optional Homework: Complete this proof. *)

Definition equiv_of_iso : forall {A B}, A ≅ B -> A ≃ B.
Proof.
  refine (fun A B e
          => {| equiv_fun := e |}).
  refine admit.
Defined.








(** Now, we prove the following helper lemma, which lets us get the
    right codes for [Equiv].  We again assume functional
    extensionality. *)

Section assume_funext'.
  Context (function_decode : forall {A B} {f g : forall a : A, B a}, function_code f g -> f = g)
          (function_endecode : forall {A B} {f g : forall a : A, B a} (p : function_code f g),
                                 function_encode (function_decode p) = p)
          (function_deencode : forall {A B} {f g : forall a : A, B a} (p : f = g),
                                 function_decode (function_encode p) = p).

  (** Homework: Complete this proof. *)
  Definition allpath_contr : forall {A} (x y : Contr A), x = y
    := admit.

  Definition allpath_isequiv : forall {A B} (f : A -> B) (e1 e2 : IsEquiv f), e1 = e2
    := admit.

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
End assume_funext'.

(** Now that we have a "good" type of isomorphism/equivalence (one
    with the right equality type), we can go back to the question of
    [Isomorphic_ap]; Recall that we want to prove:

<<
Definition Isomorphic_ap : forall (f : Type -> Type) {A B}, A ≅ B -> f A ≅ f B.
>> *)

(** We can prove this by axiomatizing the codes for types: *)

Definition Type_code' : forall (x y : Type), Type
  := fun x y => x ≃ y.

Definition Type_encode' : forall {x y : Type}, x = y -> Type_code' x y
  := admit.

(** The following are unprovable in Coq, currently.  They are
    collectively known as the "univalence axiom". *)

Axiom Type_decode' : forall {x y : Type}, Type_code' x y -> x = y.
Axiom Type_endecode' : forall {x y : Type} (p : Type_code' x y),
                         Type_encode' (Type_decode' p) = p.
Axiom Type_deencode' : forall {x y : Type} (p : x = y),
                         Type_decode' (Type_encode' p) = p.

Definition Univalence : forall {x y : Type}, IsEquiv (@Type_encode' x y)
  := fun x y
     => equiv_isequiv
          (equiv_of_iso
             {| iso_fun := @Type_encode' x y;
                iso_isiso := {| iso_inv := @Type_decode' x y;
                                right_inv := Type_endecode';
                                left_inv := Type_deencode' |} |}).

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

(** Challenge: Show, without axioms, that univalence implies
    functional extensionality: *)

Definition univalence_implies_funext
: (forall A B, IsEquiv (@Type_encode' A B))
  -> (forall A B (f g : forall a : A, B a), (forall a, f a = g a) -> f = g)
  := admit.

Print Assumptions univalence_implies_funext.

(** Exercise 2.17 from the HoTT Book:

  Show that if [A ≃ A'] and [B ≃ B'], then [(A * B) ≃ (A' * B')] in
  two ways: once using univalence, and once without assuming it. *)

Definition equiv_functor_prod_univalence
: (forall A B, IsEquiv (@Type_encode A B))
  -> forall A A' B B',
       A ≃ A' -> B ≃ B' -> (A * B ≃ A' * B')%type
  := admit.

Print Assumptions equiv_functor_prod_univalence.

Definition equiv_functor_prod_no_univalence
: forall A A' B B',
    A ≃ A' -> B ≃ B' -> (A * B ≃ A' * B')%type
  := admit.

Print Assumptions equiv_functor_prod_no_univalence.

(** Now prove that these two ways are equal *)

Definition equiv_functor_prod_eq
: forall univalence,
    equiv_functor_prod_univalence univalence = equiv_functor_prod_no_univalence
  := admit.
