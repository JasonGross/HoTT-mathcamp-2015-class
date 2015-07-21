(* -*- coq-prog-name: "d:/Documents/GitHub/coq-hit/bin/coqtop.exe" -*- *)
(** * Exploring equality via homotopy and proof assistants - Day 5 - Further topics *)
Set Universe Polymorphism.
(** The following are placeholders; [admit] indicates that something
    should be filled in later. *)

Axiom admit : forall {T}, T.

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

Definition J : forall {A} {x : A} (P : forall y, x = y -> Type),
                 P x refl -> forall {y} (H : x = y), P y H
  := fun A x P k y H
     => match H with
          | eq_refl => k
        end.

Definition ap : forall A B (f : A -> B) (x y : A), x = y -> f x = f y
  := fun A B f x y p
     => J (fun y _ => f x = f y) refl p.

Arguments ap {A B} f {x y} p, {A B} f x y p, A B f x y p.

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
     => { p : x.1 = y.1 | J (fun a _ => B a) x.2 p = y.2 }.

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
  := fun A => {| iso_fun x := x;
                 iso_isiso := {| iso_inv x := x;
                                 right_inv x := refl : (fun x => x) x = x;
                                 left_inv x := refl |} |}.

Definition Isomorphic_inverse : forall {A B}, A ≅ B -> B ≅ A
  := fun A B e =>
       {| iso_fun := iso_inv e;
          iso_isiso := {| iso_inv := iso_fun e;
                          right_inv := left_inv e;
                          left_inv := right_inv e |} |}.

Definition Isomorphic_compose : forall {A B C}, A ≅ B -> B ≅ C -> A ≅ C
  := fun A B C e1 e2 =>
       {| iso_fun x := iso_fun e2 (iso_fun e1 x);
          iso_isiso := {| iso_inv x := iso_inv e1 (iso_inv e2 x);
                          right_inv x := trans (ap e2 (right_inv e1 (iso_inv e2 x)))
                                               (right_inv e2 x);
                          left_inv x := trans (ap (iso_inv e1) (left_inv e2 (e1 x)))
                                              (left_inv e1 x) |} |}.


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

Definition equiv_refl : forall {A}, A ≃ A.
Proof.
  refine (fun A => {| equiv_fun := fun x => x;
                      equiv_isequiv := fun b => {| center := (b; refl) |} |}).
  intros [a p].
  destruct p; reflexivity.
Defined.

(** We can prove that an equivalence gives us an isomorphism very
    easily. *)

Definition iso_of_equiv : forall {A B}, A ≃ B -> A ≅ B.
Proof.
  refine (fun A B e
          => {| iso_fun x := e x;
                iso_isiso := {| iso_inv x := (@center _ (equiv_isequiv e x)).1 |} |}).
  { intro x.
    apply (center {a : A | e a = x}).2. }
  { intro x.
    refine (@trans _ _ (x; _).1 _ _ _); shelve_unifiable.
    { apply ap.
      apply contr. }
    { exact (refl (x; refl).1). } }
Defined.

(** We can go the other way with more work. *)

(** Optional Homework: Complete this proof. *)

Definition equiv_of_iso : forall {A B}, A ≅ B -> A ≃ B.
Proof.
  refine (fun A B e
          => {| equiv_fun := e;
                equiv_isequiv b := {| center := exist (fun a => e a = b) (iso_inv e b) (right_inv e b);
                                      contr := _ |} |}).
  intros [a p].
  destruct p; simpl.
  apply sigma_decode.
  pose (q := (trans (ap (iso_inv e) (ap e (sym (left_inv e a))))
                (trans (ap (iso_inv e) (right_inv e (e a)))
                       (left_inv e a)))).
  exists q.
  simpl.
  transitivity (trans (sym (ap e q)) (right_inv e _)).
  { generalize (right_inv e (e a)).
    clearbody q.
    revert q.
    generalize (iso_inv e).
    intro g.
    generalize (g (e a)).
    intros ? q.
    destruct q; simpl.
    intro e0; case e0.
    reflexivity. }
  { subst q.
    repeat rewrite <- ?ap_sym, ?sym_trans, ?ap_trans, ?sym_sym, ?trans_pp_p.
    rewrite !(ap_compose (iso_inv e) e).
    rewrite (@concat_A1p _ (fun x => e (iso_inv e x)) (right_inv e)).
    erewrite <- (trans_Vp (ap e left_inv)).
    rewrite ap_sym.
    apply ap.
    rewrite <- !trans_pp_p.
    rewrite (@concat_A1p _ (fun x => e (iso_inv e x)) (right_inv e)).
    rewrite trans_pV, trans_1p; reflexivity. }
Defined.


Definition Type_code : forall (x y : Type), Type
  := fun x y => x ≃ y.

Definition Type_encode : forall {x y : Type}, x = y -> Type_code x y
  := fun x y p
     => match p with
          | refl => equiv_refl
        end.

(** The following are unprovable in Coq, currently.  They are
    collectively known as the "univalence axiom". *)

Axiom Type_decode : forall {x y : Type}, Type_code x y -> x = y.
Axiom Type_endecode : forall {x y : Type} (p : Type_code x y),
                         Type_encode (Type_decode p) = p.
Axiom Type_deencode : forall {x y : Type} (p : x = y),
                         Type_decode (Type_encode p) = p.

Definition Univalence : forall {x y : Type}, IsEquiv (@Type_encode x y)
  := fun x y
     => equiv_isequiv
          (equiv_of_iso
             {| iso_fun := @Type_encode x y;
                iso_isiso := {| iso_inv := @Type_decode x y;
                                right_inv := Type_endecode;
                                left_inv := Type_deencode |} |}).

Definition transport {A} (P : A -> Type) {x y} (p : x = y) (u : P x) : P y
  := eq_rect _ P u _ p.

Definition apD {A} {B} (f : forall a : A, B a) {x y} (p : x = y) : transport B p (f x) = f y
  := J (fun y' p => transport B p (f x) = f y') refl p.

Definition J_transport_const : forall {A} {P k} {x y : A} {p : x = y},
                                 J (fun _ _ => P) k p = k
  := fun A P k x y p
     => match p with
          | refl => refl
        end.

Definition ap' {A B} (f : A -> B) {x y} (p : x = y) : f x = f y
  := trans (sym J_transport_const) (apD f p).

Module Import Interval.
  Local Unset Elimination Schemes.
  Inductive Interval := zero | one.
  Axiom seg : zero = one.
  Definition Interval_rect
  : forall (P : Interval -> Type) (a : P zero) (b : P one)
           (c : J (fun y _ => P y) a seg = b)
           (i : Interval),
      P i
    := fun P a b c i
       => match i with
            | zero => fun _ => a
            | one => fun _ => b
          end c.

  Axiom Interval_rect_beta_seg
  : forall (P : Interval -> Type)
           (a : P zero) (b : P one) (p : transport _ seg a = b),
      apD (Interval_rect P a b p) seg = p.
End Interval.

Definition Interval_rectnd (P : Type) (a b : P) (p : a = b)
: Interval -> P
  := Interval_rect (fun _ => P) a b (trans J_transport_const p).

Definition Interval_rectnd_beta_seg (P : Type) (a b : P) (p : a = b)
  : ap' (Interval_rectnd P a b p) seg = p.
Proof.
  unfold ap'.
  unfold Interval_rectnd.
  rewrite Interval_rect_beta_seg.
  rewrite <- trans_pp_p.
  rewrite trans_Vp.
  rewrite trans_1p.
  reflexivity.
Defined.

Definition funext : forall {A B} (f g : forall a : A, B a)
                           (H : forall a, f a = g a),
                      f = g.
Proof.
  intros A B f g H.
  pose ((fun k => ap (fun i a => Interval_rect (fun _ => B a) (f a) (g a) (k a) i) seg)) as r.
  simpl in r.
  refine (r _).
  case seg.
  exact H.
Defined.

(**
<<
Inductive interval : Set :=
| zero : interval
| one : interval
with paths :=
  seg : zero = one.

Definition funext' : forall {A B} (f g : forall a : A, B a)
                            (H : forall a, f a = g a),
                       f = g
  := fun A B f g H
     => ap (fun i a => fixmatch {h} i with
           | zero => f a
           | one => g a
           | seg => match seg as seg in (_ = one') return eq_rect zero (fun _ => B a) (f a) one' seg = g a with
                      | refl => H a
                    end
            end)
           seg.

Lemma interval_rect_beta_seg
: forall (P : interval -> Type)
         (a : P zero) (b : P one) (p : transport _ seg a = b),
    apD (interval_rect P a b p) seg = p.
Proof.
  intros P a b p.
  transitivity (interval_rect2 P a b p _ _ seg); [ | reflexivity ].
  generalize seg; intro e.
  destruct e; reflexivity.
Defined.

Definition interval_rectnd (P : Type) (a b : P) (p : a = b)
: interval -> P
  := interval_rect (fun _ => P) a b (trans J_transport_const p).

Definition interval_rectnd_beta_seg (P : Type) (a b : P) (p : a = b)
  : ap' (interval_rectnd P a b p) seg = p.
Proof.
  unfold ap'.
  unfold interval_rectnd.
  rewrite interval_rect_beta_seg.
  rewrite <- trans_pp_p.
  rewrite trans_Vp.
  rewrite trans_1p.
  reflexivity.
Defined.

>> *)

Definition i : bool -> Interval := fun x => if x then one else zero.

(** Puzzle: invert this function; define a function [myst] such that
    [myst (i true) ≡ true] and [myst (i false) ≡ false]. *)

Definition negb_involutive : forall {b}, negb (negb b) = b
  := fun b => if b return negb (negb b) = b
              then refl
              else refl.

Global Instance isequiv_negb : IsEquiv negb.
Proof.
  refine (fun b => _).
  refine {| center := (negb b; negb_involutive) |}.
  intros [a p].
  destruct p.
  destruct a; reflexivity.
Defined.

Definition equiv_negb : bool ≃ bool
  := {| equiv_fun := negb |}.

Lemma transport_idmap_ap : forall {A P x y p u},
                             @transport A P x y p u = transport (fun x => x) (ap' P p) u.
Proof.
  destruct p; reflexivity.
Defined.

Lemma transport_path_universe
: forall {A B} (f : A ≃ B) u,
    transport (fun x => x) (Type_decode f) u = f u.
Proof.
  intros A B f u.
  rewrite <- (Type_endecode f), Type_deencode.
  generalize (Type_decode f).
  intro e; destruct e; reflexivity.
Defined.

Notation Type0 := Set.

Definition tboH : eq_rect _ (fun _ => Type0) _ one seg = bool
  := trans J_transport_const (Type_decode equiv_negb).

(**
<<
Definition twisted_bool_of (x : interval) : Type
  := (fixmatch {h} x with
     | zero => bool : Type
     | one => bool : Type
     | seg => tboH
      end).
>> *)
Definition twisted_bool_of (x : Interval) : Type
  := Interval_rect (fun _ => Type0) bool bool tboH x.

Definition nearly_if_helper : eq_rect zero twisted_bool_of false one seg = true.
Proof.
  change (transport twisted_bool_of seg false = true).
  transitivity (transport (fun x => x) (ap' twisted_bool_of seg) false).
  { exact transport_idmap_ap. }
  { symmetry; transitivity (transport (fun x => x) (Type_decode equiv_negb) (negb true)).
    { rewrite transport_path_universe; simpl; reflexivity. }
    { cut (Type_decode equiv_negb
           = ap' twisted_bool_of seg).
      { intro H; rewrite H; reflexivity. }
      { change twisted_bool_of with (Interval_rectnd Type0 bool bool (Type_decode equiv_negb)).
        rewrite Interval_rectnd_beta_seg.
        reflexivity. } } }
Defined.

Definition nearly_if : forall x, twisted_bool_of x.
Proof.
  exact (Interval_rect twisted_bool_of false true nearly_if_helper).
Defined.

Definition id_factored_true : nearly_if (i true) = true := refl.
Definition id_factored_false : nearly_if (i false) = false := refl.

Module Import Minus1Trunc.
  Local Unset Elimination Schemes.
  Inductive Minus1Trunc (A : Type) := trunc (x : A).
  Global Arguments trunc A x, {A} x.
  Axiom istrunc_trunc : forall {A} (x y : A), trunc x = trunc y.
  Definition Minus1Trunc_rect
  : forall (A : Type)
           (P : Minus1Trunc A -> Type) (k : forall x : A, P (trunc x))
           (c : forall x y, J (fun y _ => P y) (k x) (istrunc_trunc x y) = (k y))
           (x : Minus1Trunc A),
      P x
    := fun A P k c x
       => match x with
            | trunc x' => fun _ => k x'
          end c.
End Minus1Trunc.

(**
<<
Inductive minus1Trunc (A : Type) :=
| trunc (x : A)
with paths :=
  istrunc_trunc (x y : A) : (trunc x) = (trunc y).

Global Arguments trunc {A} x, A x.
>> *)

Module Import Circle.
  Local Unset Elimination Schemes.
  Inductive S1 : Set := base : S1.
  Axiom loop : base = base.
  Definition S1_rect
  : forall (P : S1 -> Type) (k : P base)
           (c : J (fun y _ => P y) k loop = k)
           (x : S1),
      P x
    := fun P k c x
       => match x with
            | base => fun _ => k
          end c.
End Circle.

(**
<<
Inductive S¹ :=
| base : S¹
with paths :=
  loop : base = base.
>> *)


(** Challenge: prove that the 0-truncation of the type [base = base] is
    isomorphic to the integers (i.e., π₁(S¹) ≃ ℤ) *)


(** Other topic ideas: homotopies, axioms of choice, laws of excluded middle.

    Löb's theorem, quining

    More ideas: Models of type theory:

    * How do we know univalence is consistent?
    * Interpretation functions
    * Model in sets (not of univalence, though)
    * Model in topological spaces?
    * Model in Quillen Model Categories?
    * cubical model/proof assistant that runs on Kan complexes *)
