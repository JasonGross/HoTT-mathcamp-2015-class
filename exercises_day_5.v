(* -*- coq-prog-name: "d:/Documents/GitHub/coq-hit/bin/coqtop.exe" -*- *)

Inductive interval :=
| zero : interval
| one : interval
with paths :=
| seg : zero = one.

Definition function_extensionality
: forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.
Admitted.

Inductive S¹ :=
| base : S¹
with paths :=
| loop : base = base.

Inductive unit := tt.
Definition unit_elim : forall (P : unit -> Type) (x : unit), P tt -> P x
  := fun P x Ptt => match x with
                      | tt => Ptt
                    end.


Inductive nat' := Z' | S' (x : nat').
Fixpoint nat'_elim (P : nat' -> Type) (x : nat')
: P Z' -> (forall n, P n -> P (S' n)) -> P x
  := fun Pz Ps =>
       match x with
         | Z' => Pz
         | S' x' => Ps x' (nat'_elim P x' Pz Ps)
       end.

Fail Fixpoint bad (x : unit) : Empty_set
  := match x with
       | tt => bad tt
     end.

Definition eq_elim : forall A (x : A) (P : forall y, eq x y -> Type),
                       P x eq_refl -> forall y (H : eq x y), P y H
  := fun A x P Prefl y H => match H with
                              | eq_refl => Prefl
                            end.

Definition J_nondep : forall {A} {x : A} (P : A -> Type),
                        P x -> forall {y}, x = y -> P y
  := fun A x P Prefl y H => match H with
                              | eq_refl => Prefl
                            end.

Definition S¹_elim (P : S¹ -> Type) (x : S¹) (Pbase : P base)
: (J_nondep P Pbase loop = Pbase) -> P x.
Proof.
  refine (fun Ploop => S¹_rect P Pbase Ploop x).
Defined.

Definition circle_contractible' : forall x : S¹, x = base.
Proof.
  refine (fun x => _).
  refine (S¹_elim
            (fun x' => x' = base) x
            eq_refl
            _).
  transitivity (eq_sym loop).
  { case loop; exact eq_refl. }
Abort.

(*Inductive zero_truncation (A : Type) :=
| incl (x : A)
with paths :=
| trunc (x y : A) (p q : incl x = incl y) : p = q.
*)
(*

Definition S¹_code (x : S¹) : Type
  := match x with
       | base => ℤ
       | loop => univalence applied to the automorphism (+1)
   end.




forall x : S¹, (base = x) ≃ ℤ
Idea:
  pattern match on x
  when x is base, we get 0
  on the loop,

Definition circle_contractible : forall x y : S¹, x = y.
Proof.
  refine (fun x => _).

  refine (S¹_elim
            (fun x' => forall y, x' = y) x
            _
            _).
About S¹_rect.
  *)

Definition choice_inf
: forall (I : Type) (X : I -> Type) (P : forall i, X i -> Prop),
    (forall i : I, { x : X i | P i x })
    -> { g : forall i, X i | forall i, P _ (g i) }.
Proof.
  refine (fun I X P proof_of_nonemptyness => _).
  refine (exist _ (fun i => proj1_sig (proof_of_nonemptyness i)) _).
  refine (fun i => proj2_sig (proof_of_nonemptyness i)).
Defined.

Inductive interval' := zero' | one'.
Axiom seg' : zero' = one'.

Inductive -1Trunc (A : Type) := incl (x : A).
Axiom -1trunc_istrunc : forall A (x y : -1Trunc A), x = y.


Inductive 0Trunc (A : Type) := incl (x : A).
Axiom 0trunc_istrunc : forall A (x y : 0Trunc A) (p q : x = y), p = q.

Definition choice_n
: forall (I : Type) (X : I -> Type) (P : forall i, X i -> Prop),
    (forall i : I, ∥ { x : X i | P i x } ∥_n)
    -> ∥ { g : forall i, X i | forall i, P _ (g i) } ∥_n.
