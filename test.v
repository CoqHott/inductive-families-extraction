Require Import Vector.
Require Import List.

Set Primitive Projections.

Record sig {A : Type} (P : A -> Prop) : Type := exist
  { proj1_sig : A ;
    proj2_sig : P proj1_sig }.


Notation "{ x : A & P }" := (sig (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (proj1_sig _ x) (at level 3).
Notation "x .2" := (proj2_sig _ x) (at level 3).
Notation " ( x ; p ) " := (exist _ _ x p).

Fixpoint IsVect A (n : nat) (l : list A) : Prop :=
  match n,l with
  | 0,nil => True
  | S _ , nil => False
  | 0, cons _ _ => False
  | S n , cons _ l => IsVect _ n l end.
 
(* Inductive IsVect A : nat -> list A -> Prop := *)
(* | nil0 : IsVect A 0 nil *)
(* | cons0 : forall x n l, IsVect A n l -> IsVect A (S n) (cons x l). *)
                 
Definition llist A n := {l : list A & IsVect A n l}. 

Definition cons_l : forall A , A -> forall n : nat, llist A n -> llist A (S n) :=
  fun A x n l => (cons x (l.1) ; l.2).

Definition nil_l : forall A , llist A 0 :=
  fun A => (nil ; I).

(* Definition cons_l : forall A , A -> forall n : nat, llist A n -> llist A (S n) := *)
(*   fun A x n l => (cons x (l.1) ; cons0 A x n l.1 l.2). *)

Definition t_rect 
     : forall (A : Type) (P : forall n : nat, t A n -> Type),
       P 0 (Vector.nil A) ->
       (forall (h : A) (n : nat) (t : t A n), P n t -> P (S n) (Vector.cons A h n t)) -> forall (n : nat) (t : t A n), P n t := 
fun (A : Type) (P : forall n : nat, t A n -> Type) (f : P 0 (Vector.nil A))
  (f0 : forall (h : A) (n : nat) (t : t A n), P n t -> P (S n) (Vector.cons A h n t)) =>
fix F (n : nat) (t : t A n) {struct t} : P n t :=
  match t as t0 in (Vector.t _ n0) return (P n0 t0) with
  | Vector.nil _ => f
  | Vector.cons _ h n0 t0 => f0 h n0 t0 (F n0 t0)
  end.

Definition llist_rect 
     : forall (A : Type) (P : forall n : nat, llist A n -> Type),
       P 0 (nil_l A) ->
       (forall (h : A) (n : nat) (t : llist A n), P n t -> P (S n) (cons_l A h n t)) ->
       forall (n : nat) (t : llist A n), P n t := 
fun (A : Type) (P : forall n : nat, llist A n -> Type) (f : P 0 (nil_l A))
  (f0 : forall (h : A) (n : nat) (t : llist A n), P n t -> P (S n) (cons_l A h n t)) n X =>
    (fix F (n : nat) (t : list A) {struct t} : forall (H : IsVect A n t), P n (t;H) :=
  match t as t0, n as n0 return forall (H : IsVect A n0 t0), (P n0 (t0;H)) with
  | nil,0 => fun i => match i with I => f end
  | nil, S _ => fun i => match i with end
  | cons h t0, S n0 => fun i => f0 h n0 (t0;i) (F n0 t0 i)
  | cons _ _ , 0 => fun i => match i with end
  end) n X.1 X.2.

Definition caseS' : forall {A : Type} (P : forall n : nat, t A (S n) -> Type),
    (forall (h : A) (n : nat) (t : t A n), P n (Vector.cons A h n t)) ->
    forall {n : nat} (v : t A (S n)), P n v :=
  fun (A : Type) (P : forall n : nat, t A (S n) -> Type)
       (H : forall (h : A) (n : nat) (t : t A n), P n (Vector.cons A h n t))
       (n : nat) (v : t A (S n)) =>
    t_rect A (fun n => match n with 0 => fun _ => unit | S m => P m end) tt
                  (fun (h : A) (m : nat) (t0 : t A m) _ => H h m t0) (S n) v.

Definition caseS'_l : forall {A : Type} (P : forall n : nat, llist A (S n) -> Type),
       (forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) ->
       forall {n : nat} (v : llist A (S n)), P n v  :=
  fun (A : Type) (P : forall n : nat, llist A (S n) -> Type)
       (H : forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t))
       (n : nat) (v : llist A (S n)) =>
    llist_rect A (fun n => match n with 0 => fun _ => unit | S m => P m end) tt
                  (fun (h : A) (m : nat) (t0 : llist A m) _ => H h m t0) (S n) v.

Extraction llist_rect.

Definition caseS : forall {A : Type} (P : forall n : nat, t A (S n) -> Type),
    (forall (h : A) (n : nat) (t : t A n), P n (Vector.cons A h n t)) ->
    forall {n : nat} (v : t A (S n)), P n v :=
  fun (A : Type) (P : forall n : nat, t A (S n) -> Type)
      (H : forall (h : A) (n : nat) (t : t A n), P n (Vector.cons A h n t))
      (n : nat) (v : t A (S n)) =>
    match
      v as v0 in (t _ n0)
      return
      (match n0 as x return (t A x -> Type) with
       | 0 => fun _ : t A 0 => False -> IDProp
       | S n1 => fun v1 : t A (S n1) => P n1 v1
       end v0)
    with
    | Vector.nil _ => fun devil : False => False_ind IDProp devil
    | Vector.cons _ h n0 t0 => H h n0 t0
    end.

Definition caseS_l : forall {A : Type} (P : forall n : nat, llist A (S n) -> Type),
    (forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) ->
    forall {n : nat} (v : llist A (S n)), P n v :=
  fun (A : Type) (P : forall n : nat, llist A (S n) -> Type)
      (H : forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t))
      (n : nat) (v : llist A (S n)) =>
    match
      v.1 as v0, S n as n0
      return forall H0 : IsVect A n0 v0,
      (match n0 as x return (llist A x -> Type) with
       | 0 => fun _ : llist A 0 => False -> IDProp
       | S n1 => fun v1 : llist A (S n1) => P n1 v1
       end (v0;H0))
    with
    | nil, 0 => fun i (devil : False) => False_ind IDProp devil
    | nil, S _ => fun i => match i with end
    | cons h t0, S n0 => fun i => H h n0 (t0;i)
    | cons h t0, 0 => fun i => match i with end
    end v.2.


Definition caseS_l :=
(fun (A : Type) (P : forall n : nat, llist A (S n) -> Type)
  (H : forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t))
  (n : nat) (v : llist A (S n)) =>
match
  v.1 as v0, n as n0 
  (* in (IsVect _ n0 l) *)
  return
    (match n0 as x return (llist A x -> Type) with
     | 0 => fun _ : llist A 0 => False -> IDProp
     | S n1 => fun v1 : llist A (S n1) => P n1 v1
     end (v0;v.2))
with
| nil, _ => fun devil : False => False_ind IDProp devil
| cons h t0, S n => H h n (t0;v.2)
end)
     : forall {A : Prop} (P : forall n : nat, llist A (S n) -> Prop),
       (forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) ->
       forall {n : nat} (v : llist A (S n)), P n v.





Definition caseS_l := 
(fun (A : Type) (P : forall n : nat, llist A (S n) -> Prop)
  (H : forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) 
  (n : nat) (v : llist A (S n)) =>
match
  v.2 as v20 in (IsVect _ n0 l)
  return
    (match n0 as x return (llist A x -> Prop) with
     | 0 => fun _ : llist A 0 => False -> IDProp
     | S n1 => fun v1 : llist A (S n1) => P n1 v1
     end (l;v20))
with
| nil0 _ => fun devil : False => False_ind IDProp devil
| cons0 _ h n t0 t1 => H h n (t0;t1)
end)
     : forall {A : Prop} (P : forall n : nat, llist A (S n) -> Prop),
       (forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) ->
       forall {n : nat} (v : llist A (S n)), P n v.

Definition caseS_l := 
(fun (A : Type) (P : forall n : nat, llist A (S n) -> Prop)
  (H : forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) 
  (n : nat) (v : llist A (S n)) =>
match v.2  
with
| nil0 _ => fun devil : False => False_ind IDProp devil
| cons0 _ h n t0 t1 => H h n (t0;t1)
end)
     : forall {A : Prop} (P : forall n : nat, llist A (S n) -> Prop),
       (forall (h : A) (n : nat) (t : llist A n), P n (cons_l A h n t)) ->
       forall {n : nat} (v : llist A (S n)), P n v.




Definition nth {A : Type} : forall (m : nat), t A m -> Fin.t m -> A :=
fix nth_fix (m : nat) (v' : t A m) (p : Fin.t m) {struct v'} : A :=
  match p in (Fin.t m') return (t A m' -> A) with
  | @Fin.F1 n => caseS (fun (n0 : nat) (_ : t A (S n0)) => A) (fun (h : A) (n0 : nat) (_ : t A n0) => h)
  | @Fin.FS n p' =>
      fun v : t A (S n) =>
      caseS (fun (n0 : nat) (_ : t A (S n0)) => Fin.t n0 -> A)
        (fun (_ : A) (n0 : nat) (t : t A n0) (p0 : Fin.t n0) => nth_fix n0 t p0) v p'
  end v'.

Definition nth_l {A:Prop} : forall (m : nat), llist A m -> Fin.t m -> A := fun n (v:llist A n) =>
(fix nth_fix (m:nat) l (v' : IsVect A m l) (p : Fin.t m) {struct v'} : A :=
match p in Fin.t m' return forall x,  IsVect A m' x -> A with
 |Fin.F1 => fun X Y => caseS_l (fun n v' => A) (fun h n t => h) (X;Y)
 |Fin.FS p' => fun v1 v2 => (caseS_l (fun n v' => Fin.t n -> A)
   (fun h n t p0 => nth_fix n t.1 t.2 p0) (v1;v2)) p'
end l v') n v.1 v.2.

Extraction Language Ocaml.

Extraction llist. 

