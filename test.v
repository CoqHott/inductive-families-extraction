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
                 
Definition llist A n := {l : list A & IsVect A n l}. 

Definition cons_l : forall A , A -> forall n : nat, llist A n -> llist A (S n) :=
  fun A x n l => (cons x (l.1) ; l.2).

Definition nil_l : forall A , llist A 0 :=
  fun A => (nil ; I).

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

Extraction llist_rect.

Definition caseS : forall {A : Type} (P : forall n : nat, t A (S n) -> Type),
    (forall (h : A) (n : nat) (t : t A n), P n (Vector.cons A h n t)) ->
    forall {n : nat} (v : t A (S n)), P n v :=
  fun (A : Type) (P : forall n : nat, t A (S n) -> Type)
      (H : forall (h : A) (n : nat) (t : t A n), P n (Vector.cons A h n t))
      (n : nat) (v : t A (S n)) =>
    let Q n0 v0 := match n0 as x return (t A x -> Type) with
       | 0 => fun _ : t A 0 => False -> IDProp
       | S n1 => fun v1 : t A (S n1) => P n1 v1
       end v0 in
    match
      v as v0 in (t _ n0) return
      Q n0 v0
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
    | nil, 0 => fun i => match i with I => fun (devil : False) => False_ind IDProp devil end
    | nil, S _ => fun i => match i with end
    | cons h t0, S n0 => fun i => H h n0 (t0;i)
    | cons h t0, 0 => fun i => match i with end
    end v.2.

Definition nth {A : Type} : forall (m : nat), t A m -> Fin.t m -> A :=
fix nth_fix (m : nat) (v' : t A m) (p : Fin.t m) {struct v'} : A :=
  match p in (Fin.t m') return (t A m' -> A) with
  | @Fin.F1 n => caseS (fun (n0 : nat) (_ : t A (S n0)) => A) (fun (h : A) (n0 : nat) (_ : t A n0) => h)
  | @Fin.FS n p' =>
      fun v : t A (S n) =>
      caseS (fun (n0 : nat) (_ : t A (S n0)) => Fin.t n0 -> A)
        (fun (_ : A) (n0 : nat) (t : t A n0) (p0 : Fin.t n0) => nth_fix n0 t p0) v p'
  end v'.

Definition nth_l {A:Type} : forall (m : nat), llist A m -> Fin.t m -> A :=
  fun m X => 
(fix nth_fix (m : nat) (v' : list A) (H : IsVect A m v') (p : Fin.t m) {struct v'} : A :=
  match p in (Fin.t m') return (forall (v' : list A) (H : IsVect A m' v'), A) with
  | @Fin.F1 n => fun X Y => caseS_l (fun (n0 : nat) (_ : llist A (S n0)) => A) (fun (h : A) (n0 : nat) (_ : llist A n0) => h) (X;Y)
  | @Fin.FS n p' =>
      fun X Y => 
      caseS_l (fun (n0 : nat) (_ : llist A (S n0)) => Fin.t n0 -> A)
        (fun (_ : A) (n0 : nat) (t : llist A n0) (p0 : Fin.t n0) => nth_fix n0 t.1 t.2 p0) (X;Y) p'
  end v' H) m X.1 X.2.


Extraction Language Ocaml.

Extraction caseS_l. 

Extraction nth_l. 

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (Vector.cons _ h _ t)), P v :=
  match v with
  | Vector.cons _ h _ t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

Definition caseS'_l {A} {n : nat} (v : llist A (S n)) : forall (P : llist A (S n) -> Type)
                                                               (H : forall h t, P (cons_l _ h _ t)), P v :=
  let Q n0 v0 := (match n0 as x return (llist A x -> Type) with
     | 0 => fun _ : llist A 0 => False -> IDProp
     | S n1 =>
         fun v1 : llist A (S n1) => forall P : llist A (S n1) -> Type, (forall (h : A) (t : llist A n1), P (cons_l A h n1 t)) -> P v1
   end v0) in 
  match v.1 as l0 , S n as n0
  return forall H0 : IsVect A n0 l0, Q n0 (l0;H0)
  with
  | h :: t, S m => fun i P H => H h (t;i)
  | h :: t, 0 => fun i => match i with end                                     
  | nil , 0 => fun i devil => False_rect (@IDProp) devil
  | nil , S _ => fun i => match i with end                                     
  end v.2.

Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => Vector.cons _ a _ t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => Vector.cons _ h _ (replace t p' a)))
  end v.

Fixpoint replace_l {A n} (v : llist A n) (p: Fin.t n) (a : A) {struct p}: llist A n :=
  match p with
  | @Fin.F1 k => fun (l : list A) (H : IsVect A (S k) l) => caseS'_l (l;H) _ (fun h t => cons_l _ a _ t)
  | @Fin.FS k p' => fun (l : list A) (H : IsVect A (S k) l) => 
    (caseS'_l (l;H) (fun _ => llist A (S k)) (fun h t => cons_l _ h _ (replace_l t p' a)))
  end v.1 v.2.

Require Import Arith_base.

Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p := 
  match p as p return p <= n -> t A p with 
  | 0 => fun _ => Vector.nil _ 
  | S p' => match v in t _ n return S p' <= n -> t A (S p') with
    | Vector.nil _=> fun le => False_rect _ (Nat.nle_succ_0 p' le)
    | Vector.cons _ x _ xs => fun le => Vector.cons _ x _ (take p' (le_S_n p' _ le) xs)
    end 
  end le.

Fixpoint take_l {A} {n} (p:nat) (le:p <= n) (v:llist A n) : llist A p := 
  match p as p return p <= n -> llist A p with 
  | 0 => fun _ => nil_l _ 
  | S p' => match v.1 as l0, n as n0 return forall H0 : IsVect A n0 l0, S p' <= n0 -> llist A (S p') with
    | nil, 0 => fun i le => False_rect _ (Nat.nle_succ_0 p' le)
    | nil, S _ => fun i le => match i with end
    | cons x xs, S _ => fun i le => cons_l _ x _ (take_l p' (le_S_n p' _ le) (xs;i))
    | cons _ _ , 0 => fun i le => match i with end
    end v.2
  end le.
