Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Vectors.Vector.
Require Import ZArith.

(* * The Bad *)

Inductive Bush (A : Type): Type :=
| leaf : A -> Bush A
| node : Bush (A * A) -> Bush A.

(** TODO: Ralf Hinze PNS "Numerical Representations as Higher-Order Nested Datatypes" *)

(* * The Ugly *)

Inductive BushV (A: Type): nat -> Type :=
| leafV: forall n, Vector.t A n -> BushV A n
| nodeV: forall n, BushV A (2 * n) -> BushV A n.

(* This should work because [N.to_nat] is an embedding *)
Inductive BushV' (A: Type): nat -> Type :=
| leafV': forall n, Vector.t A n -> BushV' A n
| nodeV': forall n, BushV A (N.to_nat (N.shiftl n 1)) -> BushV' A (N.to_nat n).

(* * The Good ? *)

(* ** SSR's tuple *)

Section Tuple.

Variable (A: Type).

Inductive list: Type :=
| nil: list
| cons: A -> list -> list.

Inductive vec: nat -> Type :=
| vnil: vec 0
| vcons: forall {n}, A -> vec n -> vec (S n).

(* XXX: this follows from hprop-ness: *)
Axiom val_vec: forall {n}, vec n -> list.
Axiom vec_inj: forall {n} (xs ys: vec n), val_vec xs = val_vec ys -> xs = ys. 

(* *** Definitions & Specifications *)

Fixpoint behead {n}(t: vec (S n)): vec n :=
  match t with
  | vcons x t => t
  end.

(* Factories *)

Fixpoint ncons {m} n x (xs: vec m): vec (n+m) :=
  match n with
  | 0 => xs
  | S n => vcons x (ncons n x xs)
  end.

(* FAILED(compositionality): [n + 0 != n] *)
Fail Definition nseq n x: vec n := ncons n x vnil.

Fixpoint nseq (n: nat)(x: A): vec n :=
  match n with
  | 0 => vnil
  | S n => vcons x (nseq n x)
  end.

(* Sequence catenation "cat". *)

Fixpoint cat {n m} (t: vec n): vec m -> vec (n+m) :=
  match t in vec n return vec m -> vec (n+m) with
  | vnil => fun u => u
  | vcons x t => fun u => vcons x (cat t u)
  end.

Lemma cat0s n (s: vec n) : cat vnil s = s.
Proof. reflexivity. Qed.
Lemma cat1s n x (s: vec n) : cat (vcons x vnil) s = vcons x s.
Proof. reflexivity. Qed.
Lemma cat_cons m n x (s1: vec m)(s2: vec n) : cat (vcons x s1) s2 = vcons x (cat s1 s2).
Proof. reflexivity. Qed.

Lemma cat_nseq m n x (s: vec m) : cat (nseq n x) s = ncons n x s.
Proof. induction n; auto; simpl. rewrite IHn; auto. Qed.

(* FAILED(statement): [m + 0 != m] *)
Fail Lemma cats0 n (s: vec n) : cat s vnil = s.

(* FAILED(statement): [(m + n) + o != m + (n + o)] *)
Fail Lemma catA m n o (s1: vec m)(s2: vec n)(s3: vec o) :
  cat s1 (cat s2 s3) = cat (cat s1 s2) s3.

(* last, belast, rcons, and last induction. *)

Fixpoint rcons {n} (s: vec n)(z: A): vec (S n) :=
  match s with
  | vcons x s' => vcons x (rcons s' z)
  | vnil => vcons z vnil
  end.

Lemma rcons_cons n x (s: vec n) z : rcons (vcons x s) z = vcons x (rcons s z).
Proof. reflexivity. Qed.

(* FAILED(statement): [S n != n + 1] *)
Fail Lemma cats1 n (s: vec n) z : cat s (vcons z vnil) = rcons s z.

Fixpoint last' {n} (a: A)(t: vec n) : A :=
  match t with
  | vnil => a
  | vcons a xs => last' a xs
  end.

Definition last {n}(t: vec (S n)): A :=
  match t with
  | vcons a xs => last' a xs
  end.

Fixpoint belast {n}(x: A)(t: vec n): vec n :=
  match t in vec n return vec n with
  | vcons x' t => vcons x (belast x' t)
  | vnil => vnil
  end.

Lemma lastI n x (s: vec n) : vcons x s = rcons (belast x s) (last' x s).
Proof.
generalize x. induction s; intros; auto.
simpl. rewrite IHs at 1. auto.
Qed.

Lemma last_cons n x y (s: vec n) : last' x (vcons y s) = last' y s.
Proof. reflexivity. Qed.

Lemma last_cat m n x (s1: vec m)(s2: vec n) : last' x (cat s1 s2) = last' (last' x s1) s2.
Proof.
generalize x.
induction s1; intros; auto; simpl.
rewrite IHs1. auto.
Qed.

(* FAILED(rewriting): [rcons s x !== cat s (vcons x vnil)] *)
Lemma last_rcons n x (s: vec n) z : last' x (rcons s z) = z.
Proof. generalize x; induction s; intros; auto; simpl. rewrite IHs. auto. Qed.
(* by rewrite -cats1 last_cat. *)

Lemma belast_cat m n x (s1: vec m)(s2: vec n) :
  belast x (cat s1 s2) = cat (belast x s1) (belast (last' x s1) s2).
Proof. generalize x. induction s1; intros; auto; simpl. rewrite IHs1; auto. Qed.

Lemma belast_rcons n x (s: vec n) z : belast x (rcons s z) = vcons x s.
Proof.
  generalize x. induction s; auto. intro. rewrite rcons_cons. simpl; rewrite IHs. auto.
Qed.

(* FAILED(statement): [m + S n != S m + n] *)
Fail Lemma cat_rcons m n x (s1: vec m)(s2: vec n) : cat (rcons s1 x) s2 = cat s1 (vcons x s2).

(* FAILED(statement): [m + S n != S (m + n)] *)
Fail Lemma rcons_cat m n x (s1: vec m)(s2: vec n) : rcons (cat s1 s2) x = cat s1 (rcons s2 x).

CoInductive last_spec : forall n, vec n -> Type :=
  | LastNil        : last_spec vnil
  | LastRcons n (s: vec n) x  : last_spec (rcons s x).

Lemma lastP n (s: vec n) : last_spec s.
Proof. case s; [ left | ]. intros; rewrite lastI; constructor. Qed.


Lemma last_ind (P: forall n, vec n -> Type) :
  P _ vnil -> (forall n (s: vec n) x, P _ s -> P _ (rcons s x)) -> forall n (s: vec n), P _ s.
Proof.
intros Hnil Hlast n s.
rewrite <-(cat0s s).
Admitted.
(* XXX: the generalization is not sufficient in the dependently-typed case *)
(*
elim: s [::] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
by rewrite -cat_rcons; auto.
Qed. *)

(* Surgery: drop, take, rot, rotr.                                        *)

(* FAILED(typing): [n - 0 != n] *)
Fail Fixpoint drop {n} (m: nat): vec n -> vec (n - m) :=
  match m return vec n -> vec (n - m) with
  | 0 => fun t => t
  | S n => fun t => match t with
                | vnil => vnil
                | vcons s t => drop n t
                end
  end.

(* FAILED(typing): [Nat.min m 0 !== 0] *)
Fail Fixpoint take {n} (m: nat)(t: vec n) {struct t}: vec (Nat.min m n) :=
  match t, n with
  | vcons x s', S n => vcons x (take n s')
  | _, _ => vnil
  end.

(* reversal *)

(* FAILED(typing): [n + 0 != n] *)
Fail Fixpoint catrev {m}{n} (s1: vec m)(s2: vec n): vec (n + m)  :=
  match s1 with
  | vcons x s1' => catrev s1' (vcons x s2)
  | vnil => s2
  end.
Fail Definition rev {n} (s : vec n) := catrev s vnil.

(* XXX: inefficient implementation *)
Fixpoint rev {n} (t: vec n): vec n :=
  match t with
  | vnil => vnil
  | vcons x xs => rcons (rev xs) x
  end.

Lemma rev_cons n x (s: vec n) : rev (vcons x s) = rcons (rev s) x.
Proof. reflexivity. (* works because of inefficient implem *) Qed.

(* FAILED(statement): [m + n != n + m] *)
Fail Lemma rev_cat m n (s: vec m)(t: vec n) : rev (cat s t) = cat (rev t) (rev s).

Lemma rev_rcons n (s: vec n) x : rev (rcons s x) = vcons x (rev s).
Proof. induction s; auto; simpl. rewrite IHs. auto. Qed.

End Tuple.

Section PolyTuple.

Variable (A B C: Type).

Fixpoint map {n} (f: A -> B)(t: vec A n): vec B n :=
  match t with
  | vnil _ => vnil _
  | vcons x xs => vcons (f x) (map f xs)
  end.

Lemma map_cons n (f: A -> B) x (s: vec A n) : map f (vcons x s) = vcons (f x) (map f s).
Proof. reflexivity. Qed.

Lemma map_nseq (f: A -> B) n0 x : map f (nseq n0 x) = nseq n0 (f x).
Proof. induction n0; auto; simpl. rewrite IHn0. auto. Qed.

Lemma map_cat m n (f : A -> B) (s1: vec A m)(s2: vec A n) : map f (cat s1 s2) = cat (map f s1) (map f s2).
Proof. induction s1; auto; simpl. rewrite IHs1. auto. Qed.

(* XXX: Painful (inversion of [vec A (S n)] *)
Lemma behead_map n (f: A -> B) (s: vec A (S n)) : behead (map f s) = map f (behead s).
Admitted.

(* FAILED(rewriting): [rcons s x != cat s (vcons x vnil)] *)
Lemma map_rcons n (f: A -> B) (s: vec A n) x : map f (rcons s x) = rcons (map f s) (f x).
Proof. induction s; auto; simpl. rewrite IHs. auto. Qed.

Lemma last_map n (f: A -> B)(s: vec A n) x : last' (f x) (map f s) = f (last' x s).
Proof. generalize x. induction s; auto; simpl; intros. rewrite IHs. auto. Qed.

Lemma belast_map n (f: A -> B)(s: vec A n) x : belast (f x) (map f s) = map f (belast x s).
Proof. generalize x. induction s; auto; simpl; intros. rewrite IHs. auto. Qed.

Lemma map_rev n (f: A -> B)(s: vec A n) : map f (rev s) = rev (map f s).
Proof.
  induction s; auto; simpl; intros.
  rewrite map_rcons. rewrite IHs. auto.
Qed.

Fixpoint pairmap {n} (f: A -> A -> A)(a : A)(t: vec A n): vec A n :=
  match t with
  | vnil _ => vnil _
  | vcons x xs => vcons (f a x) (pairmap f x xs)
  end.

Lemma pairmap_cat m n (f: A -> A -> A) x (s1: vec A m)(s2: vec A n) :
  pairmap f x (cat s1 s2) = cat (pairmap f x s1) (pairmap f (last' x s1) s2).
Proof. generalize x. induction s1; intros; auto; simpl. rewrite IHs1. auto. Qed.

Fixpoint scanl {n} (f: A -> B -> A)(a: A)(t: vec B n): vec A n :=
  match t with
  | vnil _ => vnil _
  | vcons x xs =>
    let fx := f a x in
    vcons fx (scanl f fx xs)
  end.

End PolyTuple.

Section PolyTuple'.

Variable (A B C: Type).

Fixpoint zip {m n} (t1: vec A m)(t2: vec B n): vec (A * B) (Nat.min m n) :=
  match t1, t2 with
  | vnil _, _ => vnil _
  | _, vnil _ => vnil _
  | vcons x1 xs1, vcons x2 xs2 => vcons (x1, x2) (zip xs1 xs2)
  end.

(* XXX: this redundancy is annoying. *)
Fixpoint zip' {n} (t1: vec A n) {struct t1}: vec B n -> vec (A * B) n :=
  match t1 with
  | vnil _ => fun _ => vnil _
  | vcons x1 xs1 =>
    fun xs =>
      match xs in vec _ n
            return match n with
                   | 0 => unit
                   | S n => (vec B n -> vec (A * B) n) -> vec (A * B) (S n)
                   end with
      | vcons x2 xs2 => fun zip => vcons (x1, x2) (zip xs2)
      | vnil _ => tt
      end (zip' xs1)
  end.

Definition unzip1 n := @map _ _ n (@fst A B).
Definition unzip2 n := @map _ _ n (@snd A B).

(* FAILED(statement): [Nat.min n n != n] *)
Fail Lemma zip_unzip s : zip (unzip1 s) (unzip2 s) = s.

Lemma zip_unzip n (s: vec (A * B) n) : zip' (unzip1 s) (unzip2 s) = s.
Proof.
  induction s; auto; simpl. unfold unzip1, unzip2 in IHs.
  rewrite IHs. rewrite <- surjective_pairing. auto.
Qed.

(* FAILED(statement): [Nat.min m n !== m] under [m <= n] *)
Fail Lemma unzip1_zip m n (s: vec A m)(t: vec B n) : m <= n -> unzip1 (zip s t) = s.

(* FAILED(statement): [Nat.min m n !== n] under [n <= m] *)
Fail Lemma unzip2_zip m n (s: vec A m)(t: vec B n) : m <= n -> unzip2 (zip s t) = t.

(* FAILED(statement): [Nat.min m m + Nat.min k l != Nat.min (m + k) (m + l)] *)
Fail Lemma zip_cat m k l (s1: vec A m)(s2: vec A k)(t1: vec B m)(t2: vec B l) :
  zip (cat s1 s2) (cat t1 t2) = cat (zip s1 t1) (zip s2 t2).

(* FAILED(rewriting): [rcons x s != cat s (vcons x vnil)] *)
Lemma zip_rcons n (s1: vec A n)(s2: vec B n) z1 z2 :
  zip (rcons s1 z1) (rcons s2 z2) = rcons (zip s1 s2) (z1, z2).
Proof.
Admitted. (* XXX: looks painful *)

(* FAILED(rewriting): [rev xs != catrev xs vnil] *)
Lemma rev_zip n (s1: vec A n)(s2: vec B n) :
  rev (zip s1 s2) = zip (rev s1) (rev s2).
Proof.
generalize s2. induction s1; intros; auto.
(* XXX: do inversion on s0 *)
Admitted.
(* by rewrite !rev_cons zip_rcons ?IHs ?size_rev. *)

Fixpoint iota (m n: nat): vec nat n :=
  match n with
  | S n => vcons m (iota (S m) n)
  | 0 => vnil _
  end.

Lemma iota_add m n1 n2 : iota m (n1 + n2) = cat (iota m n1) (iota (m + n1) n2).
Proof.
generalize m. induction n1; intros; auto; simpl.
- rewrite <- plus_n_O. auto.
- rewrite IHn1.
  rewrite plus_Snm_nSm.
  auto.
Qed.

End PolyTuple'.

Section PolyTuple2.

Variable (A B C: Type).

Definition uncurry (f: A -> B -> C)(ab: A * B): C :=
  let (a, b) := ab in f a b.

Fixpoint allpairs {m n} (f: A -> B -> C)(s: vec A n)(t: vec B m): vec C (n * m) :=
  match s with
  | vnil _ => vnil _
  | vcons a s => cat (map (uncurry f) (zip' (nseq m a) t)) (allpairs f s t)
  end.

(* FAILED(statement): [m * k + n * k != (m + n) * k] *)
Fail Lemma allpairs_cat m n (f: A -> B -> C) (s1: vec A m)(s2: vec A n) t :
  allpairs f (cat s1 s2) t = cat (allpairs f s1 t) (allpairs f s2 t).


End PolyTuple2.

(* TODO: implement [nth], [rot], [rotr] *)
