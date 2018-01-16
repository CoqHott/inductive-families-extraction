Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Vectors.Vector.
Require Import ZArith.

(* * The Bad *)

Inductive Bush (A : Type): Type :=
| leaf : A -> Bush A
| node : Bush (A * A) -> Bush A.


(** Ralf Hinze PNS "Numerical Representations as Higher-Order Nested Datatypes" *)

Inductive Node23 (T A: Type): Type :=
| Node2 : T -> A -> T -> Node23 T A
| Node3 : T -> A -> T -> A -> T -> Node23 T A.

Inductive Tree23 (T A: Type): Type := 
| Zero : T -> Tree23 T A
| Succ : Tree23 (Node23 T A) A -> Tree23 T A.

Arguments Zero {_}{_} a.
Arguments Succ {_}{_} t.

Definition TREE23 := Tree23 unit.

Example t : TREE23 nat :=
  Succ
    (Succ 
       (Succ
          (Zero
             (Node2
                (Node2
                   (Node3 tt 1 tt 2 tt)
                   3
                   (Node3 tt 4 tt 5 tt))
                6
                (Node3 
                   (Node2 tt 7 tt)
                   8
                   (Node2 tt 9 tt)
                   10
                   (Node3 tt 11 tt 12 tt)))))).


Inductive Node23' (T : Type -> Type)(A : Type) :=
| Node2' : T A -> A -> T A -> Node23' T A
| Node3' : T A -> A -> T A -> A -> T A -> Node23' T A.

Definition unit' (A : Type) := unit.

Inductive Tree23' (T : Type -> Type)(A : Type) :=
| Zero' : T A -> Tree23' T A
| Succ' : Tree23' (Node23' T) A -> Tree23' T A.

Definition TREE23' := Tree23' unit'.


Example t' : TREE23' nat :=
  Succ'
    (Succ' 
       (Succ'
          (Zero'
             (Node2'
                (Node2'
                   (Node3' tt 1 tt 2 tt)
                   3
                   (Node3' tt 4 tt 5 tt))
                6
                (Node3' 
                   (Node2' tt 7 tt)
                   8
                   (Node2' tt 9 tt)
                   10
                   (Node3' tt 11 tt 12 tt)))))).


(* * The Ugly *)

Inductive BushV (A: Type): nat -> Type :=
| leafV: forall n, Vector.t A n -> BushV A n
| nodeV: forall n, BushV A (2 * n) -> BushV A n.

(* This should work because [N.to_nat] is an embedding *)
Inductive BushV' (A: Type): nat -> Type :=
| leafV': forall n, Vector.t A n -> BushV' A n
| nodeV': forall n, BushV A (N.to_nat (N.shiftl n 1)) -> BushV' A (N.to_nat n).

(* From 'Equations, reloaded", Sozeau & Mangin *)

Definition IsNZ (z: Z): Prop := (z <> 0)%Z.

Inductive poly : bool -> nat -> Type :=
| poly_z : poly true O
| poly_c z : IsNZ z -> poly false O
| poly_l {n b}(Q : poly b n) : poly b (S n)
| poly_s {n b}(P : poly b n)(Q : poly false (S n)) : poly false (S n).

Inductive mono : nat -> Type :=
| mono_z : mono O
| mono_l {n} : mono n -> mono (S n)
| mono_s {n} : mono (S n) -> mono (S n).

Fixpoint get_coef {n}(m: mono n): forall {b}, poly b n -> Z :=
  match m with
  | mono_z =>
    fun b (p: poly b 0) =>
      match p in poly _ n return match n with O => Z | S _ => unit end with
      | poly_z => 0%Z
      | @poly_c z nz => z
      | poly_l Q => tt
      | poly_s P Q => tt
      end
  | mono_l m =>
    fun b p =>
      match p in poly _ n
            return match n with
                   | 0 => unit
                   | S n => (forall b, poly b n -> Z) -> Z
                   end
      with
      | poly_z => tt
      | poly_c nz => tt
      | poly_l Q => fun k => k _ Q
      | poly_s P Q => fun k => k _ P
      end (@get_coef _ m)
  | mono_s m =>
    fun b p =>
      match p in poly _ n
            return match n with
                   | 0 => unit
                   | S n => (forall b, poly b (S n) -> Z) -> Z
                   end
      with
      | poly_z => tt
      | poly_c nz => tt
      | poly_l Q => fun k => 0%Z
      | poly_s P Q => fun k => k _ Q
      end (@get_coef _ m)
  end.

Record sig (A: Type)(B: A -> Type): Type :=
  ex { proj1: A; proj2: B proj1 }.

Notation "a ; b" := (@ex _ _ a b) (at level 50).

Definition transport {A: Type} (P: A -> Type) {x y: A} 
    (p: x = y) (u: P x): P y :=
  match p with eq_refl => u end.
Notation "p # x" := (transport p x)
                      (right associativity, at level 65, only parsing).

Definition ap {A B: Type} (f: A -> B) {x y: A} : x = y -> f x = f y.
  exact (fun p => match p with eq_refl => eq_refl end).
Defined.

Lemma ap2 {A B C} : forall (f: A -> B -> C), forall a1 a2 b1 b2 (q : a1 = a2)(qb : b1 = b2), f a1 b1 = f a2 b2.
Proof.
  intros; induction q; induction qb; auto.
Defined.


Definition sig_path {A}{B : A -> Type} {u v : sig B}(q : v.(proj1) = u.(proj1))(p : u.(proj2) = transport (P := fun x => B (x)) q v.(proj2)): u = v.
  destruct u, v. simpl in *. destruct q. simpl in *. destruct p. auto.
Defined.

Definition proj1_path {A} {B : A -> Type} {u v : sig B} (p : u = v): u.(proj1) = v.(proj1) :=
  ap (fun x => x.(proj1)) p.

Notation "p ..1" := (proj1_path p) (at level 3).

Definition proj2_path {A} {B : A -> Type} {u v : sig B} (p : u = v): p..1 # u.(proj2) = v.(proj2) := match p with eq_refl => eq_refl end.


Lemma uip_nat {n : nat}: forall (q: n = n), q = eq_refl.
Admitted. (* from Hedberg *)

Lemma uip_bool {b : bool}: forall (q: b = b), q = eq_refl.
Admitted. (* from Hedberg *)

Lemma uip_Z {b : Z}: forall (q: b = b), q = eq_refl.
Admitted. (* from Hedberg *)

Axiom HProp_Prop : forall {P : Prop} (p q: P), p = q.
(* assuming proof irrelevance of Prop *)


Lemma transp_refl {b n}: forall (q: n = n) (p: poly b n), transport q p = p.
Proof.
intros q p. rewrite (uip_nat q). auto.
Qed.

Definition S_inj {m n}: S m = S n -> m = n.
Proof.
intro q. inversion q. reflexivity.
Defined.

Lemma transp_S {b m n}: forall (q: S m = S n) (p: poly b m), transport q (poly_l p) = poly_l (transport (S_inj q) p).
Proof.
inversion q. subst. rewrite (uip_nat q). simpl. auto.
Defined.

Lemma transp_S_poly_s {b m n}: forall (Q: S m = S n) (p: poly b m)(q: poly false (S m)),
    transport Q (poly_s p q) = poly_s (transport (S_inj Q) p) (transport Q q).
Proof.
inversion Q. subst. rewrite (uip_nat Q). simpl. auto.
Defined.


Fixpoint mL {n} (p : poly false n): mono n :=
  match p in poly b n
        return match b with
               | false => mono n
               | true => unit 
               end
  with
  | poly_z => tt
  | poly_c nz => mono_z
  | @poly_l _ b q => 
    match b return forall n, poly b n -> if b then unit else mono (S n) with true => fun _ _ => tt | false => fun n q => mono_l (mL q) end _ q
  | poly_s p q => mono_s (mL q)
  end.

Lemma get_coef_mL {b n}: forall (p: poly b n)(q : b = false), IsNZ (get_coef (mL (transport (P := fun b => poly b n) q p)) p).
Proof.
intros p q.
induction p; simpl; try solve [inversion q]; auto.
- rewrite (uip_bool q); auto.
- destruct b; try solve [inversion q]. 
  rewrite (uip_bool q); auto. 
  apply (IHp eq_refl).
- rewrite (uip_bool q).
  apply (IHp2 eq_refl).
Qed.

Lemma get_coef_eq_1 {n n'} b1 b2 (p1: poly b1 n)(p2: poly b2 n')(q: n' = n):
  (forall (m: mono n), get_coef m p1 = get_coef m (transport q p2)) ->
  (b1 ; p1) = (b2 ; transport (P := fun n => poly b2 n) q p2) :> @sig bool (fun b => poly b n).
Proof.
generalize dependent n'. generalize dependent b2.
induction p1; intros b2 n' p2.
- destruct p2; intros q H; try solve [inversion q].
  + rewrite transp_refl.
    reflexivity.
  + rewrite transp_refl in H.
    specialize (H mono_z).
    simpl in H. subst.
    contradiction.
- destruct p2; intros q H; try solve [inversion q].
  + rewrite transp_refl in H.
    specialize (H mono_z).
    contradiction.
  + rewrite transp_refl in *.
    specialize (H mono_z).
    simpl in H. subst.
    assert (i = i0) as <- by apply HProp_Prop.
    reflexivity.
- destruct p2; intros q H; try solve [inversion q].
  + rewrite transp_S.
    assert ((b ; p1) = (b0 ; transport (P := poly b0)(S_inj q) p2) :> @sig bool (fun b => poly b n)).
    {
      apply IHp1. intros.
      specialize (H (mono_l m)).
      simpl in H.
      rewrite transp_S in H. assumption.
    }
    inversion H0. induction H2.
    destruct H3.
    reflexivity.
  + exfalso.
    rewrite transp_S_poly_s in H.
    specialize (H (mono_s (mL (transport q p2_2)))).
    replace (get_coef (mono_s (mL _)) (poly_l p1)) with 0%Z in H; [|compute; auto].
    replace (get_coef (mono_s (mL _)) (poly_s (transport (S_inj q) p2_1) (transport q p2_2))) with (get_coef (mL (transport q p2_2)) (transport q p2_2)) in H; [|compute;auto].

    pose proof (@get_coef_mL _ _ (transport (P := poly false) q p2_2)).
    specialize (H0 eq_refl). simpl in *.
    rewrite <- H in H0.
    contradiction.
- destruct p2; intros q H; try solve [inversion q].
  + exfalso.
    rewrite transp_S in H.
    specialize (H (mono_s (mL p1_2))).
    replace (get_coef (mono_s (mL _)) (poly_l _)) with 0%Z in H; [|compute; auto].
    replace (get_coef (mono_s (mL _)) (poly_s p1_1 p1_2)) with (get_coef (mL p1_2) p1_2) in H; [|compute;auto].

    pose proof (@get_coef_mL _ _ p1_2).
    specialize (H0 eq_refl). simpl in *.
    rewrite H in H0.
    contradiction.
  + rewrite transp_S_poly_s in * |- *.
    assert ((b ; p1_1) = (b0 ; transport (P := poly b0) (S_inj q) p2_1) :> @sig bool (fun b => poly b n)).
    {
      apply IHp1_1.
      intros.
      apply (H (mono_l m)).
    }
    assert ((false; p1_2) = (false; transport (P := poly false) q p2_2) :> @sig bool (fun b => poly b (S n))).
    {
      apply IHp1_2.
      intros.
      apply (H (mono_s m)).
    }
    pose proof (@sig_path bool (fun b => poly b (S n)) (false; poly_s p1_1 p1_2) (false; poly_s (transport (S_inj q) p2_1) (transport q p2_2)) eq_refl).
    apply H2.
    simpl.
    set (x1 := ((b ; p1_1 : @sig bool (fun b => poly b n)))).
    set (y1 := ((b0 ; transport (P := poly b0) (S_inj q) p2_1 : @sig bool (fun b => poly b n)))).
    set (x2 := p1_2).
    set (y2 := transport (P := poly _) q p2_2).
    pose proof (ap2 (fun u v => poly_s u.(proj2) v)
                       (a1 := x1)(a2 := y1)
                       (b1 := x2)(b2 := y2)).
    apply H3. subst x1 y1; auto.
    subst x2 y2.
    pose proof (proj2_path H1).
    simpl in *.
    assert (H1 ..1 = eq_refl) by apply uip_bool.
    rewrite H5 in H4. simpl in *. auto.
Qed.

Fixpoint eval {n b} (p: poly b n): Vector.t Z n -> Z :=
  match p with
  | poly_z =>
    fun (v: Vector.t Z 0) =>
      match v in Vector.t _ n
            return match n with 0 => Z | S _ => unit end
      with
      | nil _ => 0%Z
      | cons _ _ _ _ => tt
      end
  | @poly_c z nz =>
    fun (v: Vector.t Z 0) =>
      match v in Vector.t _ n
            return match n with 0 => Z | S _ => unit end
      with
      | nil _ => z
      | cons _ _ _ _ => tt
            end
  | poly_l Q =>
    fun v =>
      match v in Vector.t _ n
            return match n with
                   | 0 => unit
                   | S n => (Vector.t Z n -> Z) -> Z
                   end
      with
      | nil _ => tt
      | cons _ _ _ xs => fun k => k xs
      end (@eval _ _ Q)
  | poly_s P Q =>
    fun v =>
      match v in Vector.t _ n
            return match n with
                   | 0 => unit
                   | S n => (Vector.t Z n -> Z) -> (Vector.t Z (S n) -> Z) -> Z
                         end
      with
      | nil _ => tt
      | cons _ y _ ys => fun kP kQ => (kP ys + y * kQ (cons _ y _ ys))%Z
      end (@eval _ _ P) (@eval _ _ Q)
  end.

Lemma polyz_eval {n} (p : poly true n) (v: Vector.t Z n) : eval p v = 0%Z.
Proof.
remember true as b eqn:Hb.
induction p; try solve [inversion Hb].
- case v using case0.
  auto.
- unshelve eapply (@caseS _ (fun n' v => forall p' (q: n = n') , transport q p = p' -> eval (poly_l p') v = 0%Z) _  n v p).
  + simpl. intros. 
    destruct q.
    simpl in *.
    destruct H.
    apply IHp. auto. 
  + auto.
  + auto.
Qed.  


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
Axiom vec_JMEq: forall {m} (xs : vec m) (P : forall {k}, vec k -> Type), P xs -> forall {n} (ys : vec n), m = n -> val_vec xs = val_vec ys -> P ys. 

Axiom val_vec_vnil: val_vec vnil = nil.
Axiom val_vec_vcons: forall n (a : A) (xs: vec n), val_vec (vcons a xs) = cons a (val_vec xs).

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

Definition val_cat {n m} (t: vec n)(u: vec m): list := val_vec (cat t u).
Arguments val_cat /.

Lemma val_cat_vnil: forall n (xs: vec n), val_cat vnil xs = val_vec xs.
Proof. reflexivity. Qed.

Lemma val_cat_vcons: forall m n x (t: vec n)(u : vec m), val_cat (vcons x t) u = cons x (val_cat t u).
Proof. intros; unfold val_cat; simpl. rewrite val_vec_vcons. reflexivity. Qed.


Lemma cat0s n (s: vec n) : cat vnil s = s.
Proof. reflexivity. Qed.
Lemma cat1s n x (s: vec n) : cat (vcons x vnil) s = vcons x s.
Proof. reflexivity. Qed.
Lemma cat_cons m n x (s1: vec m)(s2: vec n) : cat (vcons x s1) s2 = vcons x (cat s1 s2).
Proof. reflexivity. Qed.

Lemma cat_nseq m n x (s: vec m) : cat (nseq n x) s = ncons n x s.
Proof. induction n; auto; simpl. rewrite IHn; auto. Qed.

(* FAILED(heterogeneity): [m + 0 != m] *)
Fail Lemma cats0 n (s: vec n) : cat s vnil = s.

Lemma val_cats0 n (s: vec n) : val_cat s vnil = val_vec s.
Proof.
induction s; auto. 
simpl in *; rewrite !val_vec_vcons; congruence.
Qed.

(* FAILED(heterogeneity): [(m + n) + o != m + (n + o)] *)
Fail Lemma catA m n o (s1: vec m)(s2: vec n)(s3: vec o) :
  cat s1 (cat s2 s3) = cat (cat s1 s2) s3.

Lemma val_catA m n o (s1: vec m)(s2: vec n)(s3: vec o) :
  val_cat s1 (cat s2 s3) = val_cat (cat s1 s2) s3.
Proof.
induction s1; auto.
simpl in *. rewrite !val_vec_vcons. congruence. 
Qed.

(* last, belast, rcons, and last induction. *)

Fixpoint rcons {n} (s: vec n)(z: A): vec (S n) :=
  match s with
  | vcons x s' => vcons x (rcons s' z)
  | vnil => vcons z vnil
  end.

Definition val_rcons  {n} (s: vec n)(z: A): list := val_vec (rcons s z).
Arguments val_rcons /.

Lemma val_rcons_vcons : forall n (s: vec n) x z, 
    val_rcons (vcons x s) z = cons x (val_rcons s z).
Proof. intros; simpl; rewrite !val_vec_vcons; reflexivity. Qed.

Lemma val_rcons_vnil : forall n (s: vec n) z, 
    val_rcons vnil z = cons z nil.
Proof. intros; simpl; rewrite !val_vec_vcons, !val_vec_vnil; reflexivity. Qed.

Lemma rcons_cons n x (s: vec n) z : rcons (vcons x s) z = vcons x (rcons s z).
Proof. reflexivity. Qed.

(* FAILED(heterogeneity): [S n != n + 1] *)
Fail Lemma cats1 n (s: vec n) z : cat s (vcons z vnil) = rcons s z.

Lemma val_cats1 n (s: vec n) z : val_cat s (vcons z vnil) = val_rcons s z.
Proof.
induction s.
- auto.
- rewrite val_cat_vcons, val_rcons_vcons; congruence.
Qed.


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

(* FAILED(heterogeneity): [m + S n != S m + n] *)
Fail Lemma cat_rcons m n x (s1: vec m)(s2: vec n) : cat (rcons s1 x) s2 = cat s1 (vcons x s2).

Lemma val_cat_rcons m n x (s1: vec m)(s2: vec n) : val_cat (rcons s1 x) s2 = val_cat s1 (vcons x s2).
Proof.
(* XXX: How could I exploit the following lemmas: *)
Check val_cats1.
Check val_catA.
(* rewrite -cats1 -catA.  *)
Abort.

(* FAILED(heterogeneity): [m + S n != S (m + n)] *)
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

(* FAILED(heterogeneity): [m + n != n + m] *)
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

(* FAILED(heterogeneity): [Nat.min n n != n] *)
Fail Lemma zip_unzip s : zip (unzip1 s) (unzip2 s) = s.

Lemma zip_unzip n (s: vec (A * B) n) : zip' (unzip1 s) (unzip2 s) = s.
Proof.
  induction s; auto; simpl. unfold unzip1, unzip2 in IHs.
  rewrite IHs. rewrite <- surjective_pairing. auto.
Qed.

(* FAILED(heterogeneity): [Nat.min m n !== m] under [m <= n] *)
Fail Lemma unzip1_zip m n (s: vec A m)(t: vec B n) : m <= n -> unzip1 (zip s t) = s.

(* FAILED(heterogeneity): [Nat.min m n !== n] under [n <= m] *)
Fail Lemma unzip2_zip m n (s: vec A m)(t: vec B n) : m <= n -> unzip2 (zip s t) = t.

(* FAILED(heterogeneity): [Nat.min m m + Nat.min k l != Nat.min (m + k) (m + l)] *)
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

(* FAILED(heterogeneity): [m * k + n * k != (m + n) * k] *)
Fail Lemma allpairs_cat m n (f: A -> B -> C) (s1: vec A m)(s2: vec A n) t :
  allpairs f (cat s1 s2) t = cat (allpairs f s1 t) (allpairs f s2 t).


End PolyTuple2.

(* TODO: implement [nth], [rot], [rotr] *)
