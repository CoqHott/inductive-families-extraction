{-# OPTIONS --without-K #-}

open import Level renaming (zero to zeroL ; suc to sucL)

open import Function

open import Data.Empty
open import Data.Unit hiding (_≤?_ ; decTotalOrder ; _≤_ )
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.List
open import Data.List.All

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- * Structure of equality

Σ-path : ∀ {A : Set}{B : A → Set} {u v : Σ[ a ∈ A ] B a} → 
         (q : proj₁ u ≡ proj₁ v) → subst B q (proj₂ u) ≡ proj₂ v → u ≡ v
Σ-path {u = (x , y)} {(.x , .y)} refl refl = refl

Prod-path : ∀ {A B : Set}{u v : A × B} → 
            (q : proj₁ u ≡ proj₁ v) → proj₂ u ≡ proj₂ v → u ≡ v
Prod-path {u = (x , y)} {(.x , .y)} refl refl = refl

hprop-Σ : ∀ {A : Set}{B : A → Set} → {x y : Σ[ a ∈ A ] B a} →
          (q₁ : proj₁ x ≡ proj₁ y) →
          (q₂ : ∀ {x} → (b₁ b₂ : B x) → b₁ ≡ b₂) →
          subst B q₁ (proj₂ x) ≡ proj₂ y
hprop-Σ {x = (a , b)} {(.a , c)} refl q₂ with q₂ b c 
hprop-Σ {x = (a , b)} {(.a , .b)} refl q₂ | refl = refl

-- * H-propositions

postulate 
  extensionality : {A : Set}{B : A → Set}{f g : (a : A) → B a} →
                   ((x : A) → f x ≡ g x) → f ≡ g

IsHProp : Set → Set
IsHProp P = ∀ (x y : P) → x ≡ y

record HProp (P : Set) : Set where
  field
    isHProp : IsHProp P

open HProp {{...}} public

instance
  Unit-IsHProp : HProp ⊤
  isHProp {{Unit-IsHProp}} tt tt = refl

instance
  BoolEq-IsHProp : ∀ {b} → HProp (b ≡ true)
  isHProp {{BoolEq-IsHProp {false}}} () _
  isHProp {{BoolEq-IsHProp {true}}} refl refl = refl


Prod-IsHProp : ∀ {A B : Set} → (H₁ : IsHProp A)(H₂ : IsHProp B) → IsHProp (A × B)
Prod-IsHProp H₁ H₂ (a₁ , a₂) (b₁ , b₂) =  Prod-path (H₁ a₁ b₁) (H₂ a₂ b₂)

instance 
  Prod-IsHProp' : ∀ {A B : Set} → {{ _ : HProp A }} {{ _ : HProp B }} → HProp (A × B)
  isHProp {{Prod-IsHProp'}} = Prod-IsHProp isHProp isHProp

Pi-IsHProp : ∀ {A : Set}{B : A → Set} → (H : ∀ {a} → IsHProp (B a)) → IsHProp (∀ (a : A) → B a)
Pi-IsHProp H f g = extensionality (λ a → H (f a) (g a))

instance 
  Pi-IsHProp' : ∀ {A : Set}{B : A → Set} → {{ _ : ∀ {a} → HProp (B a)}} → HProp (∀ (a : A) → B a)
  isHProp {{Pi-IsHProp'}} = Pi-IsHProp isHProp

-- * H-propositional inductive predicates

-- These inductive predicates are defined through a universe (code &
-- interpretation) construction.

-- ** Code:

-- To be hprop, the inductive predicate must not be able to contain
-- any actual data. This means that there must be no choice (sum or
-- sigma) nor Set (which would a priori be at least h-set).

data PropDesc (I : Set) : Set₁ where
  `0 : PropDesc I
  `1 : PropDesc I
  `X : (i : I) → PropDesc I
  _`×_ : (A B : PropDesc I) → PropDesc I
  `Π : (S : Set)(T : S → PropDesc I) → PropDesc I

-- ** Interpretation

-- A [PropDesc] interprets into a functor [Set/I → Set]

⟦_⟧Prop : ∀ {I} → PropDesc I → (I → Set) → Set
⟦ `0 ⟧Prop X = ⊥
⟦ `1 ⟧Prop X = ⊤
⟦ `X i ⟧Prop X = X i
⟦ A `× B ⟧Prop X = ⟦ A ⟧Prop X × ⟦ B ⟧Prop X
⟦ `Π S T ⟧Prop X = (s : S) → ⟦ T s ⟧Prop X

-- ** Descriptions

-- For uniformity (and to help unification), the functor is packaged
-- in a record.

record PropFunc (I : Set) : Set₁ where
  constructor mk
  field
    apply : I → PropDesc I

-- Fixpoint:

data μProp {I} (R : PropFunc I)(i : I) : Set where
  con : ⟦ PropFunc.apply R i ⟧Prop (μProp R) → μProp R i

-- ** Lemma: [μProp R i] is hprop

module IsHProp where

  {-# TERMINATING #-}
  μProp-IsHProp : ∀{I}{R : PropFunc I}{i} → IsHProp (μProp R i)
  μProp-IsHProp-map : ∀{I R} → (D : PropDesc I) → IsHProp (⟦ D ⟧Prop (μProp R))

  μProp-IsHProp {R = R} (con xs) (con ys) = cong con (μProp-IsHProp-map (PropFunc.apply R _) xs ys)

  μProp-IsHProp-map `0 () _
  μProp-IsHProp-map `1 tt tt = refl
  μProp-IsHProp-map {R = R} (`X i) (con xs) (con ys) = cong con (μProp-IsHProp-map (PropFunc.apply R _) xs ys)
  μProp-IsHProp-map (D₁ `× D₂) (xs₁ , xs₂) (ys₁ , ys₂) = cong₂ _,_ (μProp-IsHProp-map D₁ xs₁ ys₁) (μProp-IsHProp-map D₂ xs₂ ys₂)
  μProp-IsHProp-map (`Π S T) f g = extensionality λ s → μProp-IsHProp-map (T s) (f s) (g s)

instance
  μProp-IsHProp' : ∀{I}{R : PropFunc I}{i} → HProp (μProp R i)
  isHProp {{μProp-IsHProp'}} = IsHProp.μProp-IsHProp

-- ** Examples

module Nat where

  -- Equality predicate over natural numbers

  NatEqD : ℕ × ℕ → PropDesc (ℕ × ℕ)
  NatEqD (zero , zero) = `1
  NatEqD (suc m , suc n) = `X (m , n)
  NatEqD (_ , _) = `0

  NatEqF : PropFunc (ℕ × ℕ)
  NatEqF = mk NatEqD

  NatEq : ℕ → ℕ → Set
  NatEq m n = μProp NatEqF (m , n)

  data NatEq' : ℕ → ℕ → Set where
    isZero : NatEq' 0 0
    isSuc : ∀ m n → NatEq' n m → NatEq' (suc n) (suc m)

  {-
  data NatEq' : ℕ → ℕ → Set where
    NatEq' 0 0 ∋ isZero
    NatEq' (suc n) (suc m) ∋ isSuc : NatEq' n m
  -}

  data IsPair : Σ[ x ∈ ℕ ] Bool → Set where
    isPair : ∀ x y → IsPair (x , y)

{-
  data IsPair : Σ[ x ∈ ℕ ] Bool → Set where
    IsPair (x , y) ∋ isPair
-}

  P : Bool → Set
  P true = Bool
  P false = ℕ

  data IsPair' : Σ[ x ∈ Bool ] P x → Set where
    isPair : ∀ x y → IsPair' (x , y)

{-
  data IsPair' : Σ[ x ∈ Bool ] P x → Set where
    IsPair' (x , y) ∋ isPair
-}

  NatEq-refl : ∀{m} → NatEq m m
  NatEq-refl {m} = con (NatEqF-refl m)
    where NatEqF-refl : ∀ m → ⟦ NatEqD (m , m)  ⟧Prop (μProp NatEqF)
          NatEqF-refl zero = tt
          NatEqF-refl (suc m) = con (NatEqF-refl m)


  -- Singleton predicates over natural numbers

  IsZeD :  ℕ → PropDesc ℕ
  IsZeD 0 = `1
  IsZeD (suc m) = `0

  IsZeF : PropFunc ℕ
  IsZeF = mk IsZeD

  IsZe : ℕ → Set
  IsZe m = μProp IsZeF m

  sound-IsZe : IsZe 0
  sound-IsZe = con tt

  complete-IsZe : ∀ n → IsZe n → n ≡ 0
  complete-IsZe zero (con tt) = refl
  complete-IsZe (suc _) (con ())

{-
  data ISSN (m : ℕ) : ℕ → Set where
    ze : ISSN 0 1
    su : ∀ n → ISSN m n → ISSN (suc m) (suc n)
-}

  isSn : ℕ → ℕ → Bool
  isSn 0 1 = true
  isSn (suc m) (suc n) = isSn m n
  isSn _ _ = false

  sound-isSn : ∀ n → isSn n (suc n) ≡ true
  sound-isSn 0 = refl
  sound-isSn (suc n) = sound-isSn n

  complete-isSn : ∀{m n} → isSn m n ≡ true → suc m ≡ n
  complete-isSn {zero} {zero} ()
  complete-isSn {zero} {1} _ = refl
  complete-isSn {zero} {suc (suc _)} ()
  complete-isSn {suc m} {zero} ()
  complete-isSn {suc m} {suc n} q = cong suc (complete-isSn q)

  -- Relational predicates over ℕ × ℕ (for the stack machine)
  
  nSnD :  ℕ × ℕ → PropDesc (ℕ × ℕ)
  nSnD (0 , suc 0) = `1
  nSnD (suc m , suc n) = nSnD (m , n)
  nSnD (_ , _) = `0

  nSnF : PropFunc (ℕ × ℕ)
  nSnF = mk nSnD

  nSn : ℕ → ℕ → Set
  nSn m n = μProp nSnF (m , n)

  nSn-refl : ∀{n} → nSn n (suc n)
  nSn-refl {n} = con (nSnF-refl n)
    where nSnF-refl : ∀ m → ⟦ nSnD (m , suc m) ⟧Prop (μProp nSnF)
          nSnF-refl zero = tt
          nSnF-refl (suc m) = nSnF-refl m

  SSnSnD : ℕ × ℕ → PropDesc (ℕ × ℕ)
  SSnSnD (2 , 1) = `1
  SSnSnD (suc m , suc n ) = SSnSnD (m , n)
  SSnSnD (_ , _) = `0

  SSnSnF : PropFunc (ℕ × ℕ)
  SSnSnF = mk SSnSnD

  SSnSn :  ℕ → ℕ → Set
  SSnSn m n = μProp SSnSnF (m , n)

  SSnSn-refl : ∀ {n} → SSnSn (suc (suc n)) (suc n)
  SSnSn-refl {n} = con (SSnSnF-refl n)
    where SSnSnF-refl : ∀ m → ⟦ SSnSnD (suc (suc m) , suc m) ⟧Prop (μProp SSnSnF)
          SSnSnF-refl zero = tt
          SSnSnF-refl (suc m) = SSnSnF-refl m

-- * Well-behaved datatypes

-- We define, once again through a universe construction, a set of
-- inductive families that will behave well with respect to
-- equality. In particular, they should _always_ factorize as a plain
-- (ML) datatype and an h-prop predicate.

-- ** Code:

data Desc (I : Set) : Set₁ where
  -- predicate applied to current index, this is the only way to use the index
  `P[_] : (P : PropFunc I) → Desc I 
  `B[_] : (P : I → Bool) → Desc I
  -- recursive call
  `X : I → Desc I
  -- Business as usual
  `0 : Desc I
  `1 : Desc I
  _`+_ _`×_ : (A B : Desc I) → Desc I
  `Σ `Π : (S : Set)(T : S → Desc I) → Desc I

-- ** Interpretation

-- A [Desc] defines an endofunctors [Set/I → Set/I]

⟦_⟧ : ∀ {I} → Desc I → (I → Set) → I → Set
⟦ `P[ P ] ⟧ X j = μProp P j
⟦ `B[ P ] ⟧ X j = P j ≡ true
⟦ `X i ⟧ X j = X i
⟦ `0 ⟧ X j = ⊥
⟦ `1 ⟧ X j = ⊤
⟦ A `× B ⟧ X j = ⟦ A ⟧ X j × ⟦ B ⟧ X j
⟦ A `+ B ⟧ X j = ⟦ A ⟧ X j ⊎ ⟦ B ⟧ X j
⟦ `Π S T ⟧ X j = (s : S) → ⟦ T s ⟧ X j
⟦ `Σ S T ⟧ X j = Σ[ s ∈ S ] ⟦ T s ⟧ X j

-- ** Fixpoint:
data μ {I}(F : Desc I)(i : I) : Set where
  con : ⟦ F ⟧ (μ F) i → μ F i

-- ** Examples

module Vector where

  VecD : Set → Desc ℕ
  VecD A =     (`P[ Nat.IsZeF ])
              `+ `Σ ℕ (λ m → `Σ A (λ _ → `X m `× (`B[ Nat.isSn m ])))

  Vec : Set → ℕ → Set
  Vec A = μ (VecD A)

  vnil : ∀ {A} → Vec A 0
  vnil = con (inj₁ (con tt))

  vcons : ∀ {A n} → A → Vec A n → Vec A (suc n)
  vcons {n = n} a vs = con (inj₂ (_ , a , vs , Nat.sound-isSn n))

module Instr where

  InstrD : Desc (ℕ × ℕ)
  InstrD = (`Σ ℕ λ _ → `P[ Nat.nSnF ])
         `+ `P[ Nat.SSnSnF ]

  Instr : ℕ → ℕ → Set
  Instr m n = μ InstrD (m , n)

  iconst : ∀ {n} → ℕ → Instr n (suc n)
  iconst {n} k = con (inj₁ (n , Nat.nSn-refl))

  iplus : ∀ {n} → Instr (suc (suc n)) (suc n)
  iplus = con (inj₂ Nat.SSnSn-refl)


-- * From dependent to plain inductive types

module Erasure {I : Set} where

-- ** Plain inductive type

-- We compute the code of the plain inductive type from the code of
-- the dependent type

  rawD : Desc I → Desc ⊤
  rawD `0 = `0
  rawD `1 = `1
  rawD (`P[ P ]) = `1
  rawD (`B[ P ]) = `1
  rawD (`X i) = `X tt
  rawD (D₁ `+ D₂) = rawD D₁ `+ rawD D₂
  rawD (D₁ `× D₂) = rawD D₁ `× rawD D₂
  rawD (`Σ S T) = `Σ S λ s → rawD (T s)
  rawD (`Π S T) = `Π S λ s → rawD (T s)
  
  μ↓ : (F : Desc I) → Set
  μ↓ F = μ (rawD F) tt

-- ** Indexing predicate

-- We implement a generic predicate which captures exactly the logical
-- content of the dependent family

  {-# TERMINATING #-}
  Pred : ∀{F} → μ↓ F → I → Set
  Pred-map : ∀{F} → (D : Desc I) → ⟦ rawD D ⟧ (λ _ → μ↓ F) tt → I → Set

  Pred {F} (con xs) j = Pred-map {F} F xs j 

  Pred-map `P[ P ] xs j = μProp P j
  Pred-map `B[ P ] xs j = P j ≡ true
  Pred-map {F} (`X i) xs j = Pred {F} xs i
  Pred-map `0 () _
  Pred-map `1 tt j = ⊤
  Pred-map {F} (D₁ `+ D₂) (inj₁ xs) j = Pred-map {F} D₁ xs j
  Pred-map {F} (D₁ `+ D₂) (inj₂ xs) j = Pred-map {F} D₂ xs j
  Pred-map {F} (D₁ `× D₂) (xs₁ , xs₂) j = Pred-map {F} D₁ xs₁ j × Pred-map {F} D₂ xs₂ j
  Pred-map {F} (`Σ S T) (s , xs) j = Pred-map {F} (T s) xs j
  Pred-map {F} (`Π S T) f j = ∀ s → Pred-map {F} (T s) (f s) j

-- ** From dependent to plain value

-- We implement a generic function translating from dependent to plain
-- datatypes

  {-# TERMINATING #-}
  val : ∀ {F}{i} → μ F i → μ↓ F
  val-map : ∀ {F}{i} D → ⟦ D ⟧ (λ i → μ F i) i → ⟦ rawD D ⟧ (λ _ → μ↓ F) tt
  
  val {F} (con xs) = con (val-map F xs)

  val-map `0 ()
  val-map `1 tt = tt
  val-map `P[ P ] _ = tt
  val-map `B[ P ] _ = tt
  val-map (`X i) x = val x
  val-map (D₁ `+ D₂) (inj₁ xs₁) = inj₁ (val-map D₁ xs₁)
  val-map (D₁ `+ D₂) (inj₂ xs₂) = inj₂ (val-map D₂ xs₂)
  val-map (D₁ `× D₂) (xs₁ , xs₂) = val-map D₁ xs₁ , val-map D₂ xs₂
  val-map (`Σ S T) (s , xs) = s , val-map (T s) xs
  val-map (`Π S T) f = λ s → val-map (T s) (f s)

-- ** Soundness

-- We show that the plain value obtained from [val] verifies the
-- logical predicate [Pred]

  {-# TERMINATING #-}
  soundness : ∀ {F}{i} → (x : μ F i) → Pred {F} (val x) i
  soundness-map : ∀ {F}{i} → (D : Desc I) → (xs : ⟦ D ⟧ (μ F) i) → Pred-map {F} D (val-map D xs) i

  soundness {F} (con xs) = soundness-map {F} F xs

  soundness-map `P[ P ] p = p
  soundness-map `B[ P ] p = p
  soundness-map (`X i) xs = soundness xs
  soundness-map `0 ()
  soundness-map `1 tt = tt
  soundness-map (D₁ `+ D₂) (inj₁ xs) = soundness-map D₁ xs
  soundness-map (D₁ `+ D₂) (inj₂ xs) = soundness-map D₂ xs
  soundness-map (D₁ `× D₂) (xs₁ , xs₂) = soundness-map D₁ xs₁ , soundness-map D₂ xs₂
  soundness-map (`Σ S T) (s , xs) = soundness-map (T s) xs
  soundness-map (`Π S T) f = λ s → soundness-map (T s) (f s)

  subset : ∀{i}{F} → (x : μ F i) → Σ[ x ∈ μ↓ F ] Pred {F} x i
  subset x = (val x , soundness x)

-- ** Completeness

-- Conversely, we show that any plain value satisfying [Pred] gives an
-- inhabitant of the dependent family

  {-# TERMINATING #-}
  completeness : ∀{F}{i} → Σ[ x ∈ μ↓ F ] Pred {F} x i → μ F i
  completeness-map : ∀{F}{i} (D : Desc I) → (xs : ⟦ rawD D ⟧ (λ _ → μ↓ F) tt) → Pred-map {F} D xs i → ⟦ D ⟧ (μ F) i

  completeness {F} (con xs , p) = con (completeness-map F xs p)

  completeness-map `P[ P ] xs p = p
  completeness-map `B[ P ] xs p = p
  completeness-map (`X x) xs p = completeness (xs , p)
  completeness-map `0 () _
  completeness-map `1 tt tt = tt
  completeness-map (D₁ `+ D₂) (inj₁ xs) p = inj₁ (completeness-map D₁ xs p)
  completeness-map (D₁ `+ D₂) (inj₂ xs) p = inj₂ (completeness-map D₂ xs p)
  completeness-map (D₁ `× D₂) (xs₁ , xs₂) (p₁ , p₂) = completeness-map D₁ xs₁ p₁ , completeness-map D₂ xs₂ p₂
  completeness-map (`Σ S T) (s , xs) p = s , completeness-map (T s) xs p
  completeness-map (`Π S T) f p = λ s → completeness-map (T s) (f s) (p s)

-- ** Example

module VectorErasure where

  open Erasure {ℕ}

  List' : Set → Set
  List' A = μ↓ (Vector.VecD A)

  nil : ∀ {A} → List' A
  nil = con (inj₁ tt)

  cons : ∀{A} → ℕ → A → List' A → List' A
  cons n a xs = con (inj₂ ({- XXX: -} n , (a , (xs , tt))))

  data List'-View {A} : List' A → Set where
    isNil : List'-View nil
    isCons : ∀ n a xs → List'-View (cons n a xs)

  List'-view : ∀ {A} → (xs : List' A) → List'-View xs
  List'-view (con (inj₁ tt)) = isNil
  List'-view (con (inj₂ (n , a , xs , tt))) = isCons n a xs

  IsVec : ∀{A} → List' A → ℕ → Set
  IsVec xs n = Pred {Vector.VecD _} xs n

  IsVec-nil : ∀{A} → IsVec {A} nil 0
  IsVec-nil = con tt

  IsVec-cons : ∀{A n a xs} → IsVec {A} xs n → IsVec {A} (cons n a xs) (suc n)
  IsVec-cons {n = n} q = q , Nat.sound-isSn n

module InstrErasure where

  open Erasure {ℕ × ℕ}

  Instr : Set
  Instr = μ↓ Instr.InstrD

  iconst : ℕ → Instr
  iconst k = con (inj₁ (k , tt))

  iplus : Instr
  iplus = con (inj₂ tt)

-- ** Lemma

-- The predicate is H-Prop

module Pred-IsHProp {I : Set}(F : Desc I) where

  open IsHProp
  open Erasure {I}

  {-# TERMINATING #-}
  Pred-IsHProp : ∀ (xs : μ↓ F)(i : I) → IsHProp (Pred {F} xs i)
  PredDesc-IsHProp : (D : Desc I) → (xs : ⟦ rawD D ⟧ (λ _ → μ↓ F) tt)(i : I) → IsHProp (Pred-map {F} D xs i)

  Pred-IsHProp (con xs) j = PredDesc-IsHProp F xs j

  PredDesc-IsHProp `P[ P ] xs j = isHProp
  PredDesc-IsHProp `B[ P ] xs j = isHProp
  PredDesc-IsHProp (`X i) xs j = Pred-IsHProp xs i
  PredDesc-IsHProp `0 () _
  PredDesc-IsHProp `1 xs j = isHProp
  PredDesc-IsHProp (D₁ `+ D₂) (inj₁ xs) j = PredDesc-IsHProp D₁ xs j
  PredDesc-IsHProp (D₁ `+ D₂) (inj₂ xs) j = PredDesc-IsHProp D₂ xs j
  PredDesc-IsHProp (D₁ `× D₂) (xs₁ , xs₂) j = Prod-IsHProp (PredDesc-IsHProp D₁ xs₁ j) (PredDesc-IsHProp D₂ xs₂ j)
  PredDesc-IsHProp (`Σ S T) (s , xs) j = PredDesc-IsHProp (T s) xs j
  PredDesc-IsHProp (`Π S T) f j = Pi-IsHProp (λ {s} → PredDesc-IsHProp (T s) (f s) j)

-- * Main theorem

-- We show the injectivity property:
--     [inj : ∀ {i}(x y : μ F i) → val x ≡ val y → x ≡ y]

module Injectivity {I : Set}{F : Desc I} where

  open Erasure {I}
  open Pred-IsHProp {I} F

  hprop-μ : ∀ {i}{xs ys : ⟦ rawD  F ⟧ (λ _ → μ↓ F) tt}(q : xs ≡ ys)(p : Pred {F} (con xs) i) →
              subst (λ x → Pred {F} x i) (cong con q) p ≡ subst (λ xs₁ → Pred-map F xs₁ i) q p
  hprop-μ refl p = refl

-- ** Lemma: section

  {-# TERMINATING #-}
  sect :  ∀ {i}(x : Σ[ x ∈ μ↓ F ] Pred {F} x i) → x ≡ subset {_}{F} (completeness x)
  sect-map₁ : ∀ {i}(D : Desc I)(xs : ⟦ rawD D ⟧ (λ _ → μ↓ F) tt)(p : Pred-map {F} D xs i) → xs ≡ val-map D (completeness-map D xs p)
  sect-map₂ : ∀ {i}(D : Desc I)(xs : ⟦ rawD D ⟧ (λ _ → μ↓ F) tt)(p : Pred-map {F} D xs i) → subst (λ xs → Pred-map {F} D xs i) (sect-map₁ D xs p) p ≡ soundness-map D (completeness-map D xs p)

  sect {i} (con xs , p) = Σ-path {μ↓ F} {λ x → Pred {F} x i} 
                             (cong con (sect-map₁ F xs p)) 
                             (trans (hprop-μ (sect-map₁ F xs p) p) (sect-map₂ F xs p))
  sect-map₁ `P[ P ] tt p = refl
  sect-map₁ `B[ P ] tt p = refl
  sect-map₁ (`X i) (con xs) p = cong con (sect-map₁ (F) xs p)
  sect-map₁ `0 () _
  sect-map₁ `1 tt tt = refl
  sect-map₁ (D₁ `+ D₂) (inj₁ xs) p = cong inj₁ (sect-map₁ D₁ xs p)
  sect-map₁ (D₁ `+ D₂) (inj₂ xs) p = cong inj₂ (sect-map₁ D₂ xs p)
  sect-map₁ (D₁ `× D₂) (xs₁ , xs₂) (p₁ , p₂) = Prod-path (sect-map₁ D₁ xs₁ p₁) (sect-map₁ D₂ xs₂ p₂)
  sect-map₁ (`Σ S T) (s , xs) p = Σ-path refl (sect-map₁ (T s) xs p)
  sect-map₁ (`Π S T) f p = extensionality (λ s → sect-map₁ (T s) (f s) (p s))

  sect-map₂ {i} D xs p = PredDesc-IsHProp D (val-map D (completeness-map D xs p)) i 
                                          (subst (λ xs → Pred-map {F} D xs i) (sect-map₁ D xs p) p) 
                                          (soundness-map D (completeness-map D xs p)) 

-- ** Lemma: retraction

  {-# TERMINATING #-}
  retr : ∀ {i}(x : μ F i) → completeness (subset x) ≡ x
  retr-map : ∀ {i}(D : Desc I)(xs : ⟦ D ⟧ (μ F) i) → completeness-map D (val-map D xs) (soundness-map D xs) ≡ xs

  retr (con xs) = cong con (retr-map F xs)

  retr-map `P[ P ] xs = refl
  retr-map `B[ P ] xs = refl
  retr-map (`X i) x = retr x
  retr-map `0 ()
  retr-map `1 tt = refl
  retr-map (D₁ `+ D₂) (inj₁ xs) = cong inj₁ (retr-map D₁ xs)
  retr-map (D₁ `+ D₂) (inj₂ xs) = cong inj₂ (retr-map D₂ xs)
  retr-map (D₁ `× D₂) (xs₁ , xs₂) = Prod-path (retr-map D₁ xs₁) (retr-map D₂ xs₂)
  retr-map (`Σ S T) (s , xs) = Σ-path refl (retr-map (T s) xs)
  retr-map (`Π S T) f = extensionality (λ s → retr-map (T s) (f s))

-- ** Theorem: injectivity of [val]

  inj : ∀ {i}(x y : μ F i) → val x ≡ val y → x ≡ y
  inj {i} x y q = 
    begin x 
              ≡⟨ sym (retr x) ⟩ 
          completeness (val x , soundness x) 
              ≡⟨ cong completeness
                      (Σ-path q (hprop-Σ q (λ {x} → Pred-IsHProp x i))) ⟩ 
          completeness (val y , soundness y) 
              ≡⟨ retr y ⟩ 
          y  ∎

      where open ≡-Reasoning

-- ** More interesting theorem: JMEq-like elimination

  rewrite-val-subst : ∀ {i j} (q : i ≡ j)(x : μ F i) → val (subst (μ F) q x) ≡ val x
  rewrite-val-subst refl x = refl

  inj⁺ : ∀ {i j}(x : μ F i)(y : μ F j){P : ∀ {k} → μ F k → Set} → 
         i ≡ j → val x ≡ val y → P x → P y
  inj⁺ {i} x y {P} q-idx q-val Px = 
    subst (λ { (k , x) → P {k} x }) 
      (Σ-path q-idx 
              (inj (subst (μ F) q-idx x)
                   y 
                   (trans (rewrite-val-subst q-idx x) 
                          q-val)))
      Px 
