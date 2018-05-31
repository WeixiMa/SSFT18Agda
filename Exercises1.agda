-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Exercise session 1: First definitions and proofs in Agda


-- Cartesian product

infixl 6 _×_  -- \ times

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open _×_

-- Swap

swap : ∀{A B : Set} → A × B → B × A
swap (fst₁ , snd₁) = snd₁ , fst₁

-- Function pairing

<_,_> : ∀{A B C : Set} (f : C → A) (g : C → B) → (C → A × B)
<_,_> f g c = f c , g c

_×̇_ : ∀{A B C D : Set} (f : A → C) (g : B → D) → (A × B → C × D)  -- \ times \ ^ .
_×̇_ = λ f g z → f (fst z) , g (snd z)

-- Currying and uncurrying

curry : ∀{A B C : Set} (f : A × B → C) → (A → B → C)
curry = λ f z z₁ → f (z , z₁)

uncurry : ∀{A B C : Set} (f : A → B → C) → (A × B → C)
uncurry = λ f z → f (fst z) (snd z)


-- Disjoint sums

data _⊎_ (A B : Set) : Set where  -- \ uplus
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Case

[_,_] : ∀{A B C : Set} (f : A → C) (g : B → C) → A ⊎ B → C
[ f , g ] (inl x) = f x
[ f , g ] (inr x) = g x


-- Equality

open import Agda.Builtin.Equality using (_≡_; refl)

-- Symmetry

sym : ∀{A : Set} {x y : A} (eq : x ≡ y) → y ≡ x
sym refl = refl

-- Transitivity

trans : ∀{A : Set} {x y z : A} (eq : x ≡ y) (eq' : y ≡ z) → x ≡ z
trans refl refl = refl

-- Substitutivity

subst : ∀{A : Set} (P : A → Set) {l r : A} (eq : l ≡ r) (p : P l) → P r
subst P refl p = p

-- Congruence

cong : ∀{A B : Set} (f : A → B) {x y : A} (eq : x ≡ y) → f x ≡ f y
cong f refl = refl

-- Unicity of identity proofs

UIP : ∀{A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP refl refl = refl


-- Booleans

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : ∀{A : Set} (b : Bool) (t e : A) → A
if true then t else e  = t
if false then t else e = e

-- Lists

infixr 8 _∷_ _++_

module Lists where

  data List (A : Set) : Set where
    [] : List A
    _∷_ : (x : A) (xs : List A) → List A

  -- append

  _++_ : ∀{A} (xs ys : List A) → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- Monoid laws

  idl : ∀{A} (xs : List A) → [] ++ xs ≡ xs
  idl xs = refl

  idr : ∀{A} (xs : List A) → xs ++ [] ≡ xs
  idr [] = refl
  idr (x ∷ xs) = cong (λ almost → x ∷ almost) (idr xs)

  assoc : ∀{A} (xs {ys zs} : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc [] = refl
  assoc (x ∷ xs) = cong (λ almost → x ∷ almost) (assoc xs)

  -- Sublists

  data Sublist {A} : (xs : List A) → Set where
    [] : Sublist []
    •∷_ : ∀{xs x} (ys : Sublist xs) → Sublist (x ∷ xs)
    _∷_ : ∀{xs} (y : A) (ys : Sublist xs) → Sublist (y ∷ xs)

  -- Define a function that extras the list, forgetting the sublist property.

  toList : ∀{A} {xs : List A} (ys : Sublist xs) → List A
  toList [] = []
  toList (•∷_ {xs = xs} ys) = xs
  toList (_∷_ {xs = xs} y ys) = y ∷ xs

  -- List filtering

  filter : ∀{A} (f : A → Bool) (xs : List A) → Sublist xs
  filter f [] = []
  filter f (x ∷ xs) with f x
  filter f (x ∷ xs) | true = •∷ filter f xs 
  filter f (x ∷ xs) | false = x ∷ filter f xs

  -- Sublist concatenation

  append : ∀{A} {xs ys : List A} → Sublist xs → Sublist ys → Sublist (xs ++ ys)
  append [] sub_ys = sub_ys
  append (•∷ sub_xs) sub_ys = •∷ append sub_xs sub_ys
  append (y ∷ sub_xs) sub_ys = y ∷ append sub_xs sub_ys

-- Natural numbers

open import Agda.Builtin.Nat

-- Show that Nat forms a commutative monoid under addition.

plus-assoc : ∀ x {y z} → (x + y) + z ≡ x + (y + z)
plus-assoc zero = refl
plus-assoc (suc x) = cong (λ almost → suc almost) (plus-assoc x)

plus-zero : ∀ x → x + 0 ≡ x
plus-zero zero = refl
plus-zero (suc x) = cong (λ almost → suc almost) (plus-zero x)

plus-suc : ∀ x {y} → x + suc y ≡ suc (x + y)
plus-suc zero = refl
plus-suc (suc x) = cong (λ almost → suc almost) (plus-suc x)

plus-comm : ∀ x {y} → x + y ≡ y + x
plus-comm zero = sym (plus-zero _)
plus-comm (suc x) {y} = trans (cong suc (plus-comm x)) (sym (plus-suc y)) 


-- Empty type

data ⊥ : Set where

-- Negation

¬_ : (P : Set) → Set  -- \ neg
¬ P = P → ⊥

-- Decidability

data Dec (P : Set) : Set where
  yes : (p  :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

-- Equality of natural numbers is decidable

suc-eq : {n m : Nat} → (suc m ≡ suc n) → m ≡ n
suc-eq refl = refl

_≟_ : (n m : Nat) → Dec (n ≡ m)  -- \ ? =
zero ≟ zero = yes refl
zero ≟ suc m = no (λ ())
suc n ≟ zero = no (λ ())
suc n ≟ suc m with n ≟ m
suc n ≟ suc .n | yes refl = yes refl
suc n ≟ suc m | no ¬p = no λ p → ¬p (suc-eq p)


-- Vectors

module Vectors where

  -- Vectors are lists indexed by their length.

  data Vec (A : Set) : Nat → Set where
    [] : Vec A 0
    _∷_ : ∀{n} (x : A) (xs : Vec A n) → Vec A (suc n)

  -- append

  _++_ : ∀{A n m} (xs : Vec A n) (ys : Vec A m) → Vec A (n + m)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- Associativity of append (already tricky!)

  -- A simple-minded statement of associativity is not well-formed, because the types of
  -- the sides of the equality are formally different.
  --
  --   assoc-++ : ∀{A n m l} (xs : Vec A n) {ys : Vec A m} {zs : Vec A l} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  --
  -- The lhs speaks about Vectors of length ((n + m) + l) while the rhs has (n + (m + l)).
  -- These expressions are not definitionally equal, only provably equal.
  -- We need to convert the type of the lhs using the associativity for Nat.

  -- Congruence lemma for vector-cons:

  cong-∷ : ∀{A n m x} (eqn : n ≡ m) {xs : Vec A n} {ys : Vec A m}
    → (subst (Vec A) eqn xs) ≡ ys
    → (subst (Vec A) (cong suc eqn) (x ∷ xs)) ≡ x ∷ ys
  cong-∷ refl refl = refl

  -- Associativity

  assoc-++ : ∀{A n m l} (xs : Vec A n) {ys : Vec A m} {zs : Vec A l} →
    (subst (Vec A) (plus-assoc n) ((xs ++ ys) ++ zs)) ≡ (xs ++ (ys ++ zs))
  assoc-++ [] = refl
  assoc-++ {n = suc n-1} (x ∷ xs) = cong-∷ (plus-assoc n-1) (assoc-++ xs)

  -- Formulate and prove the identity law  xs ++ [] ≡ xs  for vectors!
  -- (You will need a similar trick than for associativity.)

  ++[] : ∀ {A n} (xs : Vec A n) → (subst (Vec A) (plus-zero n) (xs ++ [])) ≡ xs
  ++[] [] = refl
  ++[] {n = suc n-1} (x ∷ xs) = cong-∷ (plus-zero n-1) (++[] xs)

  -- Can you define a suitable concept of vector equality that
  -- encapsulates the "subst" reasoning here?

  vec-subst : ∀ {A n m} {eqn : n ≡ m} (P : (k : Nat) → (Vec A k) → Set)
                {x : Vec A n} {y : Vec A m} (eqv : (subst (Vec A) eqn x) ≡ y)
                (p : P n x) → P m y
  vec-subst {n = n} {.n} {refl} P eqv p = subst (P n) eqv p 

-- Advanced exercises:

-- Define an indexed data type of red-black trees that expresses the balancing invariant.
-- This means that by virtue of dependent typing you can never construct an unbalanced tree.

-- Define the rotations for red-black trees.
-- Define an inserting function into red-black trees.

-- Reference:
--   Chris Okasaki:
--   Red-Black Trees in a Functional Setting. J. Funct. Program. 9(4): 471-477 (1999)

-- Further advancing the exercise:
--
-- Add the ordering invariant (as seen in the lecture) to your red-black trees.
