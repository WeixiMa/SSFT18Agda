-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Exercise session 2: More definitions and proofs in Agda

open import Data.Sum
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

data ⊥ : Set where

data ⊤ : Set where
  trivial : ⊤


-- Negation

¬_ : (P : Set) → Set  -- \ neg
¬ P = P → ⊥

⊥-elim : ∀ {l} {Bullshit : Set l} → ⊥ → Bullshit
⊥-elim ()

lemma : ∀ {A : Set} {x y : A} → (p : x ≡ y) → (q : ¬ (x ≡ y)) → ⊥
lemma {A} {x} {.x} refl q = (q refl)

-- Decidability ctd.

data Dec (P : Set) : Set where
  yes : (p  :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

-- Decidable sets are closed under ⊥, ⊤, ⊎, ×, →

dec⊥ : Dec ⊥  -- \ bot
dec⊥ = no (λ x → x)

dec⊤ : Dec ⊤  -- \ top
dec⊤ = yes trivial

dec⊎ : ∀{P Q : Set} (p : Dec P) (q : Dec Q) → Dec (P ⊎ Q)  -- \ uplus
dec⊎ (yes p) (yes q) = yes (inj₁ p)
dec⊎ (yes p) (no ¬q) = yes (inj₁ p)
dec⊎ (no ¬p) (yes q) = yes (inj₂ q)
dec⊎ (no ¬p) (no ¬q) = no λ x → [ ¬p , ¬q ]′ x

dec× : ∀{P Q : Set} (p : Dec P) (q : Dec Q) → Dec (P × Q)  -- \ times
dec× (yes p) (yes q) = yes (p , q)
dec× (yes p) (no ¬q) = no (λ z → ¬q (proj₂ z))
dec× (no ¬p) (yes q) = no (λ z → ¬p (proj₁ z))
dec× (no ¬p) (no ¬q) = no (λ z → ¬q (proj₂ z))

dec→ : ∀{P Q : Set} (p : Dec P) (q : Dec Q) → Dec (P → Q)  -- \ to
dec→ (yes p) (yes q) = yes (λ x → q)
dec→ (yes p) (no ¬q) = no (λ z → ¬q (z p))
dec→ (no ¬p) (yes q) = yes (λ x → q)
dec→ (no ¬p) (no ¬q) = yes λ p → ⊥-elim (¬p p)

-- Less-or-equal order on natural numbers defined inductively

open import Agda.Builtin.Nat

data _≤_ : (n m : Nat) → Set where  -- \ le
  -- add constructors here
  0≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m

1≤3 : 1 ≤ 3
1≤3 = s≤s 0≤n

≤0 : ∀{n} (n≤0 : n ≤ 0) → n ≡ 0
≤0 0≤n = refl

≤refl : ∀ n → n ≤ n
≤refl zero = 0≤n
≤refl (suc n) = s≤s (≤refl n)

≤trans : ∀{n m l} (n≤m : n ≤ m) (m≤l : m ≤ l) → n ≤ l
≤trans 0≤n 0≤n = 0≤n
≤trans 0≤n (s≤s p') = 0≤n
≤trans (s≤s p) (s≤s p') = s≤s (≤trans p p')

≤antisym : ∀{n m} (n≤m : n ≤ m) (m≤n : m ≤ n) → n ≡ m
≤antisym 0≤n 0≤n = refl
≤antisym (s≤s p) (s≤s p') with (≤antisym p p')
≤antisym (s≤s p) (s≤s p') | refl = refl

-- Advanced exercise:
-- Define substitution for IPL (see file Substitution.agda)

-- Very advanced exercise:
-- Prove normalization for IPL (see file Normal.agda)

-- -}
