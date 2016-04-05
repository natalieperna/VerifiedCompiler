\begin{code}
module VerifiedCompiler where

open import Data.Fin hiding (_+_;_-_;_≤_;_<_)
open import Data.Nat hiding (_+_;_≤_;_≥_;_<_;_>_;_≟_)
open import Data.Integer renaming (
  _+_ to plus;
  _*_ to times;
  -_ to negative;
  _-_ to minus;
  _≤_ to leq)
open import Data.Vec
open import Data.Bool hiding (if_then_else_;_≟_) renaming (_∧_ to and; _∨_ to or)
open import Relation.Nullary.Decidable
\end{code}

\begin{code}
\end{code}

RSD p. 135:

\begin{code}
data Exp-int (n : ℕ) : Set where
  Lit : ℤ → Exp-int n
  Var : Fin n → Exp-int n
  -_ : Exp-int n → Exp-int n
  _+_ : Exp-int n → Exp-int n → Exp-int n
  _-_ : Exp-int n → Exp-int n → Exp-int n
  _×_ : Exp-int n → Exp-int n → Exp-int n
  --_div_ : Exp-int n → Exp-int n → Exp-int n
  --_mod_ : Exp-int n → Exp-int n → Exp-int n
\end{code}

\begin{code}
data Exp-bool (n : ℕ): Set where
  ⊤ : Exp-bool n
  ⊥ : Exp-bool n
  ¬_  : Exp-bool n → Exp-bool n
  _∧_ : Exp-bool n → Exp-bool n → Exp-bool n
  _∨_ : Exp-bool n → Exp-bool n → Exp-bool n
  _≡_ : Exp-int n → Exp-int n → Exp-bool n
  _≠_ : Exp-int n → Exp-int n → Exp-bool n
  _<_ : Exp-int n → Exp-int n → Exp-bool n
  _≤_ : Exp-int n → Exp-int n → Exp-bool n
  _>_ : Exp-int n → Exp-int n → Exp-bool n
  _≥_ : Exp-int n → Exp-int n → Exp-bool n
\end{code}

RSD p. 131:

\begin{code}
data Comm (n : ℕ) : Set where
  skip : Comm n
  _,_  : Comm n → Comm n → Comm n
  _≔_ : Fin n → Exp-int n → Comm n
  if_then_else_ : Exp-bool n → Comm n → Comm n → Comm n
  while_do_ : Exp-bool n → Comm n → Comm n
\end{code}

RSD p. 135:

\begin{code}
infixl 5 _⊢_⇓ₐ_
infixl 5 _⊢_⇓₀_
infixl 5 _⊢_⇓_

data _⊢_⇓ₐ_ {n : ℕ} ( E : Vec ℤ n) : Exp-int n → ℤ → Set where
  lit-e   : ∀{n}

            -------------
          → E ⊢ Lit n ⇓ₐ n

  var-e   : ∀{n}{x}

          → E [ x ]= n
            -------------
          → E ⊢ Var x ⇓ₐ n

  negative-e : ∀{e}{v}

          → E ⊢ e ⇓ₐ v
            ---------------------
          → E ⊢ - e ⇓ₐ negative v

  plus-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ₐ v₁
          → E ⊢ e₂ ⇓ₐ v₂
            ---------------------
          → E ⊢ e₁ + e₂ ⇓ₐ plus v₁ v₂

  minus-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ₐ v₁
          → E ⊢ e₂ ⇓ₐ v₂
            ---------------------
          → E ⊢ e₁ - e₂ ⇓ₐ minus v₁ v₂

  times-e : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ₐ v₁
          → E ⊢ e₂ ⇓ₐ v₂
            ---------------------
          → E ⊢ e₁ × e₂ ⇓ₐ times v₁ v₂


data _⊢_⇓₀_ {n : ℕ} ( E : Vec ℤ n) : Exp-bool n → Bool → Set where
  true-e   :

            -------------
            E ⊢ ⊤ ⇓₀ true

  false-e   :

            -------------
            E ⊢ ⊥ ⇓₀ false

  not-e : ∀{e}{v}

          → E ⊢ e ⇓₀ v
            ---------------------
          → E ⊢ ¬ e ⇓₀ not v

  and-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓₀ v₁
          → E ⊢ e₂ ⇓₀ v₂
            ---------------------
          → E ⊢ e₁ ∧ e₂ ⇓₀ and v₁ v₂

  or-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓₀ v₁
          → E ⊢ e₂ ⇓₀ v₂
            ---------------------
          → E ⊢ e₁ ∨ e₂ ⇓₀ or v₁ v₂

  equals-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ₐ v₁
          → E ⊢ e₂ ⇓ₐ v₂
            ---------------------
          → E ⊢ e₁ ≡ e₂ ⇓₀ ⌊ v₁ ≟ v₂ ⌋

  nequals-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ₐ v₁
          → E ⊢ e₂ ⇓ₐ v₂
            ---------------------
          → E ⊢ e₁ ≡ e₂ ⇓₀ not ⌊ v₁ ≟ v₂ ⌋

-- TODO _<_ : Exp-int n → Exp-int n → Exp-bool n
{-
  leq-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ₐ v₁
          → E ⊢ e₂ ⇓ₐ v₂
            ---------------------
          → E ⊢ e₁ ≤ e₂ ⇓₀ leq v₁ v₂
-}
-- TODO _>_ : Exp-int n → Exp-int n → Exp-bool n
-- TODO _≥_ : Exp-int n → Exp-int n → Exp-bool n
\end{code}

RSD p. 133:

\begin{code}
data _⊢_⇓_ {n : ℕ} ( E : Vec ℤ n) : Comm n → (E : Vec ℤ n) → Set where
  skip-e : 
           -------------------
           E ⊢ skip ⇓ E

  seq-e  : ∀{c₁ c₂}{e₁ e₂}

          → E ⊢ c₁ ⇓ e₁
          → e₁ ⊢ c₂ ⇓ e₂
            ---------------------
          → E ⊢ c₁ , c₂ ⇓ e₂

  assign-e  : ∀{a}{n}{x}

          → E ⊢ a ⇓ₐ n
            ---------------------
          → E ⊢ (x ≔ a) ⇓ (E [ x ]≔ n)

  if-true-e  : ∀{b}{c₁ c₂}{e₁}

          → E ⊢ b ⇓₀ true
          → E ⊢ c₁ ⇓ e₁
            ---------------------
          → E ⊢ if b then c₁ else c₂ ⇓ e₁

  if-false-e  : ∀{b}{c₁ c₂}{e₂}

          → E ⊢ b ⇓₀ false
          → E ⊢ c₂ ⇓ e₂
            ---------------------
          → E ⊢ if b then c₁ else c₂ ⇓ e₂

  while-true-e  : ∀{b}{c}{E′ E″}

          → E ⊢ b ⇓₀ true
          → E ⊢ c ⇓ E′
          → E′ ⊢ while b do c ⇓ E″
            ---------------------
          → E ⊢ while b do c ⇓ E″

  while-false-e  : ∀{b}{c}

          → E ⊢ b ⇓₀ false
            ---------------------
          → E ⊢ while b do c ⇓ E
\end{code}

