<div class=hidden>
\begin{code}
module VerifiedCompiler where

open import Data.Fin hiding (_+_;_-_;_≤_;_<_)
open import Data.Nat hiding (_+_;_≤_;_≥_;_<_;_>_)
open import Data.Integer renaming (
  _+_ to plus;
  _*_ to times;
  -_ to negative;
  _-_ to minus;
  _≤_ to leq)
open import Data.Vec
open import Data.Bool hiding (if_then_else_) renaming (_∧_ to and; _∨_ to or)
\end{code}
</div>

Recently my research has been centered around the development of a self-certifying compiler for a functional
language with linear types called Cogent (see @Cogent). The compiler works by emitting, along with generated
low-level code, a proof in Isabelle/HOL (see @Nipkow) that the generated code is a refinement of the original program,
expressed via a simple functional semantics in HOL.

As dependent types unify for us the language of code and proof, my current endeavour has been to explore how such a compiler
would look if it were implemented and verified in a dependently typed programming language instead. In this post, I
implement and verify a toy compiler for a language of arithmetic expressions and variables to an idealised assembly language
for a virtual stack machine, and explain some of the useful features that dependent types give us for writing verified compilers.

*The Agda snippets in this post are interactive! Click on a symbol to see its definition.*

## Wellformedness

One of the immediate advantages that dependent types give us is that we can encode the notion of _term wellformedness_
in the type given to terms, rather than aCs a separate proposition that must be assumed by every theorem.

Even in our language of arithmetic expressions and variables, which does not have much of a static semantics,
we can still ensure that each variable used in the program is bound somewhere. We will use indices instead of variable names
in the style of @deBruijn, and index terms by the _number of available variables_, a trick I first noticed in @McBride.
The `Fin` type, used to represent variables, only contains natural numbers up to its index, which makes it impossible to use
variables that are not available.

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

data Comm (n : ℕ) : Set where
  skip : Comm n
  _,_  : Comm n → Comm n → Comm n -- sequential composition
  _≔_ : Fin n → Exp-int n → Comm n
  if_then_else_ : Exp-bool n → Comm n → Comm n → Comm n
  while_do_ : Exp-bool n → Comm n
\end{code}

This allows us to express in the _type_ of our big-step semantics relation that the environment `E` (here we used the length-indexed
`Vec` type from the Agda standard library) should have a value for every available variable in the term. In any Isabelle specification
of the same, we would have to add such length constraints as explicit assumptions, either in the semantics themselves or in theorems
about them. In Agda, the dynamic semantics are extremely clean, unencumbered by irritating details of the encoding:

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

-- TODO _≡_ : Exp-int n → Exp-int n → Exp-bool n
-- TODO _≠_ : Exp-int n → Exp-int n → Exp-bool n
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

  -- TODO if_then_else_ : Exp-bool n → Comm n → Comm n → Comm n
  -- TODO while_do_ : Exp-bool n → Comm n
\end{code}

By using appropriate type indices, it is possible to extend this technique to work even for languages with elaborate static semantics.
For example, linear type systems (see @ATAPL) can be encoded by indexing terms by type contexts (in a style similar to [Oleg](http://okmij.org/ftp/tagless-final/course/LinearLC.hs)). Therefore, the boundary between
being _wellformed_ and being _well-typed_ is entirely arbitrary. It's possible to use relatively simple terms and encode static semantics
as a separate judgement, or to put the entire static semantics inside the term structure, or to use a mixture of both. In this simple example,
our static semantics only ensure variables are in scope, so it makes sense to encode the entire static semantics in the terms themselves.
