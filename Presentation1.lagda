\documentclass{beamer}

\usetheme{Antibes}

\usepackage{agda}

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}

\usepackage{ucs}
\usepackage{autofe}

\DeclareUnicodeCharacter{8759}{::}
\DeclareUnicodeCharacter{8799}{\ensuremath{\stackrel{?}{=}}}

\AtBeginSection[]{
  \begin{frame}
  \vfill
  \centering
  \begin{beamercolorbox}[sep=8pt,center,shadow=true,rounded=true]{title}
    \usebeamerfont{title}\insertsectionhead\par%
  \end{beamercolorbox}
  \vfill
  \end{frame}
}

\title{A (Toy) Verified Compiler in Agda}

\author{Natalie Perna\\
  pernanm@mcmaster.ca}

\institute{Department of Computing and Software\\
    McMaster University}

\date{March 16, 2016}

  \begin{document}

\begin{frame}
    \titlepage
\end{frame}

\begin{frame}{Outline}
    \tableofcontents
\end{frame}

\section{Agda}

\iffalse
\begin{code}
open import Data.Fin hiding (_+_;_≤_) renaming (#_ to i)
open import Data.Nat hiding (_≟_;_≤_)
open import Data.Vec hiding (_>>=_; _⊛_)
open import Data.Bool hiding (_≟_)
\end{code}
\fi

\begin{frame}{Introduction to Agda}
\textbf{Agda} is a dependently typed functional programming language and proof assistant.
\end{frame}

\begin{frame}{Dependent Types}
Types, in Agda, may \textit{depend} upon values, not just other types.
\end{frame}

\begin{frame}{Inductive Definitions}
\begin{code}
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
\end{code}
% inductive definition should be familiar to Haskell programmers
% notice mixfix, use underscores to denote where we expect arguments
% notice unicode
\end{frame}

\begin{frame}[fragile]{Function Defintions}
% As a new Agda programmer, you might try to define head (like me)
\begin{verbatim}
head₀ : {A : Set} → List A → A
head₀ (x ∷ xs) = x
\end{verbatim}

\pause

\begin{verbatim}
Incomplete pattern matching for head₀. Missing cases:
  head₀ {_} []
when checking the definition of head₀
\end{verbatim}
% Agda functions must be total
% terminating and defined for all inputs
% How do we define head []?
\end{frame}


\begin{frame}{Function Defintions}
\begin{code}
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

head₁ : {A : Set} → List A → Maybe A
head₁ [] = nothing
head₁ (x ∷ xs) = just x
\end{code}
% Nice, but now everywhere we use head we need to check whether nothing is returned
% Cumbersome, and annoying
% We want to guarantee at the time we call head, that it will not be called on an empty list
\end{frame}

\begin{frame}{Function Defintions}
\begin{code}
data Vector (A : Set) : ℕ → Set where
  [] : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

head₂ : {A : Set} {n : ℕ} → Vector A (suc n) → A
head₂ (x ∷ xs) = x
\end{code}
% We can accomplish this with A new dependent type called vector
% Now head is defined just how we'd like, but the type constraints require that it is called on a non-empty vector
\end{frame}

\section{Compiler Correctness}

\begin{frame}
Compiler correctness attempts to verify that a compiler behaves according to its language specification.

The CompCert C compiler has been formally verified with machine-checked proofs that guarantee that the generated code behaves exactly as prescribed by the semantics of the source code.
% That is, the compiler didn't introduce any bugs.
% Verifying the compiler is an incredibly difficult job
% Hopefully tools like Agda make this easier
\end{frame}

\section{Verification}

\begin{frame}{Program Verification}
A Traditional Approach:
\begin{itemize}
    \item Write a program.
    \item Verify its correctness.
\end{itemize}
% Common formal methods approach
% Use any PL
% Doesn't consider well the way that programmers actually program
% Requires advanced automated theorem provers
% ie. Write a C procedure to sort a list. Use frama-C to prove it correct.

\pause

A Synthesis Approach:
\begin{itemize}
    \item Prove that a solution for the problem exists.
    \item Extract a program (solution) from that proof.
\end{itemize}
% Holy Grail of programming
% Currently only feasible for very small programs
% ie. Prove that is possible to write a program that sorts a list, use advanced tools to extract a list sorting algorithm from that proof.

\pause

A DTP (Dependently Typed Programming) Approach:
\begin{itemize}
    \item Program is written in a way which allows one to state properties of program to prove \textit{at the same time}.
\end{itemize}
% Seen frequently in DTP functional projects
% Requires a language that allows you to write "function takes any list as input, and produces a sorted list as output", where "sorted list" is a type constraint that can be validated at compile time
% Produces inherently better documented code
% May be able to fill in pieces automatically
% We do this with a more refined type system that allows us to specify properties of the programs theorems/formulas which are expressed as type constraints
\end{frame}

\section{Verified Compiler in Agda}

\begin{frame}{Write Your Compiler by Proving It Correct}

Toy compiler for an arithmetic expression language, posted by Liam O'Connor, exploring a ``self-certifying compiler''.

Such a compiler written in a dependently typed language, has the immediate advantage of easily encoding ``term wellformedness'' in the type given to terms.
% rather than as a separate proposition that must be assumed by every theorem.
% WFF = recognized by formal language of formulas
\end{frame}

\begin{frame}
For the toy arithmetic expression language, that may mean ensuring that each variable is bound.

Use indices (instead of variable names, for simplicity), and index terms by the number of available variables.
%The `Fin` type, used to represent variables, only contains natural numbers up to its index, which makes it impossible to use variables that are not available.

\begin{code}
data Term (n : ℕ) : Set where
  Lit : ℕ → Term n
  _⊠_ : Term n → Term n → Term n
  _⊞_ : Term n → Term n → Term n
  Let_In_ : Term n → Term (suc n) → Term n
  Var : Fin n → Term n
\end{code}

% add conditions and commands
\end{frame}

\begin{frame}
The interpretation environment can then be expressed as a \texttt{Vec} with a value for every variable in the term.

This makes for an elegantly defined big-step semantics relation.
% That looks a lot more like a textbook definition that usual code.

% I haven't discussed the  Curry-Howard isomorphism, but this is a central premise of Agda that says that there's a direct correspondence between a formula and a type.  Writing a function of type A->B->C is equivalent to writing a proof that, given a proof of A and a proof of B we can prove C.
\begin{code}
infixl 5 _⊢_⇓_
data _⊢_⇓_ {n : ℕ} ( E : Vec ℕ n) : Term n → ℕ → Set where
\end{code}
\end{frame}

\begin{frame}{Big Step Semantics}
\begin{code}
  lit-e   : ∀{n}

            -------------
          → E ⊢ Lit n ⇓ n
\end{code}
\end{frame}

\begin{frame}{Big Step Semantics}
\begin{code}
  times-e : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ v₁
          → E ⊢ e₂ ⇓ v₂
            ---------------------
          → E ⊢ e₁ ⊠ e₂ ⇓ v₁ * v₂

  plus-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ v₁
          → E ⊢ e₂ ⇓ v₂
            ---------------------
          → E ⊢ e₁ ⊞ e₂ ⇓ v₁ + v₂
\end{code}
\end{frame}

\begin{frame}{Big Step Semantics}
\begin{code}
  var-e   : ∀{n}{x}

          → E [ x ]= n
            -------------
          → E ⊢ Var x ⇓ n

  let-e   : ∀{e₁}{e₂}{v₁ v₂}

          → E        ⊢ e₁ ⇓ v₁
          → (v₁ ∷ E) ⊢ e₂ ⇓ v₂
            ---------------------
          → E ⊢ Let e₁ In e₂ ⇓ v₂
\end{code}
\end{frame}
\end{document}
