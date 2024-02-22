\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Fin where

open import Prim.Type
open import Base.Operators
open import Base.Pi
open import Base.Sigma
open import Base.Empty
open import Base.Unit
open import Base.Naturals
open import Base.Plus
open import Base.Id

data Fin : ℕ → 𝓤₀ ̇ where
 zero : {n : ℕ} → Fin (succ n)
 succ : {n : ℕ} → (i : Fin n) → Fin (succ n)

Fin-induction : (P : (n : ℕ) → Fin n → 𝓤 ̇ )
              → ((n : ℕ) → P (succ n) zero)
              → ((n : ℕ) (i : Fin n) → P n i → P (succℕ n) (succ𝔽 i))
              →  (n : ℕ) (i : Fin n) → P n i
Fin-induction P β σ (succℕ n) zero = β n
Fin-induction P β σ (succℕ n) (succ𝔽 i) = σ n i (Fin-induction P β σ n i)

\end{code}

Infixities

\begin{code}

\end{code}
