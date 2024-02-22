\begin{code}

{-# OPTIONS --safe --without-K #-}

module Data.Natural where

open import Prim.Type

data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

open import Operators.Succ ℕ suc public

rec : {X : 𝓤 ̇ } → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (suc n) = f (rec x f n)

_^_ : {X : 𝓤 ̇ } → (X → X) → ℕ → (X → X)
(f ^ n) x = rec x f n

induction : {A : ℕ → 𝓤 ̇ } → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n
induction base step 0 = base
induction base step (suc n) = step n (induction base step n)

Seq : (X : 𝓤 ̇) → 𝓤 ̇
Seq X = ℕ → X

\end{code}
