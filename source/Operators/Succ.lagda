\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type

module Operators.Succ (X : 𝓤 ̇) (f : X → X) where

record `succ` : 𝓤 ̇ where
 field
  succ : X → X

open `succ` {{...}} public

instance
 op-succ : `succ`
 succ ⦃ op-succ ⦄ = f

\end{code}
