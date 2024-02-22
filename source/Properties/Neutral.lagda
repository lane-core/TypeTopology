\begin{code}

{-# OPTIONS --safe --without-K  #-}

module Properties.Neutral where

open import Prim.Type
open import Prim.Path

is-neutral : {X : 𝓤 ̇} → (X → X) → 𝓤 ̇
is-neutral f = ∀ x → f x ＝ x



\end{code}
