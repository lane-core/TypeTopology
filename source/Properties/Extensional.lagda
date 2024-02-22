\begin{code}

{-# OPTIONS --safe --without-K  #-}

module Properties.Extensional where

open import Prim.Type
open import Prim.Path

is-extensional : {X : 𝓤 ̇} → (X → X) → 𝓤 ̇
is-extensional f = ∀ x y → f x ＝ f y → x ＝ y

\end{code}
