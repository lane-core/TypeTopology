\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type

module Operators.Ring where

record Op-Ring (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (Z : X → Y → 𝓦 ̇ ) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
 constructor ∘intro
 field _∘_ : (x : X) (y : Y) → Z x y

\end{code}
