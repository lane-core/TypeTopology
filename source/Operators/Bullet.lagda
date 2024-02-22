
Elementary notation and instances

\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type

module Operators.Bullet where

record Op-Bullet {𝓤} (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇ where
 constructor ∙intro
 field _∙_ : X → Y → Z

\end{code}
