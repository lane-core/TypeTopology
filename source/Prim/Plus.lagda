Plus

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Plus where

open import Prim.Type
open import Operators.Plus public

data _∔_ {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 inl : X → X ∔ Y
 inr : Y → X ∔ Y

{-# FOREIGN GHC type AgdaEither a b = _∔_ #-}

instance
 Sum-Plus : `+` (𝓤 ̇) (𝓥 ̇) (𝓤 ⊔ 𝓥 ̇)
 _+_ {{Sum-Plus}} = _∔_

\end{code}

Properties

\begin{code}

dep-cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X ∔ Y → 𝓦 ̇ }
          → ((x : X) → A (inl x))
          → ((y : Y) → A (inr y))
          → ((z : X ∔ Y) → A z)
dep-cases f g (inl x) = f x
dep-cases f g (inr y) = g y

cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → X ∔ Y → A
cases = dep-cases

∔-commutative : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A ∔ B → B ∔ A
∔-commutative = cases inr inl

∔functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
         → (X → A) → (Y → B) → X ∔ Y → A ∔ B
∔functor f g (inl x) = inl (f x)
∔functor f g (inr y) = inr (g y)

\end{code}

Fixities

\begin{code}

infixr 1 _∔_

\end{code}
