Sigma type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Sigma where

open import Prim.Type

record Σ {X : 𝓤 ̇} (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
  constructor
   _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

open Σ public

Sigma : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Sigma _ Y = Σ Y

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

open import Operators.Span public

module SigmaSpan {𝓤 𝓥 : Universe} {X : 𝓤 ̇} {Y : X → 𝓥 ̇} = Operators.Span (Σ Y) pr₁ pr₂

infixr -1 Sigma

private variable
 X : 𝓤 ̇

_×_ : (X : 𝓤 ̇) (Y : 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

uncurry : {Y : X → 𝓥 ̇ } {Z : 𝓦 ̇ } → ((x : X) → Y x → Z) → Σ Y → Z
uncurry f (x , y) = f x y

curry :  {Y : X → 𝓥 ̇ } {Z : 𝓦 ̇ } → (Σ Y → Z) → ((x : X) → Y x → Z)
curry f x y = f (x , y)

×functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
         → (X → A) → (Y → B) → X × Y → A × B
×functor f g (x , y) = f x , g y

\end{code}

Fixities

\begin{code}

infixr 4 _,_
infixr 2 _×_

\end{code}

Set builtin

\begin{code}

{-# BUILTIN SIGMA Sigma #-}

\end{code}
