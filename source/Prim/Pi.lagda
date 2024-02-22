Pi type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Pi where

open import Prim.Type
open import Prim.Morphism
open import Operators.Ring public

Π : {X : 𝓤 ̇} (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

-- We often write Π x ꞉ X , A x for Π A to make X explicit.
Pi : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Pi X Y = Π Y

syntax Pi A (λ x → b) = Π x ꞉ A , b

presheaf-of : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Π Y → Psh X 𝓥
presheaf-of {𝓤} {𝓥} {X} {Y} f = Y

𝒦 : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X → Y → X
𝒦 x = λ _ → x -- K-combinator

𝒮 : {X : 𝓤 ̇} {Y : X → 𝓥 ̇ } {Z : (x : X) → Y x → 𝓦 ̇}
             → ((x : X) → (y : Y x) → Z x y)
             → (f : Π Y) (x : X) → Z x (f x)
𝒮 g f = λ x → g x (f x) -- S-combinator

{-# INLINE 𝒮 #-}

comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → (Π Z) → (f : X → Y) (x : X) → Z (f x)
comp g f = λ x → g (f x)

{-# INLINE comp #-}

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {_} {_} {X} {_} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) →  𝓥 ̇
codomain {_} {_} {_} {Y} f = Y

instance
 Π-comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇} → Op-Ring (Π Z) (X → Y) (λ _ f → Π (comp Z f))
 Π-comp = ∘intro comp

\end{code}

Fixities:

\begin{code}

infixr 5 comp
infixr -1 Pi
infixr 3 Π

\end{code}
