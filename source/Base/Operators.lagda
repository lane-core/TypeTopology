
Elementary notation and instances

\begin{code}

{-# OPTIONS --safe --without-K  #-}

module Base.Operators where

open import Base.Type
open import Base.Sigma

private variable
 X : 𝓤 ̇
 Y : 𝓥 ̇

\end{code}

General purpose operator records for commonly reused symbols.

First we begin with Transitive, which is meant as a general purpose operator
for any types which have some transitive property.

\begin{code}

record Dot {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
 field
  _∙_ : X → Y → Z

 infixr 2 _∙_

open Dot {{...}} public

\end{code}

Now we have Composition operators, which are meant for any case in which we are
composing functions when we proceed with the composition of terms or types. This
is encouraged notation for more than just function composition proper.

For example, with ap we represent a term with 'f ∘ p' for function (X → Y)
applied on a term x ＝ y with x y ꞉ X; the composition happens on the level of f
being composed on both sides of the equality on the level of the identity type
former itself.

Likewise, with Nat we also represent it as a process of composition for its
transitive property, for its transitive property consists in function composition

The goal is for as many operations are formed by composition that we may proceed with
a common intuitive notation.

\begin{code}

record Compose {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) (Z : ∀ x → Y x → 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
 field
  _∘_ : ∀ x y → Z x y

 infixr 5 _∘_

open Compose {{...}} public

record Identity (X : 𝓤 ̇) (Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 field
  ℯ : ∀ {x} → Y x
  ℰ : ∀ x → Y x

open Identity {{...}} public

record Inverse {𝓤} {𝓥} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇  where
  field
   _⁻¹ : ∀ x → Y x

open Inverse {{...}} public

record Negation {𝓤 𝓥} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 field
  ¬_ : ∀ x → Y x

open Negation {{...}} public

\end{code}

Binary Operators

\begin{code}

record Equality {𝓤} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) : 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇ where
 field _≡_ : ∀ x → Y x → 𝓤 ⊔ 𝓥 ̇

record Sum {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) (Z : ∀ x → Y x → 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
 field
  _+_ : ∀ x y → Z x y

open Sum {{...}} public

record Slash {𝓤 𝓥 𝓦} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) (Z : (x : X) → Y x → 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 where
  field
   _̸_ : ∀ x y → Z x y

open Slash {{...}} public

\end{code}
