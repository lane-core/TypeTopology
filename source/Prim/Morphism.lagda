\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Morphism where

open import Prim.Type

maps-to : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → ((x : X) → Y x) → (x : X) → Y x
maps-to f = f

syntax maps-to (λ x → b) = x ↦ b

Maps-to : (X : 𝓤 ̇ ) {Y : X → 𝓥 ̇ } → ((x : X) → Y x) → (x : X) → Y x
Maps-to X f = f

syntax Maps-to A (λ x → b) = x ꞉ A ↦ b

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

-- Ambient category of object X
Amb : 𝓤 ̇ → 𝓤 ⁺ ̇
Amb {𝓤} X = 𝓤 ̇

-- Presheaves
Psh : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Psh X 𝓥 = X → 𝓥 ̇

-- Endomorphism
End : 𝓤 ̇ → 𝓤 ̇
End X = X → X

-- Actions
Act : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
Act X Y = X → Y → Y

-- Relations
Rel : (X : 𝓤 ̇) (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Rel X 𝓥 = X → X → 𝓥 ̇

-- Op
op : {Ob : 𝓒 ̇} {U : 𝓤 ̇} → (Ob → Ob → U) → (Ob → Ob → U)
op R x y = R y x

_←_ : (X : 𝓤 ̇) (Y : 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
X ← Y = Y → X

id : {X : 𝓤 ̇} → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇) → X → X
𝑖𝑑 X = id

Nat : {X : 𝓤 ̇} → Psh X 𝓥 → Psh X 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = ∀ x → A x → B x

\end{code}

This will be our reasoning notation, with a suitably overloaded _∙_

\begin{code}

_⨾_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → (x : X) → A x → A x
_ ⨾ p = p

infixr 5 _⨾_

\end{code}

Fixities

\begin{code}

infixl 5 Nat
infixr 10 maps-to
infixr 10 Maps-to

\end{code}
