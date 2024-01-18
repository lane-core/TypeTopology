Elementary notation and instances

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Definitions where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Homotopy
open import Base.Empty
open import Base.Plus

\end{code}

Inverses, Retracts, and Equivalences

\begin{code}

-- Involution : (X : 𝓤 ̇) {Y : 𝓥 ̇} (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
-- Involution X f = Σ e ꞉ Equiv f , pr₁ (pr₁ e) ＝ pr₁ (pr₂ e)

\end{code}

Poset properties

\begin{code}

Reflexive : {X : 𝓤 ̇ } (R : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Reflexive R = ∀ x → R x x

Symmetric : {X : 𝓤 ̇ } → (R : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Symmetric R = ∀ x y → R x y → R y x

Antisymmetric : {X : 𝓤 ̇ } → (R : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Antisymmetric R = ∀ x y → R x y → R y x → x ＝ y

Transitive : {X : 𝓤 ̇ } → (R : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Transitive R = ∀ x y z → R x y → R y z → R x z

\end{code}

Properties of types

\begin{code}

Decidable : 𝓤 ̇ → 𝓤 ̇
Decidable A = A ∔ ¬ A

Distinct₂ : 𝓤 ̇ → 𝓤 ̇
Distinct₂ X = Σ (x , y) ꞉ X × X , (x ≠ y)

Distinct₃ : 𝓤 ̇ → 𝓤 ̇
Distinct₃ X = Σ (x , y , z) ꞉ X × X × X , (x ≠ y) × (y ≠ z) × (z ≠ x)

\end{code}

Cover

\begin{code}

cover : {Z : 𝓤 ̇} (Y : Z → 𝓥 ̇) (X : 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
cover Y X = ∀ i → Y i → X 

\end{code}

Unary function properties

\begin{code}

record Idempotent-Map {X : 𝓥 ̇ } (f : X → X) : 𝓥 ̇
 where
  field
   idempotent : ∀ x → f (f x) ＝ f x

open Idempotent-Map {{...}} public

Left-Cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Left-Cancellable f = ∀ x x' → f x ＝ f x' → x ＝ x'

Right-Cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤ω
Right-Cancellable f = {𝓦 : Universe} {Z : 𝓦 ̇ } (g h : target f → Z)
                    → g ∘ f ∼ h ∘ f
                    → g ∼ h

record Cancellable {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) : 𝓤 ⊔ 𝓥 ̇ where
 field
  cancel : ∀ x y → f x ＝ f y → x ＝ y

open Cancellable {{...}} public

record Neutral (X : 𝓤 ̇) (f : X → X) : 𝓤 ̇
 where
  field
   neutral : ∀ x → f x ＝ x

open Neutral {{...}} public

\end{code}

Binary function properties

\begin{code}

Left-Neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
Left-Neutral e _·_ = ∀ x → e · x ＝ x

Right-Neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
Right-Neutral e _·_ = ∀ x → x · e ＝ x

instance
 Left-Neutral-proof : {X : 𝓤 ̇ } {e : X} {_·_ : X → X → X}
                      {p : Left-Neutral e _·_} → Neutral X (e ·_)
 Left-Neutral-proof {𝓤} {X} {e} {_∙_} {p} = record { neutral = λ x → p x }

 Right-Neutral-proof : {X : 𝓤 ̇ } {e : X} {_·_ : X → X → X}
                       {p : Right-Neutral e _·_} → Neutral X (_· e)
 Right-Neutral-proof {𝓤} {X} {e} {_∙_} {p} = record { neutral = λ x → p x }

record Associative {X : 𝓤 ̇ } (_·_ : X → X → X) : 𝓤 ̇
 where
  field
   assoc : ∀ x y z → (x · y) · z ＝ x · (y · z)

open Associative {{...}} public

record Commutative  {X : 𝓤 ̇} {Y : 𝓥 ̇} (_·_ : X → X → Y) : 𝓤 ⊔ 𝓥 ̇
 where
  field
   comm : ∀ x y → (x · y) ＝ (y · x)

\end{code}

From Notation.CanonicalMap

\begin{code}

record Canonical-Map {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 field
  ι : X → Y

open Canonical-Map {{...}} public

canonical-map : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → {{_ : Canonical-Map X Y}} → X → Y
canonical-map X Y = ι

[_] : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {{ r : Canonical-Map X Y }} → X → Y
[_] = ι
\end{code}


Fixities:

\begin{code}

\end{code}
