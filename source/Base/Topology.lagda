\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Transport where

open import Base.Type
open import Base.Id

∼-refl : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f : Π A} → f ∼ f
∼-refl x = refl

∼-trans : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g h : Π A} → f ∼ g → g ∼ h → f ∼ h
∼-trans h k x = {!h x ∙ ?!}

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ s ꞉ (codomain r → domain r) , (r ∘ s) ∼ id

data _◁_ (Y : 𝓤 ̇) (X : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 retr : (r : X → Y) (s : Y → X) → (r ∘ s) ∼ id → Y ◁ X

◁-trans : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 → Z ◁ Y
                 → Y ◁ X
                 → Z ◁ X
◁-trans (retr r s x) (retr h k y) = retr (r ∘ h) (k ∘ s) {!!}

-- data _∈_ {𝓤} {X : 𝓤  ̇} {U : 𝓤 ⁺ ̇} : (x : X) → U → 𝓤 ⊔ 𝓤 ⁺  ̇ where
--  belongs : {x : X} {u : (type-of X)} → x ∈ {!u ̂!}



_∈_ : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺  ̇
𝓤 ∈ 𝓥  = (𝓤 ̇) ◁ (𝓥 ̇)

--syntax

∈-trans : (𝓧 𝓨 : Universe) → 𝓧 ∈ 𝓨 → 𝓨 ∈ 𝓤 → 𝓧 ∈ 𝓤
∈-trans 𝑥 𝑦 p q = {!!}


pre-universe : (𝓤 : Universe) → 𝓤 ⁺ ̇
pre-universe 𝓤 = {!!}
 where
  I = (𝓧 𝓨 : Universe) → 𝓧 ∈ 𝓨 → 𝓨 ∈ 𝓤 → 𝓧 ∈ 𝓤

-- grothendieck-universe : (𝓤 : Universe) → 𝓤 ⁺ ̇
-- grothendieck-universe 𝓤 = ((𝑢 : 𝓤 ̇) (𝑡 : 𝑢) → 𝑡 ∈ (𝓤 ̇)) × {!!}

--g4 : (I : 𝓤 ̇) → (𝑢 : I → 𝓤 ̇) →

--gu2 : (X : 𝓤 ̇) (x : X) → x ∈ X → ?

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
_ ◁⟨ d ⟩ e = {!!}

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl {𝓤} X = {!!}



\end{code}
