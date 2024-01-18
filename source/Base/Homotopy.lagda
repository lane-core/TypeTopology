Function homotopy equivalence

\begin{code}
{-# OPTIONS --safe --without-K #-}

module Base.Homotopy where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Unit
open import Base.Empty
open import Base.Plus
open import Base.Operators public

\end{code}

\begin{code}

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ＝ g x

∼-refl : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f : Π A} → f ∼ f
∼-refl x = refl

∼-trivial : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f : Π A) → f ∼ f
∼-trivial f x = refl

∼-trans : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g h : Π A} → f ∼ g → g ∼ h → f ∼ h
∼-trans h k x = h x ∙ k x

instance
 ∼-Dot : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g h : Π A} → Dot (f ∼ g) (g ∼ h) (f ∼ h)
 _∙_ {{∼-Dot}} = ∼-trans

∼-sym : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → g ∼ f
∼-sym h x = h x ⁻¹

instance
 ∼-Inverse : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → Inverse (f ∼ g) (λ _ → g ∼ f)
 _⁻¹ {{∼-Inverse}} = ∼-sym

∼-ap : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {E : 𝓦 ̇ } (F : E → Π A) {e e' : E}
     → e ＝ e' → F e ∼ F e'
∼-ap F p x = ap (λ - → F - x) p

_∼⟨_⟩_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : Π A) {g h : Π A}
       → f ∼ g → g ∼ h → f ∼ h
_ ∼⟨ p ⟩ q = ∼-trans p q

_∼∎ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : Π A) → f ∼ f
_∼∎ _ = ∼-refl

∼-comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {f g : X → Y} {h k : Y → Z}
              → h ∼ k → f ∼ g → h ∘ f ∼ k ∘ g
∼-comp {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} {h} {k} p q x =
 (sym (q x) ↝ (λ u → h u ＝ k (g x)))  (p (g x))

instance
 ∼-Comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {f g : X → Y} {h k : Y → Z}
        → Compose (h ∼ k) (λ _ → f ∼ g) (λ _ _ → h ∘ f ∼ k ∘ g)
 _∘_ {{∼-Comp}} = ∼-comp

∼-id-neutral : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {g : Y → Y} {h : X → Y}
             → g ∘ f ∼ h → g ∼ id → f ∼ h
∼-id-neutral p i = (i ∘ ∼-refl) ⁻¹ ∙ p

\end{code}



\begin{code}

-- homotopy-cell : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f g : X → Y) → 𝓤
-- homotopy-cell =

\end{code}



\end{code}

Idtofun

\begin{code}

Idtofun : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Idtofun = transport id

Idtofun-retraction : {X Y : 𝓤 ̇ } (p : X ＝ Y) → Idtofun p ∘ Idtofun (p ⁻¹) ∼ id
Idtofun-retraction refl _ = refl

Idtofun-section : {X Y : 𝓤 ̇ } (p : X ＝ Y) → Idtofun (p ⁻¹) ∘ Idtofun p ∼ id
Idtofun-section refl _ = refl

Idtofun⁻¹ : {X Y : 𝓤 ̇ } → X ＝ Y → Y → X
Idtofun⁻¹ = transport⁻¹ id

\end{code}

\begin{code}

{-# DISPLAY trans p q = p ∙ q #-}

\end{code}

Infixities

\begin{code}

infix  4 _∼_
infix  1 _∼∎
infixr 0 _∼⟨_⟩_

\end{code}
