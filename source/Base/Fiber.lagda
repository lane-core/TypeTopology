Fibers

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Fiber where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Retracts
open import Base.Algebra

fiber _⊸_  : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ source f , f x ＝ y
_⊸_ = fiber

fiber-point : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y} → f ⊸ y → X
fiber-point = pr₁

fiber-identification : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y} (w : f ⊸ y)
                     → f (fiber-point w) ＝ y
fiber-identification = pr₂

each-fiber-of : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (X → Y)
              → (𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇)
              → 𝓥 ⊔ 𝓦 ̇
each-fiber-of f P = ∀ y → P (fiber f y)

transport-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  (x x' : X) (y : Y) (p : x ＝ x') (q : f x ＝ y)
                → (p ↝ (λ - → f - ＝ y)) q ＝ (f ◦ (p ⁻¹)) ∙ q
transport-fiber f x .x .(f x) refl refl = refl

-- ftransport : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A :  {f : X → Y}
--              {x : X} {y : Y} {p : f x ＝ y}
--            → f ⊸ y → A (f x)
-- ftransport {𝓤} {𝓥}

cover : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) →
cover = (y : Y) → fiber f y

\end{code}

Paths

\begin{code}

-- lift : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {x y : X} (a : A x) (p : x ＝ y)
--      → x , a ＝ y , (p ↝ A) a
-- lift a p = {!to-Σ-＝ ?!}

\end{code}
