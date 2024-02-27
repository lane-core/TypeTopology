This type witnesses the destination of a source x : X after applying
some function f, I am calling it the Image type. The constructor
denotes a path sending some x to another point in the Codomain of f. The
identity type becomes a specific case of this, and the notation for path
becomes intuitive because definitionally refl is a path from a term to itself
as witnessed by id ꞉ x ⟶ x. But also from this type, you naturally get the others:
The sigma type, the Pi type, as well as the identity type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Path where

open import Prim.Type
open import Prim.Function
open import Prim.Pi
open import Prim.Sigma

open import Operators.Bullet public
open import Operators.Inverse public
open import Operators.Ring public

data _꞉_⟶_ {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (f : Π Y) (x : X) : Y x → 𝓤 ⊔ 𝓥  ̇ where
 path : f ꞉ x ⟶ f x

Path : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Π Y → (x : X) → Y x → 𝓤 ⊔ 𝓥 ̇
Path f x y = f ꞉ x ⟶ y

Fiber : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f : Π A) {x : X} (y : A x) → 𝓤 ⊔ 𝓥 ̇
Fiber f {x} y = Path f x y

Jbased : {X : 𝓤 ̇} (x : X) {Y : X → 𝓥 ̇} {f : ∀ x → Y x}
  → (A : ∀ y → f ꞉ x ⟶ y → 𝓦 ̇) → A (f x) path
  → (y : Y x) (r : f ꞉ x ⟶ y) → A y r
Jbased x {Y} {f} A b .(f x) path = b

𝕁 : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : ∀ x → Y x}
  → (A : ∀ x y → f ꞉ x ⟶ y → 𝓦 ̇) → (∀ x → A x (f x) path)
  → {x : X} {y : Y x} → (r : f ꞉ x ⟶ y) → A x y r
𝕁 A f {x} path = f x

_＝_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
_＝_ = Path id

Id : (X : 𝓤 ̇) → X → X → 𝓤 ̇
Id X = Path id

Hom : {X : 𝓤 ̇} → X → X → 𝓤  ̇
Hom = Path id

refl : {X : 𝓤 ̇} {x : X} → x ＝ x
refl = path

erefl : {X : 𝓤 ̇} (x : X) → x ＝ x
erefl = λ _ → refl

_∎ : {X : 𝓤 ̇} (x : X) → x ＝ x
_∎ = λ _ → refl

route : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : (x : X) → Y x} {x : X} {y : Y x}
       → f ꞉ x ⟶ y → Π Y
route {𝓤} {𝓥} {X} {Y} {f} p = f

source : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : (x : X) → Y x} {x : X} {y : Y x}
       → f ꞉ x ⟶ y → X
source {𝓤} {𝓥} {X} {Y} {f} {x} p = x

target : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : (x : X) → Y x} {x : X} {y : Y x}
       → f ꞉ x ⟶ y → Y x
target {𝓤} {𝓥} {X} {Y} {f} {x} {y} p = y

recf : {X : 𝓤 ̇} (Y : X → 𝓥 ̇) (A : (x : X) → Y x → 𝓦 ̇)
     (f : Π Y) {x : X} {y : Y x} → Fiber f y → A x (f x) → A x y
recf _ _ _ path = id

-- transportf : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (A : {x : X} → Y x → 𝓦 ̇)
--              {f : Π Y} {x : X} {y : Y x} → Fiber f y → A (f x) → A y
-- transportf A p = Fib-rec _ (λ x y → A ((π p) x) → A y) (π p) p id

-- transportf works across both fiber types and identity types

transportf : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (A : {x : X} → Y x → 𝓦 ̇)
            {f : Π Y} {x : X} {y : Y x} → Fiber f y → A (f x) → A y
transportf A path = id

-- syntax for transportf

syntax transportf (λ x → b) p a = x ↝ p ꞉ a ⇒ b

transport : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X} → x ＝ y → A x → A y
transport A = transportf A

Fibtoid : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (f : Π Y) {x : X} {y : Y x}
        → Fiber f y → f x ＝ y
Fibtoid f p = transportf (f _ ＝_) p refl

Idtofib : {X : 𝓤 ̇} {Y : X → 𝓥 ̇}  (f : Π Y) {x : X} {y : Y x}
        → f x ＝ y → Fiber f y
Idtofib f p = transportf (f ꞉ _ ⟶_) p path

sym : {X : 𝓤 ̇} {x y : X} → x ＝ y → y ＝ x
sym p = transport (λ - → - ＝ source p) p refl

open Op-Inverse {{...}} public renaming (_⁻¹ to infixr 3 _⁻¹)

instance
 symⅈ : {X : 𝓤 ̇} {x y : X} → Op-Inverse (y ＝ x) (x ＝ y)
 _⁻¹ ⦃ symⅈ ⦄ = sym

{-# DISPLAY sym p = p ⁻¹ #-}

id-trans : {X : 𝓤 ̇} {x y z : X} → x ＝ y → y ＝ z → x ＝ z
id-trans p q = transport (λ - → - ＝ target q) (sym p) q

open Op-Bullet {{...}} public renaming (_∙_ to infixr 2 _∙_)
open Op-Ring {{...}} public renaming (_∘_ to infixr 5 _∘_)

instance
 ⅈ₀ : {X : 𝓤 ̇} {x y z : X} → Op-Bullet (x ＝ y) (y ＝ z) (x ＝ z)
 _∙_ ⦃ ⅈ₀ ⦄ = id-trans

 ⅈ₁ : {X : 𝓤 ̇} {x y z : X} → Op-Ring (y ＝ z) (x ＝ y) (λ _ _ → x ＝ z)
 _∘_ ⦃ ⅈ₁ ⦄ q p = id-trans p q

{-# DISPLAY id-trans p q = p ∙ q #-}

refl-lc : {X : 𝓤 ̇} {x y : X} (p : x ＝ y) → refl ∙ p ＝ p
refl-lc path = refl

refl-rc : {X : 𝓤 ̇} {x y : X} (p : x ＝ y) → p ∙ refl ＝ p
refl-rc path = refl

symf : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f g : Π A) {x : X} → Fiber g (f x) → Fiber f (g x)
symf f g p = transport (λ - → Fiber f -) (sym (Fibtoid g p)) path

_∼_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → Fiber f (g x)

Homotopy : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
Homotopy A = _∼_

∼trans : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g h : Π A}
    → f ∼ g → g ∼ h → f ∼ h
∼trans p q x = a ↝ q x ꞉ p x ⇒ Fiber (route (p x)) a

instance
 ⅈ₃ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g h : Π A}
   → Op-Bullet (f ∼ g) (g ∼ h) (f ∼ h)
 _∙_ ⦃ ⅈ₃ ⦄ = ∼trans

_≈_ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇} {x : X} {A : X → 𝓥 ̇}
    → Nat (Id X x) A → Nat (Hom x) A → 𝓤 ⊔ 𝓥 ̇
η ≈ θ = ∀ y → η y ∼ θ y

ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x y : X} (f : X → Y)
   → x ＝ y → f x ＝ f y
ap f p = transport (λ - → f (source p) ＝ f -) p refl

apf : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {Z : 𝓦 ̇} {f : Π A} {x : X}
   (g : A x → Z) {a : A x} → Fiber f a → Fiber g (g a)
apf g p = transport (λ x → g ꞉ x ⟶ g (target p)) (sym (Fibtoid _ p)) path

-- instance
 -- ⅈ₄ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x y : X}
 --    → Op-Ring (X → Y) (x ＝ y) (λ f _ → f x ＝ f y)
 -- _∘_ ⦃ ⅈ₄ ⦄ = ap

Fibtofun : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {Y : 𝓥 ̇} {x : X} → Fiber A Y → A x → Y
Fibtofun A = transportf id

Idtofun : {X Y : 𝓤 ̇} → X ＝ Y → X → Y
Idtofun = Fibtofun id

-- record Graph {𝓤 𝓥} (E : 𝓤 ̇) (V : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
--  no-eta-equality
--  field
--   src : E → V
--   tgt : E → V

--  record Edge (s t : V) : 𝓤 ⊔ 𝓥 ̇ where
--   field
--    edge : E
--    has-src : src edge ＝ s
--    has-tgt : tgt edge ＝ t

--  open Edge {{...}} public

--  data Path-between (s t : V) : 𝓤 ⊔ 𝓥 ̇ where
--   nil : Path-between s t
--   cons : ∀ {v} → Edge s v → Path-between v t → Path-between s t

-- open Graph {{...}} public
-- open Edge {{...}} public

-- instance
--  path-connects-a-graph : {V : 𝓤 ̇} {f g : V → V} {s t : V}
--                        → Graph (f ꞉ s ⟶ g t) V
--  src {{path-connects-a-graph}} = source
--  tgt {{path-connects-a-graph}} = target

-- path-is-an-edge : {V : 𝓤 ̇} {f g : V → V} {s t : V}
--   → f ꞉ s ⟶ g t → Edge {{path-connects-a-graph {𝓤} {V} {f} {g}}} s (g t)
-- edge {{path-is-an-edge p}} = p
-- has-src {{path-is-an-edge p}} = refl
-- has-tgt {{path-is-an-edge p}} = refl

\end{code}

Proofs definitions cited from UF.Base. I decided to fill in where instance
resolution by case matching prevailed before.

\begin{code}

×-hom : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y} → (h : Hom z z') →
 z ＝ (pr₁ (target h) , pr₂ (target h))
×-hom h = h

-- to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} {y y' : Y}
--          → x ＝ x'
--          → y ＝ y'
--          → (x , y) ＝ (x' , y')
-- to-×-＝ p q = ap (λ - → - , source q) p ∙ ap (λ - → target p  , -) q

-- to-×-＝' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
--           → (pr₁ z ＝ pr₁ z') × (pr₂ z ＝ pr₂ z')
--           → z ＝ z'
-- to-×-＝' = uncurry to-×-＝

×⟵＝' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
            → z ＝ z'
            → (pr₁ z ＝ pr₁ z') × (pr₂ z ＝ pr₂ z' )
×⟵＝' p = ap pr₁ p , ap pr₂ p

-- ×⟷＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
--               {z z' : X × Y} (p : z ＝ z')
--             → p ＝ ×⟶＝ (pr₁ (from-×-＝' p)) (pr₂ (×⟵＝' p))
-- ×⟷＝ p = {!!} ∙ ap (λ - → to-×-＝ (pr₁ -) (pr₂ -)) (×-hom ({!p!} ∙ {!!}))

Σ⟵＝' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {u v : Σ Y} (r : u ＝ v)
           → transport Y (ap pr₁ r) (pr₂ u) ＝ (pr₂ v)
Σ⟵＝' {𝓤} {𝓥} {X} {Y} {u} {v} path = path

Σ⟵＝ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {σ τ : Σ Y} (r : σ ＝ τ)
          → Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport Y p (pr₂ σ) ＝ (pr₂ τ)
Σ⟵＝ r = (ap pr₁ r , Σ⟵＝' r)

Σ⟶＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
        → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
        → σ ＝ τ
Σ⟶＝ (path , path) = path

\end{code}

Proof that the classic identity type is equivalent to this one

\begin{code}

open import Prim.Unit
open import Prim.Plus

private
 module _ where
  data _≡_ {X : 𝓤 ̇} : X → X → 𝓤 ̇ where
   rfl : {x : X} → x ≡ x

  transport≡ : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X} → x ≡ y → A x → A y
  transport≡ A rfl = id

  id＝ : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x : X} → (transport A (erefl x)) ＝ (transport≡ A rfl)
  id＝ A = refl

  id≡ : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x : X} → (transport A (erefl x)) ≡ (transport≡ A rfl)
  id≡ A = rfl

  ＝⟶≡ : {X : 𝓤 ̇} {x y : X} → x ＝ y → x ≡ y
  ＝⟶≡ p = transport (λ - → (source p) ≡ -) p rfl

  ≡⟶＝ : {X : 𝓤 ̇} {x y : X} → x ≡ y → x ＝ y
  ≡⟶＝ p = transport≡ (λ - → (lhs p) ＝ -) p refl
   where
    lhs : {X : 𝓤 ̇} {x y : X} → x ≡ y → X
    lhs {_} {_} {x} p = x

    \end{code}

Infixities

\begin{code}
infixr 2 id-trans
infixr 3 sym
infixl 0 _＝_
infixl 0 _꞉_⟶_

\end{code}
