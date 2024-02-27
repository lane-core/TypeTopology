Definition of Categories

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Cat.Type where

open import Prim.Prelude
open import Properties.Set
open import Properties.Groupoid

\end{code}

\begin{code}

cat-structure : (ob : 𝓤 ̇) (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
cat-structure ob 𝓥 =
 Σ hom ꞉ (ob → ob → 𝓥 ̇) ,
 Σ idn ꞉ ((A : ob) → hom A A) ,
 ({A B C : ob} → hom A B → hom B C → hom A C)

property-of : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
property-of ob = cat-structure ob 𝓥 → 𝓤 ⊔ 𝓥 ̇

cat-properties : {ob : 𝓤 ̇}
               → (A : cat-axiom 𝓤) → ?
               → cat-structure ob 𝓥
cat-properties {𝓤} s = {!!}

-- precategory-axioms : {ob : 𝓤 ̇} → cat-axioms ob 𝓥
-- precategory-axioms {𝓤} {𝓥} {ob} (hom , idn , seq) =
--  Σ hom-is-set ꞉ ((A B : ob) → is-set (hom A B)) ,
--  Σ idn-L ꞉ ((A B : ob) (f : hom A B) → seq (idn A) f ＝ f) ,
--  Σ idn-R ꞉ ((A B : ob) (f : hom A B) → seq f (idn B) ＝ f) ,
--  ({A B C D : ob} (f : hom A B) (g : hom B C) (h : hom C D)
--          → seq f (seq g h) ＝ seq (seq f g) h)

-- I prefer to use the keyword Cat for Precategories, and Strict Categories
-- for Univalent categories
record Cat (Ob : 𝓤 ̇) (𝓥 : Universe) : 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇ where
 no-eta-equality
 field
  str : cat-structure Ob 𝓥
  ax : cat-properties str

 -- getter functions
 ob : 𝓤 ̇
 ob = Ob

 hom : Ob → Ob → 𝓥 ̇
 hom = pr₁ str

 src : {A B : Ob} → hom A B → Ob
 src {A} = λ _ → A

 tgt : {A B : Ob} → hom A B → Ob
 tgt {_} {B} = λ _ → B

 idn : (A : Ob) → hom A A
 idn = pr₁ (pr₂ str)

 seq : {A B C : Ob} → (f : hom A B) (g : hom (tgt f) C) → hom (src f) (tgt g)
 seq = pr₂ (pr₂ str)

 cmp : {A B C : ob} → (g : hom B C) (f : hom A (src g)) → hom (src f) (tgt g)
 cmp g f = seq f g

 hom-is-set : (A B : ob) → is-set (hom A B)
 hom-is-set A B = pr₁ ax A B

 idn-L : (A B : ob) (f : hom A B) → seq (idn A) f ＝ f
 idn-L A B f = pr₁ (pr₂ ax) A B f

 idn-R : (A B : ob) (f : hom A B) → seq f (idn B) ＝ f
 idn-R A B f = pr₁ (pr₂ (pr₂ ax)) A B f

 assoc : {A B C D : ob} (f : hom A B) (g : hom (tgt f) C) (h : hom (tgt g) D)
         → seq f (seq g h) ＝ seq (seq f g) h
 assoc f g h = pr₁ (pr₂ (pr₂ (pr₂ ax))) f g h

 ext : 𝓤 ⊔ 𝓥 ̇
 ext = pr₂ (pr₂ (pr₂ (pr₂ ax)))

open Cat public

_ᵒᵖ : {X : 𝓤 ̇} → Cat X 𝓥 → Cat X 𝓥
str (_ᵒᵖ {𝓤} {𝓥} {X} C) = (λ (x : X) (y : X) → hom C y x)
          , pr₁ (pr₂ (str C))
          , λ {A} {B} {C = C₁} z z₁ → pr₂ (pr₂ (str C)) z₁ z
ax (_ᵒᵖ {𝓤} {𝓥} {X} C) = (λ A B x y p q → hom-is-set C B A x y p q)
                      , (λ A B p → idn-R C B A p)
                      , (λ A B p → idn-L C B A p)
                      , (λ f g h → assoc C h g f ⁻¹)
                      , ext C

-- Γ induces a category structure for any type X
Γ⟶cat-structure : (X : 𝓤 ̇) → cat-structure X 𝓤
Γ⟶cat-structure X = _＝_ , erefl , id-trans

-- Homotopies also induce a category structure for any function type X to Y
∼⟶cat-structure : (X : 𝓤 ̇) (Y : 𝓥 ̇) → cat-structure (X → Y) (𝓤 ⊔ 𝓥)
∼⟶cat-structure X Y = _∼_ , (λ _ _ → path) , ∼trans

transport-fiber : (X : 𝓤 ̇) (A : X → 𝓥 ̇) {f : X → X} {x y : X} → Path f x y → 𝓥 ̇
transport-fiber X A p = A (source p) → A (target p)

-- its the case that homotopies are sufficient to render displayed categories
-- display-structure : {X : 𝓤 ̇} (C : Cat X 𝓤 ̇) (D : Psh C 𝓥) {a b : C} (f : C → C) → Cat (Π D) (𝓤 ⊔ 𝓥)
-- str (display-structure C D f) = (λ h k → (h ∘ f) ∼ (k ∘ f)) , (λ A x → path) , ∼trans
-- ax (display-structure C D f) = {!!} , {!!}

-- Grpd⟶Cat : {X : 𝓤 ̇} → is-groupoid X → Cat X 𝓤
-- str (Grpd⟶Cat s) = Hom , erefl , id-trans
-- ax (Grpd⟶Cat s) = (λ A B → λ x x₁ x₂ x₃ → {!!}) , {!!}
--  where
--   _ : {!(A B : X) → ?!}
--   _ = s {!ob!} {!!}
  -- field
  -- hom-is-set : (A B : ob) → is-set (hom A B)
  -- idn-L : (A B : ob) → is-set (hom A B)
  -- idn-R : (A B : ob) (f : hom A B) → seq f (idn B) ＝ f
-- -- induces a category on functions
-- CatPathP : (ob : 𝓤 ̇) (Y : 𝓥 ̇) (f : ob → 𝓥 ̇) → category-structure ob 𝓥
-- arr (CatPathP ob f) = λ a b → f a ＝ f b
-- unit (CatPathP ob f) = λ _ → refl
-- atrans (CatPathP ob f) = ?

-- ∼is-cat : Cat 𝓤 𝓤
-- ∼is-cat

\end{code}
