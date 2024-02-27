Definition of categories a more traditional way. Currently exploring Cat.Type
as an alternative way of defining categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Category where

open import Prim.Prelude
open import Properties.Associative
open import Properties.Neutral
open import Properties.Set

\end{code}

\begin{code}
record category-structure (ob : 𝓤 ̇) (𝓥 : Universe) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
 constructor arr_⨾idn_⨾seq_
 field
  arr : ob → ob → 𝓥 ̇
  unit : (A : ob) → arr A A
  trans : {A B C : ob} → arr A B → arr B C → arr A C

open category-structure

record Precategory : (𝓤 ⊔ 𝓥) ⁺ ̇ where
 no-eta-equality
 field
  ob : 𝓤 ̇
  str : category-structure ob 𝓥
  ax : 𝓥 ̇

 hom : ob → ob → 𝓥 ̇
 hom = arr str

 seq : {A B C : ob} → hom A B → hom B C → hom A C
 seq = atrans str

 cmp : {A B C : ob} → hom B C → hom A B → hom A C
 cmp g f = seq f g

 idn : (A : ob) → hom A A
 idn A = unit str

 field
  hom-is-set : (A B : ob) → is-set (hom A B)
  idn-L : (A B : ob) → is-set (hom A B)
  idn-R : (A B : ob) (f : hom A B) → seq f (idn B) ＝ f
  assoc : (H J K L : ob) (f : hom H J) (g : hom J K) (h : hom K L)
        → seq f (seq g h) ＝ seq (seq f g) h

-- induces a category on functions
CatP : (ob : 𝓤 ̇) → category-structure ob 𝓤
arr (CatP ob) = λ X Y → X → Y
unit (CatP ob) = 𝑖𝑑
atrans (CatP ob) = λ f g → comp g f

-- induces a category on functions
CatPathP : (ob : 𝓤 ̇) (Y : 𝓥 ̇) (f : ob → 𝓥 ̇) → category-structure ob 𝓥
arr (CatPathP ob f) = λ a b → f a ＝ f b
unit (CatPathP ob f) = λ _ → refl
atrans (CatPathP ob f) = ?

-- ∼is-cat : Cat 𝓤 𝓤
-- ∼is-cat

\end{code}
