Definition of Categories

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Category where

open import Prim.Prelude hiding (Hom)
open import Properties.Associative
open import Properties.Neutral
open import Properties.Set

\end{code}

A precategory 𝓒 consists of a type of objects Ob(𝒞).

\begin{code}

record Precat (Ob : 𝓒 ̇) (𝓤 : Universe) : 𝓒 ⊔ 𝓤 ⁺ ̇ where
 field
  _⟶_ : Ob → Ob → 𝓤 ̇
  Hom-set : (x y : Ob) → is-set (x ⟶ y)
  _·_ : {x y z : Ob} → y ⟶ z → x ⟶ y → x ⟶ z
  unit : {x : Ob} → x ⟶ x
  unitr : {x y : Ob} (f : x ⟶ y) → f · unit ＝ f
  unitl : {x y : Ob} (f : x ⟶ y) → unit · f ＝ f
  Hom-assoc : {w x y z : Ob} (f : y ⟶ z) (g : x ⟶ y) (h : w ⟶ x)
        → f · (g · h) ＝ (f · g) · h

 infixr 8 _⟶_
 infixr 40 _·_

 hom : Ob → Ob → 𝓤 ̇
 hom = _⟶_

 hcomp : {x y z : Ob} → y ⟶ z → x ⟶ y → x ⟶ z
 hcomp = _·_

 hassoc : {w x y z : Ob} (f : y ⟶ z) (g : x ⟶ y) (h : w ⟶ x)
        → f · (g · h) ＝ (f · g) · h
 hassoc = Hom-assoc

 hsrc : {x y : Ob} → x ⟶ y → Ob
 hsrc {x} {y} h = x

 htgt : {x y : Ob} → x ⟶ y → Ob
 htgt {_} {y} h = y

 _ᵒᵖ : Precat Ob 𝓤  → Precat Ob 𝓤
 _⟶_ (C ᵒᵖ) x y = hom y x
 Hom-set (C ᵒᵖ) x y = Hom-set y x
 _·_ (C ᵒᵖ) g f = hcomp f g
 unit (C ᵒᵖ) = unit
 unitr (C ᵒᵖ) = unitl
 unitl (C ᵒᵖ) = unitr
 Hom-assoc (C ᵒᵖ) f g h = {!!}
   where
    _•_ : {x y z  : Ob} → hom z y → hom y x → hom z x
    _•_ g f = hcomp f g



open Precat

ob : {Ob : 𝓒 ̇} → Precat Ob 𝓤 → 𝓒 ̇
ob {_} {_} {Ob} _ = Ob

module _ {Ob : 𝓒 ̇} where





\end{code}

for each object A:Ob(𝒞) and B:Ob(𝒞), a set Hom(A,B) of morphisms

\begin{code}

 -- private
 --  Hom-type : (a b : Ob) → 𝓒 ⁺ ̇
 --  Hom-type a b = Hom a b

\end{code}

for each object A:Ob(𝒞), B:Ob(𝒞), and C:Ob(𝒞), a binary function

  (−)∘[A,B,C](−):Hom(B,C)×Hom(A,B) → Hom(A,C)

\begin{code}

 -- private
 --  hom-comp : {A B C : Ob} → Hom B C → Hom A B → Hom A C
 --  hom-comp p q = trans q p


\end{code}
