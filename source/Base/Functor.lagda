\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Functor where

open import Base.Type
open import Base.Id
open import Base.Pi

record Functor (F : 𝓤 ̇ → 𝓥 ̇) : 𝓤 ⁺ ⊔ 𝓥 ̇ where
 field
  fmap : {X Y : 𝓤 ̇} → (X → Y) → F X → F Y
  fmap-id : {X : 𝓤 ̇} → fmap {X} {X} id  ＝ id
  fmap-comp : {X Y Z : 𝓤 ̇} (h : X → Y) (g : Y → Z)
            → fmap (g ∘ h) ＝ fmap g ∘ fmap h

open Functor {{...}} public

-- mbmap : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (p : Maybe X) → (X → Maybe (Y x)) → Maybe (Y)
-- mbmap m = ?

-- instance
--  Maybe-Monad : {X : 𝓤 ̇} → Monad Maybe
--  Maybe-Monad = record { pure = just
--                       ; join = {!!}
--                       }

\end{code}
