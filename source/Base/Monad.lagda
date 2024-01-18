\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Monad where

open import Base.Type
open import Base.Functor
open import Base.Id
open import Base.Equiv
open import Base.Sigma




record Monad {φ : 𝓤 ̇ → 𝓥 ̇} (F : Functor φ) : 𝓤 ⁺ ⊔ 𝓥 ̇ where
  constructor _,_
  field
   pure : {X : 𝓤 ̇} → X → φ X
   pure-section : {s : Section pure} → pr₁ s ＝ ?
   pure-retraction : {r : Retraction pure} → pr₁ r ＝ ?
   join : {X : 𝓤 ̇} → φ (φ X) → φ X

--  _>>=_ : {A B : 𝓤 ̇} → M A → (A → M B) → M B
--  _>>=_ = bind

-- open Monad {{...}} public

-- instance
--  monad-id : Monad (id {𝓤 ⁺})
--  pure {{monad-id}} = id
--  bind {{monad-id}} x f = f x

\end{code}
