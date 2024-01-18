\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Maybe where

open import Base.Type
open import Base.Monad
open import Base.Unit
open import Base.Plus

-- mbmap : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (p : Maybe X) → (X → Maybe (Y x)) → Maybe (Y)
-- mbmap m = ?

-- instance
--  Maybe-Monad : {X : 𝓤 ̇} → Monad Maybe
--  Maybe-Monad = record { pure = just
--                       ; join = {!!}
--                       }

\end{code}
