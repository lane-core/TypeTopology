Unit type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Unit where

open import Prim.Type

record 𝟙 {𝓤} : 𝓤 ̇ where
 instance constructor ⋆

open 𝟙 public

unique-to-𝟙 : {A : 𝓤 ̇ } → A → 𝟙 {𝓥}
unique-to-𝟙 {𝓤} {𝓥} a = ⋆ {𝓥}

{-# BUILTIN UNIT 𝟙 #-}

\end{code}
