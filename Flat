{-# OPTIONS --without-K #-}
{-# OPTIONS --no-flat-split #-}

module Flat where

{- This file formalizes enough of the theory of the comonadic operator ♭ for the purposes of the Montague Test. -}

{- We import basic definitions of the HoTT-Agda library (https://github.com/HoTT/HoTT-Agda). -}

open import lib.Basics

{- (As usual for Agda-flat,) we define the comonadic modal type operator ♭ as an inductive type. Here, the constructor is 
called int to highlight the connection to Montague's intension operator. -}

data ♭ {i :{♭} ULevel} (A :{♭} Type i) : Type i where
  int : (a :{♭} A) → ♭ A

{- We define let-substitution, AKA ♭-Elim. This will be used to give logical forms for *de re* modal sentences. -}

Let-int-u-:=_In_ : {j : ULevel} {i :{♭} ULevel} {A :{♭} Type i} {C : ♭ A → Type j}
         → (x : ♭ A)
         → ((u :{♭} A) → C (int u))
         → C x
Let-int-u-:= (int u) In f = f u

{- The notation "Let-int-u-:= s In t" is about the closest thing Agda allows to "let (int u) := s in t". -}

{- We define (what is here called) ext, the extension operator, which can be thought of as a simply-typed eliminator for ♭. -}

ext : {l :{♭} ULevel} {A :{♭} Type l} → (♭ A → A)
ext (int u) = u
