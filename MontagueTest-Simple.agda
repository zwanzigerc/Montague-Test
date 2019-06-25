{-# OPTIONS --without-K #-}
{-# OPTIONS --no-flat-split #-}

{- This file is a demonstration of how to apply Agda-flat (https://github.com/agda/agda/tree/flat) to natural language, in 
particular as a framework for computational Montague semantics. It provides logical forms in Agda-flat for the Montague Test 
sentence suite (Morrill and Valentín 2016).

This is a companion file to the accepted paper

Zwanziger, Colin. (2019). "Dependently-Typed Montague Semantics in the Proof Assistant Agda-flat." Proceedings of the 16th 
Meeting on the Mathematics of Language. July 18-19, 2019. Toronto. -}

module MontagueTest-Simple where

{- We import basic definitions of the HoTT-Agda library (https://github.com/HoTT/HoTT-Agda). -}

open import lib.Basics
open import lib.types.Sigma

{- We import enough of the theory of the comonadic operator ♭. -}

open import Flat

{- I. Lexicon -}

{- We introduce a lexicon (that is, various constants) for use in our translations. -}

postulate
  E : Type₀
  j b : ♭ E
  walk man talk fish woman unicorn park : ♭ E → Type₀
  believe : ♭ Type₀ → ♭ E → Type₀
  seek catch eat find love lose : ♭ (♭ (♭ E → Type₀) → Type₀) → ♭ E → Type₀
  slowly try : ♭ (♭ E → Type₀) → ♭ E → Type₀
  In : ♭ (♭ (♭ E → Type₀) → Type₀) → ♭ (♭ E → Type₀) → ♭ E → Type₀ 

{- II. Montague Test Sentences -}

{- John walks. -}

Johnwalks : Type₀
Johnwalks = walk j

{- Every man talks. -}

Everymantalks : Type₀
Everymantalks = Π (Σ (♭ E) man) (λ x → talk (fst x))

{- The fish walks. -}

Thefishwalks : Type₀
Thefishwalks = Σ (Σ (♭ E) fish) (λ x → (walk (fst x)) × (Π (Σ (♭ E) fish) λ y → y == x))

{- Every man walks or talks. -}

Everymanwot : Type₀
Everymanwot = Π (Σ (♭ E) man) (λ x → (walk (fst x) ⊔ talk (fst x)))

{- A woman walks and she talks. -}

Awomanwast : Type₀
Awomanwast = Σ (Σ (♭ E) woman) (λ x → (walk (fst x) × talk (fst x)))

{- John believes that a fish walks. -}

Johnbelievestafw1  : Type₀
Johnbelievestafw1 = believe (int (Σ (Σ (♭ E) fish) (λ x → walk (fst x)))) j

Johnbelievestafw2 : Type₀
Johnbelievestafw2 = Σ (Σ (♭ E) fish) λ x → Let-int-u-:= (fst x) In λ u → believe (int (walk (int u))) j

{- Every man believes that a fish walks. -}

Everymanbtafw1 : Type₀
Everymanbtafw1 =  Σ (Σ (♭ E) fish) λ x → Let-int-u-:= (fst x) In λ u → Π (Σ (♭ E) man) λ y → believe (int (walk (int u))) (fst y)

Everymanbtafw2 : Type₀
Everymanbtafw2 = Π (Σ (♭ E) man) λ y → Σ (Σ (♭ E) fish) λ x → Let-int-u-:= (fst x) In λ u → believe (int (walk (int u))) (fst y)

Everymanbtafw3 : Type₀
Everymanbtafw3 =  Π (Σ (♭ E) man) λ y → believe (int (Σ (Σ (♭ E) fish) λ x → (walk (fst x)))) (fst y)

{- Every fish such that it walks talks. -}

Everyfishstiwt : Type₀
Everyfishstiwt =  Π (Σ (♭ E) λ y → fish y × walk y) (λ x → talk (fst x))

{- John seeks a unicorn. -}

Johnseeksau1 : Type₀
Johnseeksau1 = seek (int λ P → Σ (Σ (♭ E) unicorn) λ x → ext P (fst x)) j

Johnseeksau2 : Type₀
Johnseeksau2 = Σ (Σ (♭ E) unicorn) λ x → Let-int-u-:= (fst x) In λ u → seek (int (λ P → ext P (int u))) j

{- John is Bill. -}

JohnisBill : Type₀
JohnisBill = j == b

{- John is a man. -}

Johnisaman : Type₀
Johnisaman = man j

{- Necessarily, John walks. -}

NecessarilyJw : Type₀
NecessarilyJw = ♭ (walk j) 

{- John walks slowly. -}

Johnwalksslowly : Type₀
Johnwalksslowly = slowly (int walk) j 

{- John tries to walk. -}

Johntriestowalk : Type₀
Johntriestowalk = try (int walk) j 

{- John tries to catch a fish and eat it. -}
  
Johntriestcaf : Type₀
Johntriestcaf = try (int (λ y → Let-int-u-:= y In λ u → Σ (Σ (♭ E) fish) λ x → catch (int (λ P → ext P (int u))) (fst x) × eat (int (λ P → ext P (int u))) (fst x))) j 

{- John finds a unicorn. -}

Johnfindsau : Type₀
Johnfindsau = Σ (Σ (♭ E) unicorn) λ x → Let-int-u-:= (fst x) In λ u → find (int (λ P → ext P (int u))) j

{- Every man such that he loves a woman loses her. -}
  
Everymansthlow : Type₀
Everymansthlow =  Σ (Σ (♭ E) woman) λ y → Let-int-u-:= (fst y) In λ u → Π (Σ (♭ E) (λ z → man z × love (int (λ P → ext P (int u))) z)) λ x → lose (int (λ P → ext P (int u))) (fst x)
   
{- John walks in a park. -}
   
Johnwalksiap : Type₀
Johnwalksiap = Σ (Σ (♭ E) park) λ x → Let-int-u-:= (fst x) In λ u → In (int (λ P → ext P (int u))) (int walk) j

{- Every man doesn't walk. -}

Everymandw1 : Type₀
Everymandw1 = ¬ (Π (Σ (♭ E) man) (λ x → walk (fst x)))

Everymandw2 : Type₀
Everymandw2 = Π (Σ (♭ E) man) (λ x → ¬ (walk (fst x)))
