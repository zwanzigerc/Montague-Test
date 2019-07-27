{-# OPTIONS --without-K #-}
{-# OPTIONS --no-flat-split #-}

{- This file formalizes in Agda-flat the logical forms for the Montague Test sentence suite (Morrill and Valentín 2016) 
given in the paper

Zwanziger, Colin. (2019). "Dependently-Typed Montague Semantics in the Proof Assistant Agda-flat." In Proceedings of the 16th
Meeting on the Mathematics of Language. Philippe de Groote, Frank Drewes, and Gerald Penn, eds. Association for Computational 
Linguistics Anthology. https://www.aclweb.org/anthology/papers/W/W19/W19-5704/. -}

module MontagueTest-Official where

{- We import basic definitions of the HoTT-Agda library (https://github.com/HoTT/HoTT-Agda). -}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Empty
open import lib.NType
open import lib.NType2
open import lib.types.Truncation

{- We import our definitions of the usual logical operators within HoTT. -}

open import Logic

{- We import enough of the theory of the comonadic operator ♭. -}

open import Flat

{- I. Lexicon -}

{- We introduce a lexicon (that is, various constants) for use in our translations. -}

postulate
  E : Type₀
  j b : ♭ E
  walk man talk fish woman unicorn park : ♭ E → hProp₀
  believe : ♭ hProp₀ → ♭ E → hProp₀
  seek catch eat find love lose : ♭ (♭ (♭ E → hProp₀) → hProp₀) → ♭ E → hProp₀
  slowly try : ♭ (♭ E → hProp₀) → ♭ E → hProp₀
  In : ♭ (♭ (♭ E → hProp₀) → hProp₀) → ♭ (♭ E → hProp₀) → ♭ E → hProp₀ 

{- II. Montague Test Sentences -}

{- John walks. -}

Johnwalks : hProp₀
Johnwalks = walk j

{- Every man talks. -}

Everymantalks : hProp₀
Everymantalks = all (Σ (♭ E) (fst ∘ man )) (λ x → talk (fst x))

{- The fish walks. -}

Thefishwalks : hProp₀
Thefishwalks = exists (Σ (♭ E) (fst ∘ fish)) (λ x → (walk (fst x)) ∧ (all (Σ (♭ E) (fst ∘ fish)) λ y → Trunc -1 (y == x) , Trunc-level))

{- Every man walks or talks. -}

Everymanwot : hProp₀
Everymanwot = all (Σ (♭ E) (fst ∘ man)) (λ x → (walk (fst x) ∨ talk (fst x)))

{- A woman walks and she talks. -}

Awomanwast : hProp₀
Awomanwast = exists (Σ (♭ E) (fst ∘ woman)) (λ x → (walk (fst x) ∧ talk (fst x)))

{- John believes that a fish walks. -}

Johnbelievestafw1  : hProp₀
Johnbelievestafw1 = believe (int (exists (Σ (♭ E) (fst ∘ fish)) (λ x → walk (fst x)))) j

Johnbelievestafw2 : hProp₀
Johnbelievestafw2 = exists (Σ (♭ E) (fst ∘ fish)) λ x → Let-int-u-:= (fst x) In λ u → believe (int (walk (int u))) j

{- Every man believes that a fish walks. -}

Everymanbtafw1 : hProp₀
Everymanbtafw1 =  exists (Σ (♭ E) (fst ∘ fish)) λ x → Let-int-u-:= (fst x) In λ u → all (Σ (♭ E) (fst ∘ man)) λ y → believe (int (walk (int u))) (fst y)

Everymanbtafw2 : hProp₀
Everymanbtafw2 = all (Σ (♭ E) (fst ∘ man)) λ y → exists (Σ (♭ E) (fst ∘ fish)) λ x → Let-int-u-:= (fst x) In λ u → believe (int (walk (int u))) (fst y)

Everymanbtafw3 : hProp₀
Everymanbtafw3 =  all (Σ (♭ E) (fst ∘ man)) λ y → believe (int (exists (Σ (♭ E) (fst ∘ fish)) λ x → (walk (fst x)))) (fst y)

{- Every fish such that it walks talks. -}

Everyfishstiwt : hProp₀
Everyfishstiwt =  all (Σ (♭ E) λ y → fst (fish y ∧ walk y)) (λ x → talk (fst x))

{- John seeks a unicorn. -}

Johnseeksau1 : hProp₀
Johnseeksau1 = seek (int λ P → exists (Σ (♭ E) (fst ∘ unicorn)) λ x → ext P (fst x)) j

Johnseeksau2 : hProp₀
Johnseeksau2 = exists (Σ (♭ E) (fst ∘ unicorn)) λ x → Let-int-u-:= (fst x) In λ u → seek (int (λ P → ext P (int u))) j

{- John is Bill. -}

JohnisBill : hProp₀
JohnisBill = Trunc -1 (j == b) , Trunc-level

{- John is a man. -}

Johnisaman : hProp₀
Johnisaman = man j

{- Necessarily, John walks. -}

NecessarilyJw : hProp₀
NecessarilyJw = Trunc -1 (♭ ((fst ∘ walk) j)) , Trunc-level

{- John walks slowly. -}

Johnwalksslowly : hProp₀
Johnwalksslowly = slowly (int walk) j 

{- John tries to walk. -}

Johntriestowalk : hProp₀
Johntriestowalk = try (int walk) j 

{- John tries to catch a fish and eat it. -}
  
Johntriestcaf : hProp₀
Johntriestcaf = try (int (λ y → Let-int-u-:= y In λ u → exists (Σ (♭ E) (fst ∘ fish)) λ x → catch (int (λ P → ext P (int u))) (fst x) ∧ eat (int (λ P → ext P (int u))) (fst x))) j 

{- John finds a unicorn. -}

Johnfindsau : hProp₀
Johnfindsau = exists (Σ (♭ E) (fst ∘ unicorn)) λ x → Let-int-u-:= (fst x) In λ u → find (int (λ P → ext P (int u))) j

{- Every man such that he loves a woman loses her. -}
  
Everymansthlow : hProp₀
Everymansthlow =  exists (Σ (♭ E) (fst ∘ woman)) λ y → Let-int-u-:= (fst y) In λ u → all (Σ (♭ E) (λ z → fst (man z ∧ love (int (λ P → ext P (int u))) z))) λ x → lose (int (λ P → ext P (int u))) (fst x)
   
{- John walks in a park. -}
   
Johnwalksiap : hProp₀
Johnwalksiap = exists (Σ (♭ E) (fst ∘ park)) λ x → Let-int-u-:= (fst x) In λ u → In (int (λ P → ext P (int u))) (int walk) j

{- Every man doesn't walk. -}

Everymandw1 : hProp₀
Everymandw1 = not (all (Σ (♭ E) (fst ∘ man)) (λ x → walk (fst x)))

Everymandw2 : hProp₀
Everymandw2 = all (Σ (♭ E) (fst ∘ man)) (λ x → not (walk (fst x)))
