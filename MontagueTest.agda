{-# OPTIONS --without-K #-}
{-# OPTIONS --no-flat-split #-}

{- This file is a demonstation of how to apply Agda-flat to natural language, in particular as a framework for computational Montague semantics. It provides logical forms in Agda-flat for the Montague Test sentence suite (Morrill and Valentin 2016).

This is a companion file to the submitted paper

Zwanziger, Colin. (2019). "Dependently-Typed Montague Semantics in the Proof Assistant Agda-flat." 16th Meeting on the Mathematics of Language. Toronto. -}

module MontagueTest where

{- We import basic definitions of the HoTT-Agda library. -}

open import lib.Basics
open import lib.types.Sigma

{- (As usual for Agda-flat) we define the comonadic modal type operator ♭ as an inductive type. Here, the constructor is called int to highlight the connection to Montague's intension operator. -}

data ♭ {l :{♭} ULevel} (A :{♭} Type l) : Type l where
  int : (a :{♭} A) → ♭ A

{- We define let-substitution, AKA ♭ elim. -}

letin : {c : ULevel}{l :{♭} ULevel}{A :{♭} Type l}{C : ♭ A → Type c}
         → (x : ♭ A)
         → ((u :{♭} A) → C (int u))
         → C x
letin {A = A} {C = C} (int u) f = f u

{- We define (what is here called) ext, the extension operator, which can be thought of as a simply-typed eliminator for ♭. -}

ext : {l :{♭} ULevel} {A :{♭} Type l} → (♭ A → A)
ext {A = A} (int u) = u

{- We introduce a lexicon (that is, various constants) for use in our translations. -}

postulate
  E : Type0
  j b : ♭ E
  walk man talk fish woman unicorn park : ♭ E → Type0
  believe : ♭ Type0 → ♭ E → Type0
  seek catch eat find love lose : ♭ (♭ (♭ E → Type0) → Type0) → ♭ E → Type0
  slowly try : ♭ (♭ E → Type0) → ♭ E → Type0
  In : ♭ (♭ (♭ E → Type0) → Type0) → ♭ (♭ E → Type0) → ♭ E → Type0 

{- Montague Test Sentences -}

{- John walks. -}

Johnwalks : Type0
Johnwalks = walk j

{- Every man talks. -}

Everymantalks : Type0
Everymantalks = Π (Σ (♭ E) man) (λ x → talk (fst x))

{- The fish walks. -}

Thefishwalks : Type0
Thefishwalks = Σ (Σ (♭ E) fish) (λ x → (walk (fst x)) × (Π (Σ (♭ E) fish) λ y → y == x))

{- Every man walks or talks. -}

Everymanwot : Type0
Everymanwot = Π (Σ (♭ E) man) (λ x → (walk (fst x) ⊔ talk (fst x)))

{- A woman walks and she talks. -}

Awomanwast : Type0
Awomanwast = Σ (Σ (♭ E) woman) (λ x → (walk (fst x) × talk (fst x)))

{- John believes that a fish walks. -}

Johnbelievestafw1  : Type0
Johnbelievestafw1 = believe (int (Σ (Σ (♭ E) fish) (λ x → walk (fst x)))) j

Johnbelievestafw2 : Type0
Johnbelievestafw2 = Σ (Σ (♭ E) fish) λ x → letin (fst x) λ u → believe (int (walk (int u))) j

{- Every man believes that a fish walks. -}

Everymanbtafw1 : Type0
Everymanbtafw1 =  Σ (Σ (♭ E) fish) λ x → letin (fst x) λ u → Π (Σ (♭ E) man) λ y → believe (int (walk (int u))) (fst y)

Everymanbtafw2 : Type0
Everymanbtafw2 = Π (Σ (♭ E) man) λ y → Σ (Σ (♭ E) fish) λ x → letin (fst x) λ u → believe (int (walk (int u))) (fst y)

Everymanbtafw3 : Type0
Everymanbtafw3 =  Π (Σ (♭ E) man) λ y → believe (int (Σ (Σ (♭ E) fish) λ x → (walk (fst x)))) (fst y)

{- Every fish such that it walks talks. -}

Everyfishstiwt : Type0
Everyfishstiwt =  Π (Σ (♭ E) λ y → fish y × walk y) (λ x → talk (fst x))

{- John seeks a unicorn. -}

Johnseeksau1 : Type0
Johnseeksau1 = seek (int λ P → Σ (Σ (♭ E) unicorn) λ x → ext P (fst x)) j

Johnseeksau2 : Type0
Johnseeksau2 = Σ (Σ (♭ E) unicorn) λ x → letin (fst x) λ u → seek (int (λ P → ext P (int u))) j

{- John is Bill. -}

JohnisBill : Type0
JohnisBill = j == b

{- John is a man. -}

Johnisaman : Type0
Johnisaman = man j

{- Necessarily, John walks. -}

NecessarilyJw : Type0
NecessarilyJw = ♭ (walk j) 

{- John walks slowly. -}

Johnwalksslowly : Type0
Johnwalksslowly = slowly (int walk) j 

{- John tries to walk. -}

Johntriestowalk : Type0
Johntriestowalk = try (int walk) j 

{- John tries to catch a fish and eat it. -}
  
Johntriestcaf : Type0
Johntriestcaf = try (int (λ y → letin y λ u → Σ (Σ (♭ E) fish) λ x → catch (int (λ P → ext P (int u))) (fst x) × eat (int (λ P → ext P (int u))) (fst x))) j 

{- John finds a unicorn. -}

Johnfindsau : Type0
Johnfindsau = Σ (Σ (♭ E) unicorn) λ x → letin (fst x) λ u → find (int (λ P → ext P (int u))) j

{-  Every man such that he loves a woman loses her. -}
  
Everymansthlow : Type0
Everymansthlow =  Σ (Σ (♭ E) woman) λ y → letin (fst y) λ u → Π (Σ (♭ E) (λ z → man z × love (int (λ P → ext P (int u))) z)) λ x → lose (int (λ P → ext P (int u))) (fst x)
   
{- John walks in a park. -}
   
Johnwalksiap : Type0
Johnwalksiap = Σ (Σ (♭ E) park) λ x → letin (fst x) λ u → In (int (λ P → ext P (int u))) (int walk) j

{- Every man doesn't walk. -}

Everymandw1 : Type0
Everymandw1 = ¬ (Π (Σ (♭ E) man) (λ x → walk (fst x)))

Everymandw2 : Type0
Everymandw2 = Π (Σ (♭ E) man) (λ x → ¬ (walk (fst x)))

