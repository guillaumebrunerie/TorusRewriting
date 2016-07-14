\begin{code}
{-# OPTIONS --without-K --rewriting #-}

open import Rewriting

postulate
  Torus : Set
  baseT : Torus
  loopT1 loopT2 : baseT == baseT
  surfT : Square loopT1 loopT1 loopT2 loopT2

module _ {i} {P : Torus → Type i}
    (baseT* : P baseT)
    (loopT1* : PathOver P loopT1 baseT* baseT*)
    (loopT2* : PathOver P loopT2 baseT* baseT*)
    (surfT* : SquareOver P surfT
      loopT1* loopT1* loopT2* loopT2*) where
  postulate
    Torus-elim : (x : Torus) → P x
    Torus-baseT-β : Torus-elim baseT ↦ baseT*
    {-# REWRITE Torus-baseT-β #-}
    Torus-loopT1-β : ap Torus-elim loopT1 ↦ loopT1*
    {-# REWRITE Torus-loopT1-β #-}
    Torus-loopT2-β : ap Torus-elim loopT2 ↦ loopT2*
    {-# REWRITE Torus-loopT2-β #-}
    Torus-surfT-β : ap□ Torus-elim surfT ↦ surfT*
    {-# REWRITE Torus-surfT-β #-}

    -- Torus-loopT1-β-gen : ∀ {j} {Qt : (x : Torus) → Type j} (Q : {x : Torus} (y : P x) → Qt x)
    --   → ap (λ x → Q (Torus-elim x)) loopT1 ↦ ap↓ (λ {x} → Q {x}) {p = loopT1} loopT1*
    -- {-# REWRITE Torus-loopT1-β-gen #-}

{- Non-dependent eliminator, to help with unification -}
module _ {i} {P : Type i}
  (baseT* : P)
  (loopT1* : baseT* == baseT*)
  (loopT2* : baseT* == baseT*)
  (surfT* : Square loopT1* loopT1* loopT2* loopT2*) where

  Torus-rec : Torus → P
  Torus-rec = Torus-elim {P = λ _ → P} baseT* loopT1* loopT2* surfT*
\end{code}
