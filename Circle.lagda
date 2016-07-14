\begin{code}
{-# OPTIONS --without-K --rewriting #-}

open import Rewriting

postulate
  Circle : Type₀
  base : Circle
  loop : base == base

module _ {i} {P : Circle → Type i}
  (base* : P base)
  (loop* : PathOver P loop base* base*) where
  postulate
    Circle-elim : (x : Circle) → P x
    Circle-base-β : Circle-elim base ↦ base*
    {-# REWRITE Circle-base-β #-}
    Circle-loop-β : ap Circle-elim loop ↦ loop*
    {-# REWRITE Circle-loop-β #-}

{- Non-dependent eliminator, to help with unification -}
module _ {i} {P : Type i} (base* : P) (loop* : base* == base*) where

  Circle-rec : Circle → P
  Circle-rec = Circle-elim {P = λ _ → P} base* loop*
\end{code}
