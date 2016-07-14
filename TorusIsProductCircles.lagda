\begin{code}
{-# OPTIONS --without-K --rewriting #-}

open import Rewriting
open import Sigma
open import Torus
open import Circle

{- Map from the torus to the product of two circles -}

to : Torus → Circle × Circle
to = Torus-rec (base , base) (loop ,= idp) (idp ,= loop) (idh {p = loop} ,'□ idv {p = loop})

{- Map from the product of two circles to the torus -}

from : Circle × Circle → Torus
from = λ {(u , v) → from-curry u v} module _ where

  from-curry : Circle → Circle → Torus
  from-curry = Circle-rec loopT2-map (funext from-aux) module _ where

    loopT2-map : Circle → Torus
    loopT2-map = Circle-rec baseT loopT2

    from-aux : (x : Circle) → loopT2-map x == loopT2-map x
    from-aux = Circle-elim loopT1
                           (↓-='-in loopT2-map loopT2-map loop surfT)

{- First composite -}

rew1 : ap from (ap to loopT1) ↦ loopT1
rew1 = ap-cur' from loop (idp :> base == base)
{-# REWRITE rew1 #-}

rew2 : ap from (ap to loopT2) ↦ loopT2
rew2 = ap-cur' from (idp :> base == base) loop
{-# REWRITE rew2 #-}

rew3 : ap□ from (ap□ to surfT) ↦ surfT
rew3 = ap□-cur' from {l = loop} (idh {p = loop}) (idv {p = loop})
{-# REWRITE rew3 #-}
 
loopT1-β : ap (λ z → from (to z)) loopT1 ↦ loopT1
loopT1-β = ap∘ from to loopT1
{-# REWRITE loopT1-β #-}

loopT2-β : ap (λ z → from (to z)) loopT2 ↦ loopT2
loopT2-β = ap∘ from to loopT2
{-# REWRITE loopT2-β #-}

surfT-β : ap□ (λ z → from (to z)) surfT ↦ surfT
surfT-β = ap□∘ from to surfT
{-# REWRITE surfT-β #-}


from-to : (x : Torus) → from (to x) == x
from-to = Torus-elim
  idp
  (↓-='-in (from ∘ to) (λ x → x) loopT1 idv)
  (↓-='-in (from ∘ to) (λ x → x) loopT2 idv)
  (↓-□'-in (from ∘ to) (λ x → x) surfT idhc)

{- Second composite -}

red1 : ap (λ z → to (from-curry base z)) loop ↦ (idp ,= loop)
red1 = ap∘ to (from-curry base) loop
{-# REWRITE red1 #-}

module _ (z : Circle) where
  red2 : ap (λ x → from-curry x z) loop ↦ from-aux z
  red2 = ap∘ (λ h → h z) from-curry loop
  {-# REWRITE red2 #-}

  red3 : ap (λ x → to (from-curry x z)) loop ↦ ap to (from-aux z)
  red3 = ap∘ to (λ x → from-curry x z) loop
  {-# REWRITE red3 #-}

red4 : ap (λ z → ap (λ x → to (from-curry x z)) loop) loop ↦ _
red4 = ap↓∘ (ap to) from-aux loop
{-# REWRITE red4 #-}

red5 : ap↓ (λ {a} → ap to {loopT2-map a} {loopT2-map a})
       {p = loop} (↓-==-eq-in idp surfT) ↦ _
red5 = ap↓-ap-↓-='-in to {p = loop} surfT
{-# REWRITE red5 #-}

to-from : (x : Circle × Circle) → to (from x) == x
to-from (x , y) = to-from-curry y x where

  to-from-curry : (y x : Circle) → to (from-curry x y) == (x , y)
  to-from-curry y =
    Circle-elim (to-from-curry-base y)
                (↓-='-in (λ z → to (from-curry z y)) (λ z → (z , y)) loop
                  (to-from-curry-loop y))  where

    to-from-curry-base : (y : Circle) → to (from-curry base y) == (base , y)
    to-from-curry-base = Circle-elim idp (↓-='-in (to ∘ from-curry base) (λ y → (base , y)) loop idv)

    to-from-curry-loop : (y : Circle) → Square (to-from-curry-base y) (to-from-curry-base y) (ap (λ z → to (from-curry z y)) loop) (ap (λ z → z , y) loop)
    to-from-curry-loop =
      Circle-elim idv
                  (↓-□='-in to-from-curry-base to-from-curry-base (λ z → ap (λ x → to (from-curry x z)) loop) (λ z → ap (λ x → x , z) loop) loop idhc)
\end{code}
