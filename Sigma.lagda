\begin{code}
{-# OPTIONS --without-K --rewriting #-}

open import Rewriting

record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A × B = Σ A (λ _ → B)

_,'_ : ∀ {i j} {A : Type i} {B : Type j} → A → B → A × B
a ,' b = a , b

module _ {i} {A : Type i} {B : A → Type i} where

  postulate
    _,=_ : {a a' : A} (p : a == a') {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ]) → (a , b) == (a' , b')
    idpΣ : {a : A} {b : B a} → (idp ,= idp) ↦ (idp :> (a , b) == (a , b))
    {-# REWRITE idpΣ #-}

  fst= : {c c' : Σ A B} (p : c == c') → fst c == fst c'
  fst= = ap fst

  snd= : {c c' : Σ A B} (p : c == c') → snd c == snd c' [ B ↓ fst= p ]
  snd= = ap snd

  postulate
    fst=-β : {a a' : A} (p : a == a') {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ]) → ap fst (p ,= q) ↦ p
    {-# REWRITE fst=-β #-}

  rewfst : {a a' : A} (p : a == a') {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ]) → ap (λ z → B (fst z)) (p ,= q) ↦ ap B p
  rewfst p q = ap∘ B fst (p ,= q)
  {-# REWRITE rewfst #-}

  postulate
    snd=-β : {a a' : A} (p : a == a') {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ]) → ap snd (p ,= q) ↦ q
    {-# REWRITE snd=-β #-}

  postulate
    ap-, : ∀ {k} {C : Type k} (f : C → A) (g : (c : C) → B (f c)) {c c' : C} (p : c == c')
      → ap (λ c → (f c , g c) :> Σ A B) p ↦ (ap f p ,= ap g p)
    {-# REWRITE ap-, #-}

{- Nondependent versions (useful for unification, otherwise Agda can’t guess that the [B] is supposed to be constant) -}

module _ {i} {A : Type i} {B : Type i} where

  _,'=_ = _,=_ {A = A} {B = λ _ → B}

  postulate
    _,'□_ :
      {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z} (sq : Square l r t b)
      {w' x' y' z' : B} {l' : w' == y'} {r' : x' == z'} {t' : w' == x'} {b' : y' == z'} (sq' : Square l' r' t' b')
      → Square (l ,'= l') (r ,'= r') (t ,'= t') (b ,'= b')

  postulate
    ap-,'=-cst-idp : {a a' : A} (p : a == a') {b b' : B} (q : b == b') → ap (λ z → p ,'= (idp :> z == z)) q ↦ ↓-==-eq-in idp (idh ,'□ idv)
    {-# REWRITE ap-,'=-cst-idp #-}

module _ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} where

  curry : (f : (ab : Σ A B) → C (fst ab) (snd ab)) → (a : A) (b : B a) → C a b
  curry f a b = f (a , b)

  uncurry : (f : (a : A) (b : B a) → C a b) → (ab : Σ A B) → C (fst ab) (snd ab)
  uncurry f (a , b) = f a b

module _ {i} {A : Type i} {B : A → Type i} {C : Type i} where

  postulate
    ap-λ : (f : (a : A) → B a → C) {x y : A} (p : x == y) {u : B x} {v : B y} (q : u == v [ B ↓ p ]) → app↓= p (ap f p) q ↦ ap (uncurry f) (p ,= q)
    {-# REWRITE ap-λ #-}

module _ {i} {A : Type i} {B : Type i} {C : Type i} where

  curry' : (f : A × B → C) → A → B → C
  curry' f a b = f (a , b)

  uncurry' : (f : A → B → C) → A × B → C
  uncurry' f (a , b) = f a b

  {-
  The following two rewrite rules are inverse to each other. As with the case
  of [ap∘] and [∘ap], we declare one of them as a rewrite rule while the other
  one will need to be redefined by hand for every special case.
  When you do so, you need to make sure that [ap (curry' fu) p] already reduces,
  otherwise you’ll get an infinite loop in the type checker.

  We need both because sometimes the [ap fc p] reduces (when [p] is a
  path-constructor of a HIT and [fc] the eliminator) and sometimes the
  [ap fu (p ,'= q)] does (when [fc = λ a b → a] so that [fu = fst])
  -}

  postulate
    ap-λ' : (fc : A → B → C) {x y : A} (p : x == y) {u v : B} (q : u == v) → app= (ap fc p) q ↦ ap (uncurry' fc) (p ,'= q)
  {-# REWRITE ap-λ' #-}
  
  ap-cur' : (fu : A × B → C) {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    → ap fu (p ,'= q) ↦ app= (ap (curry' fu) p) q
  ap-cur' fu p q = idr

  postulate
    ap-λ□' : (fc : A → B → C) {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z} (sq : Square l r t b)
      {w' x' y' z' : B} {l' : w' == y'} {r' : x' == z'} {t' : w' == x'} {b' : y' == z'} (sq' : Square l' r' t' b')
      → app□ (ap□ fc sq) sq' ↦ ap□ (uncurry' fc) (sq ,'□ sq')
  {-# REWRITE ap-λ□' #-}

  ap□-cur' : (fu : A × B → C) {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z} (sq : Square l r t b)
    {w' x' y' z' : B} {l' : w' == y'} {r' : x' == z'} {t' : w' == x'} {b' : y' == z'} (sq' : Square l' r' t' b')
    → ap□ fu (sq ,'□ sq') ↦ app□ (ap□ (curry' fu) sq) sq'
  ap□-cur' fu p q = idr

{- Very dependent function types -}

module _ {i} {A : Type i} {B : A → Type i} {C : (a : A) → B a → Type i} where

  postulate
    λ↑ : {x y : A} (p : x == y) {u : (w : B x) → C x w} {v : (w : B y) → C y w}
      → ({w : B x} {z : B y} (q : w == z [ B ↓ p ]) → u w == v z [(λ zw → C (fst zw) (snd zw)) ↓ (p ,= q)])
      → u == v [ (λ z → (w : B z) → C z w) ↓ p ]
\end{code}
