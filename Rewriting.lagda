\begin{code}
{-# OPTIONS --without-K --rewriting #-}

module Rewriting where

{- Universe levels -}

open import Agda.Primitive renaming (_⊔_ to lmax) public

Type : (i : Level) → Set (lsuc i)
Type i = Set i

Type₀ = Type lzero

ofType : {i : Level} (A : Type i) → A → A
ofType A x = x

syntax ofType A x = x :> A

infixr 3 ofType


{- Rewriting relation -}

postulate
  _↦_ : ∀ {i} {A : Type i} → A → A → Type i
  idr : ∀ {i} {A : Type i} {a : A} → a ↦ a

{-# BUILTIN REWRITE _↦_ #-}

postulate
  ap↦ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b : A} (p : a ↦ b) → f a ↦ f b

{- Identity type -}

infixr 3 _==_

postulate
  _==_ : ∀ {i} {A : Type i} → A → A → Type i
  idp : ∀ {i} {A : Type i} {a : A} → a == a


postulate
  ↦== : ∀ {i} {A : Type i} {a b : A} → a ↦ b → a == b

{- Heterogeneous equality, dependent equality and ap -}

postulate
  HetEq : ∀ {i} {A B : Type i} (e : A == B) (a : A) (b : B) → Type i
  HetEq↦ : ∀ {i} {A : Type i} (a b : A) → HetEq idp a b ↦ (a == b)
  {-# REWRITE HetEq↦ #-}
  PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
    {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
  PathOver↦idp : ∀ {i j} {A : Type i} (B : A → Type j) {x : A} (u v : B x)
    → PathOver B idp u v ↦ (u == v)
  {-# REWRITE PathOver↦idp #-}


syntax PathOver B p u v =
  u == v [ B ↓ p ]

postulate
  PathOver-cst : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (p : x == y) (u v : B) →
    (PathOver (λ _ → B) p u v) ↦ (u == v)
  {-# REWRITE PathOver-cst #-}

-- Note that this is both [ap] and [apd], as a [PathOver] in a constant family
-- reduces to the usual identity type.
postulate
  ap : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
    → (p : x == y) → PathOver B p (f x) (f y)

  ap↦idp : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x : A}
    → ap f (idp {a = x}) ↦ idp
  {-# REWRITE ap↦idp #-}

postulate
  ap-cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) {x y : A} (p : x == y) →
    ap (λ _ → b) p ↦ idp
  {-# REWRITE ap-cst #-}

{-
Intuitively, [PathOver] should be defined using [HetEq], except that for that
we need [ap] for which we need [PathOver]. So we have to define first [PathOver]
and [ap], and then declare a rewrite rule rewriting any [PathOver] to [HetEq].
-}

postulate
  PathOver↦ : ∀ {i j} {A : Type i} (B : A → Type j)
    {x y : A} (p : x == y) (u : B x) (v : B y) → PathOver B p u v ↦ HetEq (ap B p) u v
  {-# REWRITE PathOver↦ #-}

-- [ap] for dependent paths. It might be possible to merge it with [ap] with the
-- appropriate reductions on types but I haven’t tried yet -}
postulate
  ap↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
    (g : {a : A} → B a → C a) {x y : A} {p : x == y}
    {u : B x} {v : B y}
    → (u == v [ B ↓ p ] → g u == g v [ C ↓ p ])

{- Composition of functions -}

_∘_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) (g : A → B) → A → C
f ∘ g = λ x → f (g x)

{- Squares -}

postulate
  Square : ∀ {i} {A : Type i} {w : A} {x y z : A} → w == y → x == z → w == x → y == z → Type i
  ids : ∀ {i} {A : Type i} {w : A} → Square {w = w} idp idp idp idp

  Square-degen : ∀ {i} {A : Type i} {a b : A} {p q : a == b} → p == q → Square idp idp p q
  Square-degen2 : ∀ {i} {A : Type i} {a b : A} {p q : a == b} → p == q → Square p q idp idp
  Square-degen2' : ∀ {i} {A : Type i} {a b : A} {p q : a == b} → Square p q idp idp → p == q

postulate
  HetSquare : ∀ {i} {W X Y Z : Type i} {L : W == Y} {R : X == Z} {T : W == X} {B : Y == Z} (SQ : Square L R T B)
    {w : W} {x : X} {y : Y} {z : Z} (l : HetEq L w y) (r : HetEq R x z) (t : HetEq T w x) (b : HetEq B y z)
    → Type i

  HetSquare↦ : ∀ {i} {A : Type i} {w x y z : A} (l : w == y) (r : x == z) (t : w == x) (b : y == z) → HetSquare ids l r t b ↦ Square l r t b
  {-# REWRITE HetSquare↦ #-}

postulate
  SquareOver : ∀ {i j} {A : Type i} (B : A → Type j) {w x y z : A}
    {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    (sq : Square l r t b)
    {w' : B w} {x' : B x} {y' : B y} {z' : B z}
    (l' : w' == y' [ B ↓ l ]) (r' : x' == z' [ B ↓ r ])
    (t' : w' == x' [ B ↓ t ]) (b' : y' == z' [ B ↓ b ])
    → Type j
  SquareOver↦Square : ∀ {i j} {A : Type i} (B : A → Type j) {w : A}
    {w' x y z : B w} {l : w' == y} {r : x == z} {t : w' == x} {b : y == z}
    → SquareOver B (ids {w = w}) l r t b ↦ Square l r t b
  {-# REWRITE SquareOver↦Square #-}

postulate
  ap□ : ∀ {i j} {A : Type i} {B : A → Type j} (f : (x : A) → B x)
    {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    (sq : Square l r t b)
    → SquareOver B sq (ap f l) (ap f r) (ap f t) (ap f b)

  SquareOver-cst : ∀ {i j} {A : Type i} {B : Type j} {w x y z : A}
    {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    (sq : Square l r t b)
    {w' x' y' z' : B}
    (l' : w' == y') (r' : x' == z')
    (t' : w' == x') (b' : y' == z') →
    SquareOver (λ _ → B) sq l' r' t' b' ↦ Square l' r' t' b'
  {-# REWRITE SquareOver-cst #-}

  ap□-cst : ∀ {i j} {A : Type i} {B : Type j} {b₀ : B}
    {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    (sq : Square l r t b)
    → ap□ (λ _ → b₀) sq ↦ ids
  {-# REWRITE ap□-cst #-}

  SquareOver-rewr : ∀ {i j} {A : Type i} (B : A → Type j) {w x y z : A}
    {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    (sq : Square l r t b)
    {w' : B w} {x' : B x} {y' : B y} {z' : B z}
    (l' : w' == y' [ B ↓ l ]) (r' : x' == z' [ B ↓ r ])
    (t' : w' == x' [ B ↓ t ]) (b' : y' == z' [ B ↓ b ])
    → (SquareOver B sq l' r' t' b' ↦ HetSquare (ap□ B sq) l' r' t' b')
  {-# REWRITE SquareOver-rewr #-}

  idv : ∀ {i} {A : Type i} {a a' : A} {p : a == a'} → Square idp idp p p
  idv-idp : ∀ {i} {A : Type i} {a : A} → idv {p = idp {a = a}} ↦ ids
  {-# REWRITE idv-idp #-}

  ap□-idv : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a a' : A} (p : a == a') →
    ap□ f (idv {p = p}) ↦ idv
  {-# REWRITE ap□-idv #-}

  idh : ∀ {i} {A : Type i} {a a' : A} {p : a == a'} → Square p p idp idp

  Square-degen2-idp : ∀ {i} {A : Type i} {a b : A} {p : a == b} → Square-degen2 (idp {a = p}) ↦ idh
  {-# REWRITE Square-degen2-idp #-}

  diag : ∀ {i} {A : Type i} {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    (sq : Square l r t b) → w == z

  diag-idh : ∀ {i} {A : Type i} {a a' : A} {p : a == a'} → diag (idh {p = p}) ↦ p
  {-# REWRITE diag-idh #-}


postulate
  sym-square : ∀ {i} {A : Type i}
    {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    → Square l r t b → Square t b l r

module _ {i} {A : Type i} where

  postulate
    ap-idf : {x y : A} (p : x == y) → ap (λ x → x) p ↦ p
  {-# REWRITE ap-idf #-}

  postulate
    ap□-idf : {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
      (sq : Square l r t b) →
      ap□ (λ x → x) sq ↦ sq
  {-# REWRITE ap□-idf #-}

{- Dependent identity type in an identity type -}

postulate
  ==-eq : ∀ {i} {A B : Type i} (e : A == B) {a b : A} {c d : B} (p : HetEq e a c) (q : HetEq e b d) → (a == b) == (c == d)
  ==-eq-idp : ∀ {i} {A : Type i} {a b : A} → ==-eq idp {a = a} {b = b} idp idp ↦ idp
  {-# REWRITE ==-eq-idp #-}

module _ {i} {A : Type i} {B : A → Type i} (f g : (a : A) → B a)
  {x y : A} (p : x == y) where

  postulate
    ap-== : ap (λ z → f z == g z) p ↦ ==-eq (ap B p) (ap f p) (ap g p)
    {-# REWRITE ap-== #-}

module _ {i} {A B : Type i} (e : A == B) {a b : A} {c d : B} {p : HetEq e a c} {q : HetEq e b d} {u : a == b} {v : c == d} where

  postulate
    ↓-==-eq-in : HetSquare idv u v p q → HetEq (==-eq e p q) u v
    ↓-==-eq-out : HetEq (==-eq e p q) u v → HetSquare idv u v p q
    ↓-==-eq-β : (sq : HetSquare idv u v p q) → ↓-==-eq-out (↓-==-eq-in sq) ↦ sq
    {-# REWRITE ↓-==-eq-β #-}

postulate
  ↓-==-eq-out-idp : ∀ {i} {A : Type i} {a b : A} {u v : a == b} → ↓-==-eq-out idp {p = idp} {q = idp} {u = u} {v = v} ↦ Square-degen2
  {-# REWRITE ↓-==-eq-out-idp #-}

module _ {i} {A : Type i} {B : A → Type i} (f g : (a : A) → B a)
  {x y : A} (p : x == y) {u : f x == g x} {v : f y == g y} where

  ↓-='-in : HetSquare idv u v (ap f p) (ap g p)
    → u == v [ (λ z → f z == g z) ↓ p ]
  ↓-='-in = ↓-==-eq-in (ap B p)

  ↓-='-out : u == v [ (λ z → f z == g z) ↓ p ]
    → HetSquare idv u v (ap f p) (ap g p)
  ↓-='-out = ↓-==-eq-out (ap B p)

{-
Cubes, in order to deal with dependent squares in the identity type and
dependent paths in the square type.
-}

postulate
  Cube : ∀ {i} {A : Type i} {w : A} {x y z w' x' y' z' : A}
    {ll : w == y} {lr : x == z} {lt : w == x} {lb : y == z}
    (l : Square ll lr lt lb)
    {rl : w' == y'} {rr : x' == z'} {rt : w' == x'} {rb : y' == z'}
    (r : Square rl rr rt rb)
    {w= : w == w'} {x= : x == x'} {y= : y == y'} {z= : z == z'}
    (t : Square w= y= ll rl)
    (b : Square x= z= lr rr)
    (f : Square w= x= lt rt)
    (k : Square y= z= lb rb)
    → Type i
  idc : ∀ {i} {A : Type i} {w : A} → Cube {w = w} ids ids ids ids ids ids

  idhc : ∀ {i} {A : Type i}
    {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
    {sq : Square l r t b}
    → Cube sq sq idv idv idv idv

  coh0 : ∀ {i} {A : Type i} {w x y z : A} {l : w == y} {r : x == z} {t t' : w == x} {b b' : y == z}
    (pt : t == t') (pb : b == b') (α : Square l r t b) → Square l r t' b'

  Cube-degen : ∀ {i} {A : Type i} {w x y z : A} {l : w == y} {r : x == z} {t t' : w == x} {b b' : y == z}
    {pt : t == t'} {pb : b == b'} {α : Square l r t b} {β : Square l r t' b'} → coh0 pt pb α == β → Cube α β idv idv (Square-degen pt) (Square-degen pb)



module _ {i} {A : Type i} {B : Type i} (f g : A → B)
  {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z} (sq : Square l r t b)
  {w= : f w == g w} {x= : f x == g x} {y= : f y == g y} {z= : f z == g z}
  {l= : Square w= y= (ap f l) (ap g l)} {r= : Square x= z= (ap f r) (ap g r)}
  {t= : Square w= x= (ap f t) (ap g t)} {b= : Square y= z= (ap f b) (ap g b)} where

  postulate
    ↓-□'-in : Cube (ap□ f sq) (ap□ g sq) l= r= t= b=
      → SquareOver (λ z → f z == g z) sq (↓-='-in f g l l=) (↓-='-in f g r r=) (↓-='-in f g t t=) (↓-='-in f g b b=)

module _ {i} {A : Type i} {B : Type i} {f g : A → B}
  {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z} {sq : Square l r t b}
  {w= : f w == g w} {x= : f x == g x} {y= : f y == g y} {z= : f z == g z}
  {l= : HetEq (ap (λ z₁ → f z₁ == g z₁) l) w= y=} {r= : HetEq (ap (λ z₁ → f z₁ == g z₁) r) x= z=}
  {t= : HetEq (ap (λ z₁ → f z₁ == g z₁) t) w= x=} {b= : HetEq (ap (λ z₁ → f z₁ == g z₁) b) y= z=} where
  postulate
    ↓-□'-in2 : Cube (ap□ f sq) (ap□ g sq) (↓-='-out f g l l=) (↓-='-out f g r r=) (↓-='-out f g t t=) (↓-='-out f g b b=)
      → SquareOver (λ z → f z == g z) sq l= r= t= b=

module _ {i} {A : Type i} {B : Type i}
  {w x y z : A → B} (l : (e : A) → w e == y e) (r : (e : A) → x e == z e) (t : (e : A) → w e == x e) (b : (e : A) → y e == z e)
  {a a' : A} (p : a == a')
  {sq : Square (l a) (r a) (t a) (b a)} {sq' : Square (l a') (r a') (t a') (b a')} where
  postulate
    ↓-□='-in : Cube (↓-='-out w x p (ap t p)) (↓-='-out y z p (ap b p)) sq sq' (↓-='-out w y p (ap l p)) (↓-='-out x z p (ap r p))
      → PathOver (λ z → Square (l z) (r z) (t z) (b z)) p sq sq'

postulate
  ap□-idh : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a a' : A} (p : a == a') →
    ap□ f (idh {p = p}) ↦ idh {p = ap f p}
{-# REWRITE ap□-idh #-}


module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) where

  {-
    The following two rewrite rules are inverse to each other, so they can’t
    both be defined as rewrite rules or there would be an infinite loop
    (and [ap∘] can’t possibly be a rewrite rule anyway, as there would be no way
    to guess [f] and [g]).
    We need them both, though, for instance we need [∘ap] when [f] is a
    constructor-with-argument of a (higher-)inductive type (like [inl]) and [g]
    the elimination rule, and we need [ap∘] when [p] is a path-constructor of a
    higher-inductive type and [f] the eliminator.

    We handle both of these cases as follows:
    - [∘ap] is declared as a rewrite rule so that the first case is automatic
    - [ap∘] has the type of a rewrite rule but you should define a special case
      of it everytime you need it. In order to avoid the infinite loop, you need
      to do that only when the [ap f p] term already reduces.

    This pattern is repeated for the other variants below, and also in
    [Sigma] for the application of a function of two arguments to two paths.
  -}

  postulate
    ∘ap : {x y : A} (p : x == y) →
      ap g (ap f p) ↦ ap (λ x → g (f x)) p
  {-# REWRITE ∘ap #-}

  -- [ap f p] has to reduce before you declare this as a rewrite rule!
  ap∘ : {x y : A} (p : x == y) →
    ap (λ x → g (f x)) p ↦ ap g (ap f p)
  ap∘ p = idr

  postulate
    ∘ap□ : {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
           (sq : Square l r t b) →
         ap□ g (ap□ f sq) ↦ ap□ (λ x → g (f x)) sq
  {-# REWRITE ∘ap□ #-}

  ap□∘ : {w x y z : A} {l : w == y} {r : x == z} {t : w == x} {b : y == z}
         (sq : Square l r t b) →
    ap□ (λ x → g (f x)) sq ↦ ap□ g (ap□ f sq)
  ap□∘ sq = idr

module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} (g : {a : A} → B a → C a) (f : (a : A) → B a) where

  postulate
    ∘ap↓ : {x y : A} (p : x == y) → ap↓ g {p = p} (ap f p) ↦ ap (λ x → g (f x)) p
  {-# REWRITE ∘ap↓ #-}

  ap↓∘ : {x y : A} (p : x == y) → ap (λ x → g (f x)) p ↦ ap↓ g {p = p} (ap f p)
  ap↓∘ p = idr

module _ {i j k} {A : Type i} {B : Type j} {C : B → Type k} (g : (b : B) → C b) (f : A → B) where

  postulate
    ap↑∘ : {x y : A} (p : x == y) → ap (λ x → g (f x)) p ↦ ap g (ap f p)

postulate
  ap↓-ap-↓-='-in : ∀ {i} {A B C : Type i}
    {f g : A → B} (h : B → C) {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    (sq : Square u v (ap f p) (ap g p)) →
    ap↓ (ap h) {p = p} (↓-='-in f g p sq) ↦ ↓-==-eq-in idp (ap□ h sq) --↓-='-in (h ∘ f) (h ∘ g) p (ap□ h sq)
{-# REWRITE ap↓-ap-↓-='-in #-}

postulate
  ap□-↓-='-out : ∀ {i} {A B C : Type i} (h : B → C)
    {f g : A → B} {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    (eq : u == v [ (λ z → f z == g z) ↓ p ]) →
    ap□ h (↓-='-out f g p eq) ↦ ↓-='-out (h ∘ f) (h ∘ g) p (ap↓ (ap h) {p = p} eq)
{-# REWRITE ap□-↓-='-out #-}


{- Function extensionality -}

module _ {i} {A : Type i} {B : Type i} {f g : A → B} where

  postulate
    -- Intro
    funext3 : ({x y : A} (p : x == y) → f x == g y) → f == g
    -- Elim
    app= : f == g → {x y : A} → x == y → f x == g y
    -- β
    app=↦ : (p : f == g) {x : A} → app= p idp ↦ ap (λ h → h x) p
    {-# REWRITE app=↦ #-}
    funext3-β : (h : {x y : A} (p : x == y) → f x == g y) {x y : A} (p : x == y) → app= (funext3 h) p ↦ h p
    {-# REWRITE funext3-β #-}
    funext3-β' : (h : {x y : A} (p : x == y) → f x == g y) (a : A) → ap (λ h → h a) (funext3 h) ↦ h idp
    {-# REWRITE funext3-β' #-}
    

  funext-thing : (h : (x : A) → f x == g x) {x y : A} (p : x == y) → f x == g y
  funext-thing h p = diag (↓-='-out f g p (ap h p) :> Square (h _) (h _) (ap f p) (ap g p))

  funext : ((x : A) → f x == g x) → f == g
  funext h = funext3 (funext-thing h)
    
postulate
  app□ : ∀ {i} {A : Type i} {B : Type i}
    {w x y z : A → B} {l : w == y} {r : x == z} {t : w == x} {b : y == z} (sq : Square l r t b)
    {w' x' y' z' : A} {l' : w' == y'} {r' : x' == z'} {t' : w' == x'} {b' : y' == z'} (sq' : Square l' r' t' b')
    → Square (app= l l') (app= r r') (app= t t') (app= b b')

  app=idp : ∀ {i} {A : Type i} {B : Type i} {f : A → B} {x y : A} (p : x == y) →
    app= (idp {a = f}) p ↦ ap f p
  {-# REWRITE app=idp #-}

  app□-idh-idv : ∀ {i} {A : Type i} {B : Type i} {f g : A → B} (q : f == g)
    {x y : A} (p : x == y) →
    app□ (idh {p = q}) (idv {p = p}) ↦ ↓-='-out f g p (ap (λ z → app= q (idp {a = z})) p)
  {-# REWRITE app□-idh-idv #-}




{- Natural numbers -}

data ℕ : Type₀ where
  O : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


{- Booleans -}

data Bool : Type₀ where
  true false : Bool

not : Bool → Bool
not true = false
not false = true

notNot : (x : Bool) → not (not x) ↦ x
notNot true = idr
notNot false = idr
{-# REWRITE notNot #-}


{- Unit -}

record Unit : Type₀ where
  constructor tt

-- {- Function types -}

module _ {i j k} {A : Type i} {B : A → Type j} {C : Type k} where

  postulate
    λ↓ : {x y : A} (p : x == y) {u : B x → C} {v : B y → C} →
      ({a : B x} {b : B y} (q : a == b [ B ↓ p ]) → u a == v b) → u == v [ (λ z → B z → C) ↓ p ]

    app↓= : {x y : A} (p : x == y) {u : B x → C} {v : B y → C} →
      u == v [ (λ z → B z → C) ↓ p ] → {b : B x} {b' : B y} (q : b == b' [ B ↓ p ]) → u b == v b'

  postulate
    app↓□ : {wb xb yb zb : A} {lb : wb == yb} {rb : xb == zb} {tb : wb == xb} {bb : yb == zb} (sqb : Square lb rb tb bb)
          {w : B wb → C} {x : B xb → C} {y : B yb → C} {z : B zb → C} {l : w == y [ (λ x → B x → C) ↓ lb ]} {r : x == z [ (λ x → B x → C) ↓ rb ]} {t : w == x [ (λ x → B x → C) ↓ tb ]} {b : y == z [ (λ x → B x → C) ↓ bb ]} (sq : SquareOver (λ x → B x → C) sqb l r t b)
          {w' : B wb} {x' : B xb} {y' : B yb} {z' : B zb} {l' : w' == y' [ B ↓ lb ]} {r' : x' == z' [ B ↓ rb ]} {t' : w' == x' [ B ↓ tb ]} {b' : y' == z' [ B ↓ bb ]} (sq' : SquareOver B sqb l' r' t' b')
          → Square (app↓= lb l l') (app↓= rb r r') (app↓= tb t t') (app↓= bb b b')

    app↓=-λ↓ : {x y : A} (p : x == y) {u : B x → C} {v : B y → C} (h : {a : B x} {b : B y} → (a == b [ B ↓ p ]) → u a == v b)
               {b : B x} {b' : B y} (r : b == b' [ B ↓ p ])
               → app↓= p (λ↓ p {v = v} h) r ↦ h r
{-# REWRITE app↓=-λ↓ #-}
\end{code}
