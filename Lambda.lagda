\documentclass{article}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}
 \usepackage{bbm}
 \usepackage[greek,english]{babel}

 % This handles the translation of unicode to latex:

 \usepackage{ucs}
 \usepackage[utf8x]{inputenc}
 \usepackage{autofe}

 % Some characters that are not automatically defined
 % (you figure out by the latex compilation errors you get),
 % and you need to define:

 \DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
 \DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
 \DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
 \DeclareUnicodeCharacter{10236}{\ensuremath{\mapsto}}
 \DeclareUnicodeCharacter{9655}{\ensuremath{\rhd}}
 \DeclareUnicodeCharacter{65378}{\ensuremath{\lceil}}
 \DeclareUnicodeCharacter{65379}{\ensuremath{\rfloor}}
 \DeclareUnicodeCharacter{8759}{\ensuremath{\colon}}
 \DeclareUnicodeCharacter{952}{\ensuremath{\theta}}
 \DeclareUnicodeCharacter{960}{\ensuremath{\pi}}

 % Add more as you need them (shouldn’t happen often).

 % Using “\newenvironment” to redefine verbatim to
 % be called “code” doesn’t always work properly. 
 % You can more reliably use:

 \usepackage{fancyvrb}

 \DefineVerbatimEnvironment
   {code}{Verbatim}
   {} % Add fancy options here if you like.


\title{Implementación de Cálculo Lambda simplemente tipado en Agda}

 \begin{document}

\maketitle



\section{Introducción}

Para aprender a programar con tipos dependientes en Agda nos propusimos
implementar el Cálculo Lambda con un sistema de tipos simple sin anotaciones.




\begin{code}
module Lambda where

open import Data.Nat hiding (_≟_)
open import Data.String
open import Data.List
open import Data.Bool hiding (_≟_)
open import Data.Empty
-- Para la equivalencia de tipos:
open import Relation.Binary.Core
-- Para el tipo Bottom y la negación de un tipo:
open import Relation.Nullary
-- Para las 2-uplas:
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)

Var : Set
Var = String


data LambdaTerm : Set where
  ″_″  : Var → LambdaTerm
  λ'_⟶_  : Var → LambdaTerm → LambdaTerm
  _●_  : LambdaTerm → LambdaTerm → LambdaTerm
 

data Type : Set where
  ⊙     : Type
  _⟼_  : Type → Type → Type

mutual
  data Ctx : Set where
    ø      : Ctx
    _▷_｢_｣ : (t : Var × Type) → (π : Ctx) → (proj₁ t) ∉ π → Ctx

  data _∉_ : Var → Ctx → Set where
    notInEmpty  : {x : Var} → x ∉ ø
    notInNEmpty : {x' : Var} {θ : Type} (x : Var) → (π : Ctx) → x ∉ π →
                  (p : x' ∉ π) → ¬ (x ≡ x') →
                 x ∉ ((x' , θ) ▷ π ｢ p ｣)

data _∈_ : Var × Type → Ctx → Set where
  inHead : ∀ {y} → (x : Var) → (θ : Type) → (π : Ctx) → 
           (p : y ∉ π) → x ≡ y → ( x  , θ ) ∈ (( y  , θ ) ▷ π ｢ p ｣)
  inTail : (x : Var) → (θ : Type) → (π : Ctx) → (x' : Var) → (θ' : Type) →
           ( x  , θ ) ∈ π → (p : x' ∉ π) → 
           ( x  , θ ) ∈ (( x'  , θ' ) ▷ π ｢ p ｣)
  

data _⊢_∷_ : Ctx → LambdaTerm → Type → Set where
  tdvar : ∀ {x} {θ} {π} →
          ( x  ,′ θ ) ∈ π → (π ⊢ ″ x ″ ∷ θ)

  tdabs : ∀ {t} {x} {θ} {θ'} {π} → 
          (p : x ∉ π) → (( x  , θ ) ▷ π ｢ p ｣  ⊢ t ∷ θ') →
          (π ⊢ (λ' x ⟶ t) ∷ (θ ⟼ θ') )

  tdapp : ∀ {t₁} {t₂} {θ} {θ'} {π} →
          (π ⊢ t₁ ∷ (θ ⟼ θ')) →
          (π ⊢ t₂ ∷ θ) →
          (π ⊢ (t₁ ● t₂) ∷ θ')

-- IDEA 1
-- Agregar un constructor a Juicio de Tipado que sea absurdo


-- IDEA 2
inferVar : Ctx → Var → Set
inferVar ø v = ⊥
inferVar ( (w , θ) ▷ π ｢ w∉π ｣ ) v with (w == v)
... | true = ((w , θ) ▷ π ｢ w∉π ｣) ⊢ ″ v ″ ∷ θ
... | false = inferVar π v

v∉π? : (v : Var) → (π : Ctx) → (v ∉ π) ⊎ Unit
v∉π? v ø = inj₁ notInEmpty
v∉π? v ((w , θ) ▷ π ｢ w∉π ｣) with v ≟ w | v∉π? v π
... | no v≠w | inj₁ v∉π  = inj₁ (notInNEmpty v π v∉π w∉π v≠w) 
... |    _   |     _     = inj₂ unit

infer : List Type → Type → Ctx → LambdaTerm → Set
infer _ _ π ″ v ″ = inferVar π v
infer θs (θ₁ ⟼ θ₂) π (λ' v ⟶ t₀)  with v∉π? v π  
... | inj₂ unit = ⊥
... | inj₁ v∉π with infer θs θ₂ ((v , θ₁) ▷ π ｢ v∉π ｣) t₀
... | ⊥ = ⊥
-- ... | ((.v , .θ₁) ▷ .π ｢ .v∉π ｣) ⊢ .t₀ ∷ .θ₂ = ?
infer (θ ∷ θs) θ' π (t₁ ● t₂) with infer θs (θ ⟼ θ') π t₁ | infer θs θ π t₂
--infer (θ ∷ θs) θ' π (t₁ ● t₂) | π ⊢ t₁ ∷ (θ ⟼ θ') | _ = ?
infer (θ ∷ θs) θ' π (t₁ ● t₂) | _ | _ = ⊥
infer _ _ _ _ = ⊥

-- tdapp : ∀ {t₁} {t₂} {θ} {θ'} {π} →
--          (π ⊢ t₁ ∷ (θ ⟼ θ')) →
--          (π ⊢ t₂ ∷ θ) →
--          (π ⊢ (t₁ ● t₂) ∷ θ')

-- infer ø (λ' "x" ⟶ ″ "x" ″) = {θ : _} → ø ⊢ λ' "x" ⟶ ″ "x" ″ ∷ (θ ⟼ θ)
-- infer π ″ v ″ = {!!}
-- infer _ _ = {!!}



  

π₁ : Ctx
π₁ = ( ( "y" ,′ ⊙) ▷ ø ｢ notInEmpty ｣)

xNotπ₁ : "x" ∉ π₁
xNotπ₁ = notInNEmpty "x" ø notInEmpty notInEmpty aux
  where aux : ¬ "x" ≡ "y"
        aux ()

tyId : ∀ {θ} → ø ⊢ λ' "x" ⟶ ″ "x" ″ ∷ (θ ⟼ θ)
tyId {θ} = tdabs notInEmpty (tdvar (inHead "x" θ ø notInEmpty refl))

-- ej1 : ( ( (var "x") ,′ ⊙) ▷ π₁ ｢ xNotπ₁ ｣) ⊢ (id (var "x")) ∷ ⊙
-- ej1 = tdvar (inHead (var "x") ⊙ π₁ xNotπ₁)

-- ej2 : π₁ ⊢ (abs (var "x") (id (var "x"))) ∷ (⊙ ⟼ ⊙)
-- ej2 = tdabs xNotπ₁ ej1


-- data CheckType : Ctx → LambdaTerm → Type → Set where
--   check : 


-- p' : {w : Var} {π : Ctx} (v : Var)  → NotInCtx w π →
--      w ≡ v → NotInCtx v π
-- p' {.v} v p refl = p

-- infer : {θ : Type} → (π : Ctx) → (t : LambdaTerm) → (π ⊢ t ∷ θ)
-- infer {θ} π' (id v) = tdvar (inHead v θ ((v ,′ θ) ▷ ∅ ｢notInEmpty v｣))


  -- where
  --   mkiCtx : (π : Ctx) → (v : Var) → (θ : Type) → inCtx ( v ,′ θ ) π
  --   mkiCtx ( ( .v ,  .θ ) ▷ π ｢ p ｣) v θ = (inHead v θ π p)

  --    else inTail (var v) θ π (var w) θ' (mkiCtx π (var v) θ) p



 \end{code}

 \end{document}




{-
infer : {θ : Type} → (π : Ctx) → (t : LambdaTerm) → 
        TypeDeriv (π ⊢ t ∷ θ)
infer {θ} π (id v) = tdvar (mkiCtx π v θ)

  where

  mkiCtx : (π : Ctx) → (v : Var) → (θ : Type) → inCtx [ v , θ ] π
  mkiCtx ([ var w , θ' ] ▷ π ｢ p ｣) (var v) θ =
    if (w == v) then (inHead (var w) θ' π p)
      else inTail (var v) θ π (var w) θ' (mkiCtx π (var v) θ) p
-}
