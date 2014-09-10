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

open import Data.Nat
open import Data.String
open import Data.List
open import Data.Bool
-- Para la equivalencia de tipos:
open import Relation.Binary.Core
-- Para el tipo Bottom y la negación de un tipo:
open import Relation.Nullary
-- Para las 2-uplas:
open import Data.Product

data Var : Set where
  var : String → Var

data LambdaTerm : Set where
  id   : Var → LambdaTerm
  abs  : Var → LambdaTerm → LambdaTerm
  app  : LambdaTerm → LambdaTerm → LambdaTerm
 

data Type : Set where
  ⊙     : Type
  _⟼_  : Type → Type → Type

mutual
  data Ctx : Set where
    ø      : Ctx
    _▷_｢_｣ : (t : Var × Type) → (π : Ctx) → NotInCtx (proj₁ t) π → Ctx

  data NotInCtx : Var → Ctx → Set where
    notInEmpty  : {x : Var} → NotInCtx x ø
    notInNEmpty : {x' : Var} {θ : Type} (x : Var) → (π : Ctx) → NotInCtx x π →
                  (p : NotInCtx x' π) → ¬ (x ≡ x') →
                 NotInCtx x ((x' ,′ θ) ▷ π ｢ p ｣)

data inCtx : Var × Type → Ctx → Set where
  inHead : (x : Var) → (θ : Type) → (π : Ctx) → 
           (p : NotInCtx x π) → inCtx ( x  ,′ θ ) (( x  ,′ θ ) ▷ π ｢ p ｣)
  inTail : (x : Var) → (θ : Type) → (π : Ctx) → (x' : Var) → (θ' : Type) →
           inCtx ( x  ,′ θ ) π → (p : NotInCtx x' π) → 
           inCtx ( x  ,′ θ ) (( x'  ,′ θ' ) ▷ π ｢ p ｣)
  

data _⊢_∷_ : Ctx → LambdaTerm → Type → Set where
  tdvar : ∀ {x} {θ} {π} →
          inCtx ( x  ,′ θ ) π → (π ⊢ id x ∷ θ)
  tdabs : ∀ {t} {x} {θ} {θ'} {π} → (p : NotInCtx x π) →
          (( x  ,′ θ ) ▷ π ｢ p ｣  ⊢ t ∷ θ') →
          (π ⊢ (abs x t) ∷ (θ ⟼ θ') )
  tdapp : ∀ {t₁} {t₂} {θ} {θ'} {π} →
          (π ⊢ t₁ ∷ (θ ⟼ θ')) →
          (π ⊢ t₂ ∷ θ) →
          (π ⊢ (app t₁ t₂) ∷ θ')


π₁ : Ctx
π₁ = ( ( (var "y") ,′ ⊙) ▷ ø ｢ notInEmpty ｣)

xNotπ₁ : NotInCtx (var "x") π₁
xNotπ₁ = notInNEmpty (var "x") ø notInEmpty notInEmpty aux
  where aux : ¬ (var "x") ≡ (var "y")
        aux ()

ej1 : ( ( (var "x") ,′ ⊙) ▷ π₁ ｢ xNotπ₁ ｣) ⊢ (id (var "x")) ∷ ⊙
ej1 = tdvar (inHead (var "x") ⊙ π₁ xNotπ₁)

ej2 : π₁ ⊢ (abs (var "x") (id (var "x"))) ∷ (⊙ ⟼ ⊙)
ej2 = tdabs xNotπ₁ ej1


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