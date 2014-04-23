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

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥ 

data _×_ (A : Set) (B : Set) : Set where
  [_,_] : A → B → A × B

fst : ∀ {A} {B} → A × B → A
fst [ a , _ ] = a

data Var : Set where
  var : String → Var

data LambdaTerm : Set where
  id   : Var → LambdaTerm
  abs : Var → LambdaTerm → LambdaTerm
  app  : LambdaTerm → LambdaTerm → LambdaTerm
 
data Type : Set where
  ⊙     : Type
  _⟼_  : Type → Type → Type


data _≡_ : Var → Var → Set where
  Refl : {x : Var} → x ≡ x
  


mutual
  data Ctx : Set where
    ø      : Ctx
    _▷_｢_｣ : (t : Var × Type) → (π : Ctx) → EsLibre (fst t) π → Ctx

  data EsLibre : Var → Ctx → Set where
    freeEmpty  : {x : Var} → EsLibre x ø
    freeNEmpty : (x : Var) → (π : Ctx) → EsLibre x π →
                 (x' : Var) → (p : EsLibre x' π) → 
                 ¬ (x ≡ x') →
                 EsLibre x ([ x' , _ ] ▷ π ｢ p ｣)

data inCtx : Var × Type → Ctx → Set where
  inHead : (x : Var) → (θ : Type) → (π : Ctx) → 
           (p : EsLibre x π) → inCtx [ x , θ ] ([ x , θ ] ▷ π ｢ p ｣)
  inTail : (x : Var) → (θ : Type) → (π : Ctx) → (x' : Var) → (θ' : Type) →
           inCtx [ x , θ ] π → (p : EsLibre x' π) → 
           inCtx [ x , θ ] ([ x' , θ' ] ▷ π ｢ p ｣)
  

data TypeJudgment : Set where
  _⊢_∷_ : Ctx → LambdaTerm → Type → TypeJudgment

data TypeDeriv : TypeJudgment → Set where
  tdvar : ∀ {x} {θ} {π} →
          inCtx [ x , θ ] π → TypeDeriv (π ⊢ id x ∷ θ)
  tdabs : ∀ {t} {x} {θ} {θ'} {π} → (p : EsLibre x π) →
          TypeDeriv ([ x , θ ] ▷ π ｢ p ｣  ⊢ t ∷ θ') →
          TypeDeriv (π ⊢ (abs x t) ∷ (θ ⟼ θ') )
  tdapp : ∀ {t₁} {t₂} {θ} {θ'} {π} →
          TypeDeriv (π ⊢ t₁ ∷ (θ ⟼ θ')) →
          TypeDeriv (π ⊢ t₂ ∷ θ) →
          TypeDeriv (π ⊢ (app t₁ t₂) ∷ θ')
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