\documentclass{article}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}
 \usepackage{bbm}
 \usepackage[greek,english]{babel}
 \usepackage{amsmath}

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
 \DeclareUnicodeCharacter{955}{\ensuremath{\lambda}}
 \DeclareUnicodeCharacter{10230}{\ensuremath{\longrightarrow}}
 \DeclareUnicodeCharacter{9679}{\ensuremath{\bullet}}
 \DeclareUnicodeCharacter{8348}{\ensuremath{_t}}
 \DeclareUnicodeCharacter{8799}{\ensuremath{\overset{?}{=}}}
 \DeclareUnicodeCharacter{8347}{\ensuremath{_s}}
 \DeclareUnicodeCharacter{7525}{\ensuremath{_v}}
 \DeclareUnicodeCharacter{8343}{\ensuremath{_l}}
 \DeclareUnicodeCharacter{8336}{\ensuremath{_a}}
 

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


\section{Implementación}

Para la implementación utilizaremos varias librerías de Agda:

\begin{code}
module Lambda where

open import Data.Nat hiding (_≟_)
open import Data.String
open import Data.List
open import Data.Bool hiding (_≟_)
open import Data.Empty
-- Para la equivalencia de tipos:
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
-- Para el tipo Bottom y la negación de un tipo:
open import Relation.Nullary
-- Para las 2-uplas:
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Function

\end{code}


Un término del cálculo Lambda podrá ser un identificador (el cual consta de una variable), una abstracción (que consta de una variable y un término) o una aplicación (dos términos).

\begin{code}


data Type : Set where
  ⊙     : Type
  _⟼_  : Type → Type → Type

infixr 100 _⟼_


Var : Set
Var = String

data LambdaTerm : Set where
  ″_″      : Var → LambdaTerm
  λ'_∶_⟶_  : Var → Type → LambdaTerm → LambdaTerm
  _●_      : LambdaTerm → LambdaTerm → LambdaTerm
 
infixl 100 _●_

\end{code}

Como primera aproximación a lo deseado, implementaremos tipos sin variables. Un Tipo podrá ser el "unit" o uno conformado por dos tipos el cual representará a las funciones:

\begin{code}



{-fₜ : Type → Type
fₜ (θ₀ ⟼ θ₁) = θ₀
fₜ _ = {!!}

sₜ : Type → Type
sₜ (θ₀ ⟼ θ₁) = θ₁
sₜ _ = {!!}
-}
\end{code}


Necesitaremos saber si dos tipos son iguales. Para eso definimos una función que dados dos tipos retorna si son o no iguales. El tipo de retorno es Decidable, el cual dada una expresión puede "decidir" si cumple alguna propiedad. En nuestro caso la propiedad es la igualdad proposicional:

\begin{code}

{-
_≟ₜ_ : Decidable  _≡_
⊙ ≟ₜ ⊙ = yes refl
(θ₀ ⟼ θ₁) ≟ₜ (θ₂ ⟼ θ₃) with θ₀ ≟ₜ θ₂ | θ₁ ≟ₜ θ₃
(θ₀ ⟼ θ₁) ≟ₜ (.θ₀ ⟼ .θ₁) | yes refl | yes refl = yes refl
(θ₀ ⟼ θ₁) ≟ₜ (θ₂ ⟼ θ₃)   | no prf   | _        = no (prf ∘ cong fₜ)
(θ₀ ⟼ θ₁) ≟ₜ (θ₂ ⟼ θ₃)   | _        | no prf   = no (prf ∘ cong sₜ)
⊙ ≟ₜ (θ₀ ⟼ θ₁) = no λ()
(θ₀ ⟼ θ₁) ≟ₜ ⊙ = no λ()
-}


\end{code}

Para inferir el tipo de un término necesitamos asignarle tipos a las variables libres que ocurren en el mismo. Para esto definimos un "contexto", el cual puede ser vacío o puede consistir de agregar un par (variable,tipo) a otro contexto. 

Cada variable puede aparecer solo una vez en el contexto (sólo puede tener un tipo), por lo tanto al agregar una variable $x$ con algún tipo al contexto $π$, pediremos también una "prueba" de que $x$ no está en el contexto. Estas "pruebas" las implementamos mediante un tipo de dato que representa justamente lo que queremos: Dada una variable y un contexto, o bien la variable no se encuentra en el contexto porque este es vacío, o bien la variable no se encuentra porque es distinta a la primera que ocurre y tampoco ocurre en el resto del contexto:


También necesitaremos expresar cuando una variable con un tipo sí pertenece a un contexto. Para esto definimos otro tipo de dato. Un par (variable,tipo) puede estar en la "cabeza" de un contexto, o en la "cola".


\begin{code}



mutual
  data Ctx : Set where
    ø      : Ctx
    _▷_｢_｣ : (t : Var × Type) → (π : Ctx) → (p : (proj₁ t) ∉ π) → Ctx

  data _∉_ : Var → Ctx → Set where
    notInEmpty  : {x : Var} → x ∉ ø
    notInNEmpty : {x' : Var} {θ : Type} (x : Var) → (π : Ctx) → x ∉ π →
                  (p : x' ∉ π) → ¬ (x ≡ x') →
                 x ∉ ((x' , θ) ▷ π ｢ p ｣)

data _≈_ : Ctx → Ctx → Set where
  emptyCtxEq : ø ≈ ø
  ctxEq      : ∀ {v} {θ} {π} {π'} → {p : v ∉ π} {p' : v ∉ π'} → 
               π ≈ π' → (v , θ) ▷ π ｢ p ｣ ≈ (v , θ) ▷ π' ｢ p' ｣

-- ≈ es relacion de equivalencia.

reflCtx : ∀ {π} → π ≈ π
reflCtx {ø} = emptyCtxEq
reflCtx {t ▷ π ｢ p ｣} = ctxEq (reflCtx {π})

transCtx : ∀ {π₀} {π₁} {π₂} → π₀ ≈ π₁ → π₁ ≈ π₂ → π₀ ≈ π₂
transCtx emptyCtxEq emptyCtxEq = emptyCtxEq
transCtx (ctxEq π₀≈π₁) (ctxEq π₁≈π₂) = ctxEq (transCtx π₀≈π₁ π₁≈π₂)

symCtx : ∀ {π₀} {π₁} → π₀ ≈ π₁ → π₁ ≈ π₀
symCtx emptyCtxEq = emptyCtxEq
symCtx (ctxEq π₀≈π₁) = ctxEq (symCtx π₀≈π₁)

\end{code}

\begin{code}


data _∈_ : Var × Type → Ctx → Set where
  inHead : ∀ {y} {θ'} → (x : Var) → (θ : Type) → (π : Ctx) → 
             (p : y ∉ π) → x ≡ y → θ ≡ θ' → 
                       ( x  , θ ) ∈ (( y  , θ' ) ▷ π ｢ p ｣)
  inTail : (x : Var) → (θ : Type) → (π : Ctx) → (x' : Var) → 
              (θ' : Type) → ( x  , θ ) ∈ π → (p : x' ∉ π) → 
                 ( x  , θ ) ∈ (( x'  , θ' ) ▷ π ｢ p ｣)


-- Conversión entre v ∉ π y ¬ (∃ (λ θ → (v , θ) ∈ π))
∉↝ : {v : Var} {π : Ctx} → v ∉ π → ¬ (∃ (λ θ → (v , θ) ∈ π))
∉↝ notInEmpty (_ , ())
∉↝ (notInNEmpty v π v∉π v'∉π v≠v') 
   (θ , inHead .v .θ .π .v'∉π v=v' _) = v≠v' v=v'
∉↝ (notInNEmpty v π v∉π v'∉π v≠v') 
   (θ , inTail .v .θ .π v' θ' v∈π .v'∉π) = (∉↝ v∉π) (θ , v∈π)

∉↜ : {v : Var} {π : Ctx} → ¬ (∃ (λ θ → (v , θ) ∈ π)) → v ∉ π
∉↜ {v} {ø} t↑ = notInEmpty
∉↜ {v} {t ▷ π ｢ p ｣} t↑ = notInNEmpty v π (∉↜ (g t↑)) p (f t↑)
  where
    f : {v : Var} {π : Ctx} {v' : Var} {θ' : Type} {p : v' ∉ π} →
      ¬ (∃ (λ θ → (v , θ) ∈ ((v' , θ') ▷ π ｢ p ｣))) →
      ¬ (v ≡ v')
    f {v} {π} {v'} {θ'} {p} t↑ v=v' = 
      t↑ (θ' , inHead v θ' π p v=v' refl)
    
    g : {v : Var} {π : Ctx} {v' : Var} {θ' : Type} {p : v' ∉ π} →
      ¬ (∃ (λ θ → (v , θ) ∈ ((v' , θ') ▷ π ｢ p ｣))) →
      ¬ (∃ (λ θ → (v , θ) ∈ π))
    g {v} {π} {v'} {θ'} {p} t↑ (θ , v∈π) = 
      t↑ (θ , (inTail v θ π v' θ' v∈π p))


  
data _⊢_∷_ : Ctx → LambdaTerm → Type → Set where
  _∣ᵥ : ∀ {x} {θ} {π} →
          ( x  ,′ θ ) ∈ π → (π ⊢ ″ x ″ ∷ θ)

  _∣ₗ : ∀ {t} {x} {θ} {θ'} {π} {p : x ∉ π} → 
          (( x  , θ ) ▷ π ｢ p ｣  ⊢ t ∷ θ') →
          (π ⊢ (λ' x ∶ θ ⟶ t) ∷ (θ ⟼ θ') )

  _∧_∣ₐ : ∀ {t₁} {t₂} {θ} {θ'} {π} →
          (π ⊢ t₁ ∷ (θ ⟼ θ')) →
          (π ⊢ t₂ ∷ θ) →
          (π ⊢ (t₁ ● t₂) ∷ θ')

changeCtxVar : ∀ {x} {θ} {π₀} {π₁} → 
               (x , θ) ∈ π₀ → π₀ ≈ π₁ → (x , θ) ∈ π₁
changeCtxVar x∈π₀ emptyCtxEq = x∈π₀
changeCtxVar {x} {θ} {t ▷ π₀' ｢ p ｣} {.t ▷ π₁' ｢ p' ｣} 
             (inHead .x .θ .π₀' .p x₁ x₂) (ctxEq π₀'≈π₁') = inHead x θ π₁' p' x₁ x₂
changeCtxVar {x} {θ} {(x' , θ') ▷ π₀' ｢ p ｣} {(.x' , .θ') ▷ π₁' ｢ p' ｣} 
             (inTail .x .θ .π₀' .x' .θ' x∈π₀' .p) (ctxEq π₀'≈π₁') = 
                           inTail x θ π₁' x' θ' (changeCtxVar x∈π₀' π₀'≈π₁') p'

change∉ : ∀ {v} {π₀} {π₁} → π₀ ≈ π₁ → v ∉ π₀ → v ∉ π₁
change∉ emptyCtxEq notInEmpty = notInEmpty
change∉ {v} {t ▷ π₀ ｢ p ｣} {.t ▷ π₁ ｢ p' ｣} 
            (ctxEq e) (notInNEmpty .v .π₀ p₀ .p x) = 
              notInNEmpty v π₁ (change∉ e p₀) p' x

changeCtx : ∀ {π₀} {π₁} {t} {θ} → π₀ ⊢ t ∷ θ → π₀ ≈ π₁ → π₁ ⊢ t ∷ θ
changeCtx (x∈π₀ ∣ᵥ) π₀≈π₁ = changeCtxVar x∈π₀ π₀≈π₁ ∣ᵥ
changeCtx {π₀} {π₁} {t = λ' v ∶ θᵥ ⟶ t₀} {θ = .θᵥ ⟼ θ}
          (_∣ₗ {.t₀} {.v} {.θᵥ} {.θ} {.π₀} {x∉π₀} π₀⊢t∷θ) π₀≈π₁ = 
          _∣ₗ {p = change∉ π₀≈π₁ x∉π₀} (changeCtx π₀⊢t∷θ (ctxEq π₀≈π₁)) 
changeCtx (π₀⊢t∷θ ∧ π₀⊢t∷θ₁ ∣ₐ) π₀≈π₁ = 
          (changeCtx π₀⊢t∷θ π₀≈π₁) ∧ (changeCtx π₀⊢t∷θ₁ π₀≈π₁) ∣ₐ

--  ctxEq      : ∀ {v} {θ} {π} {π'} → {p : v ∉ π} {p' : v ∉ π'} → 
  --             π ≈ π' → (v , θ) ▷ π ｢ p ｣ ≈ (v , θ) ▷ π' ｢ p' ｣

-- En esta función probamos que si no existe θ' tal que (v,θ') ∈ π y
-- v≠w, entonces no existe θ' tal que (v,θ') ∈ ((w , θ) ▷ π)
aux'' : (π : Ctx) → (v : Var) → (w : Var) → (θ : Type) → ¬ (v ≡ w) →
        (w∉π : w ∉ π) →  (p : ¬ (∃ (λ θ → (v , θ) ∈ π))) → 
        ¬ (∃ (λ θ' → (v , θ') ∈ ((w , θ) ▷ π ｢ w∉π ｣)))
-- v≠w es una función que toma un elemento de (v ≡ w) y retorna ⊥
aux'' π v w θ v≠w w∉π p (θ' , inHead .v .θ' .π .w∉π v=w q) = v≠w v=w
aux'' π v w θ v≠w w∉π p (θ' , inTail .v .θ' .π .w .θ v∈π .w∉π) = p (θ' , v∈π)


-- Dado un contexto π y una variable v decidimos si existe un tipo θ
-- tal que (v , θ) ∈ π.
v∈π? : (v : Var) → (π : Ctx) → Dec (∃ (λ θ → (v , θ) ∈ π))
v∈π? v ø = no (λ {(θ , ())})
v∈π?  v ( (w , θ) ▷ π ｢ w∉π ｣) with v ≟ w | v∈π? v π
... | yes p | _ = yes (θ , inHead v θ π w∉π p refl)
... | no _  | yes (θ' , v,θ'∈π) = yes (θ' , inTail v θ' π w θ (v,θ'∈π) w∉π)
... | no v≠w  | no pru = no (aux'' π v w θ v≠w w∉π pru)


inferVar : (π : Ctx) → (v : Var) → Dec (∃ (λ θ → π ⊢ ″ v ″ ∷ θ))
inferVar π v with v∈π? v π
inferVar π v | yes (θ' , v∈π) = yes (θ' , v∈π ∣ᵥ)
-- Si v no está en π entonces tenemos una función
-- que dado un elemento de (v,θ') ∈ π retorna ⊥
inferVar π v | no  v∉π = no (λ { (θ' , v∈π ∣ᵥ) → v∉π (θ' , v∈π) })

inferL : {v : Var} {θ : Type} {π : Ctx} {t : LambdaTerm} 
          {p : v ∉ π} → 
          ¬ (∃ (λ θ' → (v , θ) ▷ π ｢ p ｣ ⊢ t ∷ θ')) →
          ¬ (∃ (λ θ'' → π ⊢ λ' v ∶ θ ⟶ t ∷ θ''))
inferL {v} {θ} {π} {t} {p} 
            t↑ (.θ ⟼ θ' , _∣ₗ {.t} {.v} {.θ} {.θ'} {.π} {p'} t∷θ' ) = 
                   t↑ (θ' , changeCtx t∷θ' (ctxEq reflCtx))
inferL t↑ ( ⊙ , () )

inferL2 : ∀ {v} {θᵥ} {θ} {π} {t} → (v , θ) ∈ π → ¬ (∃ (λ θ' → π ⊢ λ' v ∶ θᵥ ⟶ t ∷ θ'))
inferL2 v∈π (⊙ , ())
inferL2 {θ = θ} v∈π (θᵥ ⟼ θ' , _∣ₗ {p = v∉π} π⊢λ't∷θ') = ∉↝ v∉π (θ , v∈π)

infer : (π : Ctx) → (t : LambdaTerm) → Dec (∃ (λ θ → π ⊢ t ∷ θ))
infer π ″ v ″ = inferVar π v
infer π (λ' v ∶ θ ⟶ t) with v∈π? v π
infer π (λ' v ∶ θ ⟶ t) | yes (θᵥ , v∈π) = no (inferL2 {θᵥ = θ} v∈π)
infer π (λ' v ∶ θ ⟶ t) | no v∉π with infer ((v , θ) ▷ π ｢ ∉↜ v∉π ｣) t
infer π (λ' v ∶ θ ⟶ t) | no v∉π | yes (θ' , t∷θ') = yes (θ ⟼ θ' ,  t∷θ' ∣ₗ)
infer π (λ' v ∶ θ ⟶ t) | no v∉π | no t↑ = no (inferL t↑)
infer π (t₁ ● t₂) = {!!}

{-
identity : LambdaTerm
identity = λ' "x"  ⟶ ″ "x" ″ 

θ : Type
θ = (⊙ ⟼ ⊙) ⟼ ⊙ ⟼ ⊙

twice : LambdaTerm
twice = λ' "f" ⟶ λ' "x" ⟶ ″ "f" ″ ● (″ "f" ″ ● ″ "x" ″)

-- No anda
dtwice : LambdaTerm
dtwice = twice ● twice

-- No anda
thrice : LambdaTerm
thrice = λ' "f" ⟶ λ' "x" ⟶ ″ "f" ″ ● (″ "f" ″ ● (″ "f" ″ ● ″ "x" ″))

θ₁ : Type
θ₁ = ⊙ ⟼ ⊙ ⟼ ⊙

t₁ : LambdaTerm
t₁ = λ' "f" ⟶ λ' "x" ⟶ ″ "x" ″

θ₂ : Type
θ₂ = (⊙ ⟼ ⊙) ⟼ (⊙ ⟼ ⊙) ⟼ ⊙ ⟼ ⊙

t₂ : LambdaTerm
t₂ = λ' "g" ⟶ λ' "f" ⟶ λ' "x" ⟶ ″ "g" ″ ● (″ "f" ″ ● ″ "x" ″)

θ₃ : Type
θ₃ = (⊙ ⟼ ⊙) ⟼ (⊙ ⟼ ⊙ ⟼ ⊙) ⟼ ⊙ ⟼ ⊙

t₃ : LambdaTerm
t₃ = λ' "x" ⟶ λ' "f" ⟶ λ' "g" ⟶ ″ "f" ″ ● ″ "g" ″ ● (″ "x" ″ ● ″ "g" ″)

-- No anda
θ₄ : Type
θ₄ = ((⊙ ⟼ ⊙ ⟼ ⊙) ⟼ ⊙) 
         ⟼ ((⊙ ⟼ ⊙ ⟼ ⊙) ⟼ ((⊙ ⟼ ⊙ ⟼ ⊙)  ⟼ ⊙) ⟼ ⊙)
         ⟼ (⊙ ⟼ ⊙ ⟼ ⊙)
         ⟼ ⊙

t₄ : LambdaTerm
t₄ = λ' "x" ⟶ 
     λ' "y" ⟶ 
     λ' "f" ⟶ 
            ″ "f" ″
                  ● (″ "x" ″ ● (λ' "w" ⟶ ″ "f" ″ ● ″ "w" ″))
                  ● (″ "y" ″ ● ″ "f" ″ ● ″ "x" ″)

Δ : LambdaTerm
Δ = λ' "x" ⟶ ″ "x" ″ ● ″ "x" ″

ΔΔ : LambdaTerm
ΔΔ = Δ ● Δ

-}

-- Examples
  
{-
π₁ : Ctx
π₁ = ( ( "y" ,′ ⊙) ▷ ø ｢ notInEmpty ｣)

xNotπ₁ : "x" ∉ π₁
xNotπ₁ = notInNEmpty "x" ø notInEmpty notInEmpty aux
  where aux : ¬ "x" ≡ "y"
        aux ()

tyId : ∀ {θ} → ø ⊢ λ' "x" ⟶ ″ "x" ″ ∷ (θ ⟼ θ)
tyId {θ} = (inHead "x" θ ø notInEmpty refl refl ∣ᵥ) ∣ₗ
-}
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
