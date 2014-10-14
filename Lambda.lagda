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


\title{Agda, un lenguaje con tipos dependientes}
\author{Alejandro Gadea, Emmanuel Gunther}

 \begin{document}
 
 
\maketitle



\section{Introducción}

En este trabajo estudiamos la teoría de tipos ....

Para aprender a programar con tipos dependientes en Agda nos propusimos
implementar el Cálculo Lambda con un sistema de tipos simple sin anotaciones.

\section{Teoría de tipos}

un resumen de teoría de tipos, como lo que leímos en homotopy type theory.

\section{Agda}

hablar un poco de las generalidades de agda

\section{Un inferidor de tipos para el cálculo lambda certificado}

\subsection{Descripción del problema}

Como ejercicio práctico para entender la programación con tipos dependientes
nos propusimos implementar un inferidor de tipos para el cálculo lambda, el cual
dado un término $t$ y un contexto de asignaciones de tipos a variables $\pi$, retorne
si existe un tipo $\theta$ tal que $\pi \vdash t :: \theta$ (el término $t$ tiene tipo $\theta$
bajo el contexto $\pi$) o si no existe, en cuyo caso deberá retornar una función que dado
un juicio de tipado $\pi \vdash t :: \theta$ podemos obtener $\bot$ (el tipo vacío), lo cual 
representa una prueba de que para todo tipo $\theta$ no existe juicio de tipado.

Con el programa que queremos implementar no obtendremos solo un resultado para nuestro problema, sino
también una \textbf{prueba} de que el resultado es el correcto.

Por cuestiones de simplicidad, no consideraremos variables de tipo, por lo que un tipo
podrá ser el tipo básico $\odot$ o dados dos tipos $\theta_1$ y $\theta_2$, el tipo $\theta_1 \rightarrow \theta_2$.

Esto nos obliga a que en la abstracción lambda debemos anotar el tipo de la variable, caso contrario por ejemplo
para el término $id = \lambda\,x\,.\,x$ no podríamos distinguir si tiene tipo $\odot \rightarrow \odot$ o 
$(\odot \rightarrow \odot) \rightarrow (\odot \rightarrow \odot)$, etc. Anotando el tipo de la variable, 
los términos ($\lambda\,x : \odot\,.\,x$) y ($\lambda\,x : (\odot \rightarrow \odot)\,.\,x$) son distintos
y evitan esta ambigüedad.


\subsection{Librerías auxiliares}

Para la implementación utilizaremos varias librerías de Agda:

\begin{code}
module Lambda where

open import Data.Empty
open import Data.String
-- Para la equivalencia de tipos:
open import Relation.Binary.PropositionalEquality
-- Para el tipo Bottom y la negación de un tipo:
open import Relation.Nullary
-- Para las 2-uplas:
open import Data.Product
open import Function

\end{code}

String, para representar las variables de los términos. PropositionalEquality tiene definido el tipo de la igualdad
proposicional entre dos tipos, tal como lo explicamos en la sección 2. Nullary para tener el tipo vacío $\bot$.
Y por último el producto que lo necesitamos para representar los pares (variable, tipo) en los contextos.

\subsection{Tipos y Términos del Cálculo Lambda}


Como dijimos previamente, un tipo del cálculo lambda podrá ser el tipo básico $\odot$ ó un 

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

cong⟼⁻¹ : ∀ {θ₁} {θ₂} {θ₁'} {θ₂'} → θ₁ ⟼ θ₂ ≡ θ₁' ⟼ θ₂' → θ₁ ≡ θ₁' × θ₂ ≡ θ₂'
cong⟼⁻¹ refl = refl , refl

-- La igualdad de tipos es decidible
_≟ₜ_ : (θ : Type) → (θ' : Type) → Dec (θ ≡ θ')
⊙ ≟ₜ ⊙ = yes refl
⊙ ≟ₜ θ ⟼ θ' = no (λ ())
θ₁ ⟼ θ₂ ≟ₜ ⊙ = no (λ ())
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' with θ₁ ≟ₜ θ₁' | θ₂ ≟ₜ θ₂'
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' | yes p | yes p' = yes (cong₂ _⟼_ p p')
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' | _ | no ¬p = no (λ θ₁⟼θ₂≡θ₁'⟼θ₂' → ¬p (proj₂ (cong⟼⁻¹ θ₁⟼θ₂≡θ₁'⟼θ₂')))
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' | no ¬p | _ = no (λ θ₁⟼θ₂≡θ₁'⟼θ₂' → ¬p (proj₁ (cong⟼⁻¹ θ₁⟼θ₂≡θ₁'⟼θ₂')))


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
  inTail : (x : Var) → (θ : Type) → (π : Ctx) → (y : Var) → 
              (θ' : Type) → ( x  , θ ) ∈ π → (p : y ∉ π) → 
                 ( x  , θ ) ∈ (( y  , θ' ) ▷ π ｢ p ｣)


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


change∉ : ∀ {v} {π₀} {π₁} → π₀ ≈ π₁ → v ∉ π₀ → v ∉ π₁
change∉ emptyCtxEq notInEmpty = notInEmpty
change∉ {v} {t ▷ π₀ ｢ p ｣} {.t ▷ π₁ ｢ p' ｣} 
            (ctxEq e) (notInNEmpty .v .π₀ p₀ .p x) = 
              notInNEmpty v π₁ (change∉ e p₀) p' x


changeCtxVar : ∀ {x} {θ} {θ'} {π₀} {π₁} → 
               (x , θ) ∈ π₀ → π₀ ≈ π₁ → θ ≡ θ' → (x , θ') ∈ π₁
changeCtxVar x∈π₀ emptyCtxEq refl = x∈π₀
changeCtxVar {x} {θ} {.θ} {t ▷ π₀' ｢ p ｣} {.t ▷ π₁' ｢ p' ｣} 
             (inHead .x .θ .π₀' .p x₁ x₂) (ctxEq π₀'≈π₁') refl = inHead x θ π₁' p' x₁ x₂
changeCtxVar {x} {θ} {.θ} {(x' , θ') ▷ π₀' ｢ p ｣} {(.x' , .θ') ▷ π₁' ｢ p' ｣} 
             (inTail .x .θ .π₀' .x' .θ' x∈π₀' .p) (ctxEq π₀'≈π₁') refl = 
                           inTail x θ π₁' x' θ' (changeCtxVar x∈π₀' π₀'≈π₁' refl) p'


changeCtx : ∀ {π₀} {π₁} {t} {θ} {θ'} → π₀ ⊢ t ∷ θ → π₀ ≈ π₁ → θ ≡ θ' → π₁ ⊢ t ∷ θ'
changeCtx (x∈π₀ ∣ᵥ) π₀≈π₁ refl = changeCtxVar x∈π₀ π₀≈π₁ refl ∣ᵥ
changeCtx {π₀} {π₁} {t = λ' v ∶ θᵥ ⟶ t₀} {θ = .θᵥ ⟼ θ}
          (_∣ₗ {.t₀} {.v} {.θᵥ} {.θ} {.π₀} {x∉π₀} π₀⊢t∷θ) π₀≈π₁ refl =
          _∣ₗ {p = change∉ π₀≈π₁ x∉π₀} (changeCtx π₀⊢t∷θ (ctxEq π₀≈π₁) refl) 
changeCtx (π₀⊢t∷θ ∧ π₀⊢t∷θ₁ ∣ₐ) π₀≈π₁ refl =
        (changeCtx π₀⊢t∷θ π₀≈π₁ refl) ∧ (changeCtx π₀⊢t∷θ₁ π₀≈π₁ refl) ∣ₐ


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
                   t↑ (θ' , changeCtx t∷θ' (ctxEq reflCtx) refl)
inferL t↑ ( ⊙ , () )

inferL2 : ∀ {v} {θᵥ} {θ} {π} {t} → (v , θ) ∈ π → ¬ (∃ (λ θ' → π ⊢ λ' v ∶ θᵥ ⟶ t ∷ θ'))
inferL2 v∈π (⊙ , ())
inferL2 {θ = θ} v∈π (θᵥ ⟼ θ' , _∣ₗ {p = v∉π} π⊢λ't∷θ') = ∉↝ v∉π (θ , v∈π)

--  _∣ᵥ : ∀ {x} {θ} {π} →
--          ( x  ,′ θ ) ∈ π → (π ⊢ ″ x ″ ∷ θ)
--  _∣ₗ : ∀ {t} {x} {θ} {θ'} {π} {p : x ∉ π} → 
--          (( x  , θ ) ▷ π ｢ p ｣  ⊢ t ∷ θ') →
--          (π ⊢ (λ' x ∶ θ ⟶ t) ∷ (θ ⟼ θ') )



uniqueTypeVar : ∀ {π} {x} {θ} {θ'} → (x  , θ) ∈ π → (x , θ') ∈ π → θ ≡ θ'
uniqueTypeVar (inHead x θ π a∉π x≡a θ≡θₐ) 
              (inHead .x θ' .π .a∉π x≡a' θ'≡θₐ) = trans θ≡θₐ (sym θ'≡θₐ)
uniqueTypeVar (inHead x θ π a∉π x≡a θ≡θₐ) 
              (inTail .x θ' .π a θ'' x,θ'∈π .a∉π) = 
                    ⊥-elim (∉↝ a∉π (θ' , subst (λ z → (z , θ') ∈ π) x≡a x,θ'∈π))
uniqueTypeVar (inTail x θ' π a θ'' x,θ'∈π a∉π)
              (inHead .x θ .π .a∉π x≡a θ≡θₐ) = 
                    ⊥-elim (∉↝ a∉π (θ' , subst (λ z → (z , θ') ∈ π) x≡a x,θ'∈π))
uniqueTypeVar (inTail x θ π x' θ'' x,θ∈π x'∉π) 
              (inTail .x θ' .π .x' .θ'' x,θ'∈π .x'∉π) = 
                                                      uniqueTypeVar x,θ∈π x,θ'∈π


-- Si un termino se puede tipar con θ y θ', estos son iguales
uniqueType : ∀ {π} {t} {θ} {θ'} → π ⊢ t ∷ θ → π ⊢ t ∷ θ' → θ ≡ θ'
uniqueType (x,θ∈π ∣ᵥ) (x,θ'∈π ∣ᵥ) = uniqueTypeVar x,θ∈π x,θ'∈π
uniqueType (_∣ₗ {θ = θ} π⊢t∷θ) (_∣ₗ {θ = .θ} π⊢t∷θ') = 
                cong (_⟼_ θ) $ uniqueType π⊢t∷θ $ changeCtx π⊢t∷θ' (ctxEq reflCtx) refl
uniqueType {θ = θ} {θ' = θ'} 
           (_∧_∣ₐ {θ' = .θ} π⊢t∷θ₁⟼θ₂ π⊢t∷θ₁)
           (_∧_∣ₐ π⊢t∷θ₁'⟼θ₂' π⊢t∷θ₁') = 
                           proj₂ $ cong⟼⁻¹ (trans (uniqueType π⊢t∷θ₁⟼θ₂ π⊢t∷θ₁'⟼θ₂') 
                                           (cong (λ θ → θ ⟼ θ') (sym (uniqueType π⊢t∷θ₁ π⊢t∷θ₁'))))


--  _∧_∣ₐ : ∀ {t₁} {t₂} {θ} {θ'} {π} →
 --         (π ⊢ t₁ ∷ (θ ⟼ θ')) →
   --       (π ⊢ t₂ ∷ θ) →
     --     (π ⊢ (t₁ ● t₂) ∷ θ')


inferApp₁₂ : ∀ {π} {t₁} {t₂} → 
             ∃ (λ θ → π ⊢ t₁ ∷ θ) →
             ∃ (λ θ' → π ⊢ t₂ ∷ θ') →
             Dec (∃ (λ θ → π ⊢ (t₁ ● t₂) ∷ θ))
inferApp₁₂ {π} {t₁} {t₂} (⊙ , π⊢t₁∷⊙) π⊢t₂∷θ = no t₁Absurdo
  where
    t₁Absurdo : ¬ ∃ (λ θ → π ⊢ (t₁ ● t₂) ∷ θ)
    t₁Absurdo (θ' , _∧_∣ₐ {θ = θ} π⊢t₁∷θ⟼θ' π⊢t₂∷θ) with ⊙ ≟ₜ θ ⟼ θ'
    ... | yes ()
    ... | no ¬⊙≡θ⟼θ' = ¬⊙≡θ⟼θ' $ uniqueType π⊢t₁∷⊙ π⊢t₁∷θ⟼θ'
inferApp₁₂ {π} {t₁} {t₂} (θ ⟼ θ' , π⊢t₁∷θ⟼θ') (θ'' , π⊢t₂∷θ'') with θ ≟ₜ θ''
... | yes θ≡θ'' = yes (θ' , (π⊢t₁∷θ⟼θ' ∧ changeCtx π⊢t₂∷θ'' reflCtx (sym θ≡θ'') ∣ₐ))
... | no ¬θ≡θ'' = no t₂Absurdo
  where 
    t₂Absurdo : ¬ ∃ (λ θ → π ⊢ (t₁ ● t₂) ∷ θ)
    -- esto va a ser groso
    t₂Absurdo (θ₂ , π⊢t₁∷θ₁⟼θ₂ ∧ π⊢t₂∷θ₁ ∣ₐ) = 
                    -- θ ≡ θ₁
      ¬θ≡θ'' $ trans (proj₁ $ cong⟼⁻¹ $ uniqueType π⊢t₁∷θ⟼θ' π⊢t₁∷θ₁⟼θ₂) 
                    -- θ₁ ≡ θ''
                    (uniqueType π⊢t₂∷θ₁ π⊢t₂∷θ'')

inferApp₁ : ∀ {π} {t₁} {t₂} → ¬ (∃ (λ θ → π ⊢ t₁ ∷ θ)) → ¬ (∃ (λ θ → π ⊢ (t₁ ● t₂)  ∷ θ))
inferApp₁ ¬π⊢t₁∷θ (θ' , _∧_∣ₐ {θ = θ} {θ' = .θ'} π⊢t₁∷θ⟼θ' π⊢t₂∷θ' ) = ¬π⊢t₁∷θ (θ ⟼ θ' , π⊢t₁∷θ⟼θ')

inferApp₂ : ∀ {π} {t₁} {t₂} → ¬ (∃ (λ θ → π ⊢ t₂ ∷ θ)) → ¬ (∃ (λ θ → π ⊢ (t₁ ● t₂)  ∷ θ))
inferApp₂ ¬π⊢t₂∷θ (θ' , _∧_∣ₐ {θ = θ} {θ' = .θ'} π⊢t₁∷θ⟼θ' π⊢t₂∷θ') = ¬π⊢t₂∷θ (θ , π⊢t₂∷θ')

infer : (π : Ctx) → (t : LambdaTerm) → Dec (∃ (λ θ → π ⊢ t ∷ θ))
infer π ″ v ″ = inferVar π v
infer π (λ' v ∶ θ ⟶ t) with v∈π? v π
infer π (λ' v ∶ θ ⟶ t) | yes (θᵥ , v∈π) = no (inferL2 {θᵥ = θ} v∈π)
infer π (λ' v ∶ θ ⟶ t) | no v∉π with infer ((v , θ) ▷ π ｢ ∉↜ v∉π ｣) t
infer π (λ' v ∶ θ ⟶ t) | no v∉π | yes (θ' , t∷θ') = yes (θ ⟼ θ' ,  t∷θ' ∣ₗ)
infer π (λ' v ∶ θ ⟶ t) | no v∉π | no t↑ = no (inferL t↑)
infer π (t₁ ● t₂) with infer π t₁ | infer π t₂
infer π (t₁ ● t₂) | no ¬π⊢t₁∷θ⟼θ' | _ = no (inferApp₁ ¬π⊢t₁∷θ⟼θ')
infer π (t₁ ● t₂) | _ | no ¬π⊢t₂∷θ = no (inferApp₂ ¬π⊢t₂∷θ)
infer π (t₁ ● t₂) | yes π⊢t₁∷θ⟼θ' | yes π⊢t₂∷θ = inferApp₁₂ π⊢t₁∷θ⟼θ' π⊢t₂∷θ

-- infer para términos cerrados
inferType : (t : LambdaTerm) → Dec (∃ (λ θ → ø ⊢ t ∷ θ))
inferType = infer ø 


identity : LambdaTerm
identity = λ' "x" ∶ ⊙  ⟶  ″ "x" ″ 



θ : Type
θ = (⊙ ⟼ ⊙) ⟼ ⊙ ⟼ ⊙

twice : LambdaTerm
twice = λ' "f" ∶ (⊙ ⟼ ⊙) ⟶ λ' "x" ∶ ⊙  ⟶ ″ "f" ″ ● (″ "f" ″ ● ″ "x" ″)



-- Este termino no tipa sin variables de tipo
dtwice : LambdaTerm
dtwice = twice ● twice


-- anda
thrice : LambdaTerm
thrice = λ' "f" ∶ (⊙ ⟼ ⊙) ⟶ λ' "x" ∶ ⊙  ⟶ ″ "f" ″ ● (″ "f" ″ ● (″ "f" ″ ● ″ "x" ″))

{-

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
