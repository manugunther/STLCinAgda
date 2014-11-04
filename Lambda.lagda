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

 
 \usepackage{listings}
 
 
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
 \DeclareUnicodeCharacter{8604}{\ensuremath{\hookleftarrow}}
 \DeclareUnicodeCharacter{8605}{\ensuremath{\hookrightarrow}}
 

 % Add more as you need them (shouldn’t happen often).

 % Using “\newenvironment” to redefine verbatim to
 % be called “code” doesn’t always work properly. 
 % You can more reliably use:

 \usepackage{fancyvrb}

 \usepackage{color}


 \DefineVerbatimEnvironment
   {code}{Verbatim}
   {fontsize=\footnotesize} % Add fancy options here if you like.

 %% COMMANDS
 
 \newcommand{\agType}[1] {\textbf{#1}}
 \newcommand{\comment}[1] {\textbf{\textcolor{red}{#1}}}
   
\title{Agda, un lenguaje con tipos dependientes}
\author{Alejandro Gadea, Emmanuel Gunther}

 \begin{document}

\maketitle



\section{Introducción}


\section{Teoría de tipos}

un resumen de teoría de tipos, como lo que leímos en homotopy type theory.

\section{Agda}

\subsection{Introduciendo Agda}

En lenguajes como Haskell existe una linea bien marcada entre los tipos
(\verb|Int|, \verb|Bool|, \verb|String|, etc) y los valores (\verb|0|,
{\verb|True|, {\verb|"Haskell"|, etc). En cambio en lenguajes con
tipos dependientes, como Agda, esta separación es menos clara. 

Para ejemplificar esto consideremos los clasicos vectores de algún tipo
con tamaño fijo, podemos pensar en la siguiente implementación en
Haskell,

\begin{verbatim}

data Zero where

data Suc n where

data Vec a n where
    Empty :: Vec a Zero
    Const :: a -> Vec a n -> Vec a (Suc n)

\end{verbatim}

donde definimos los tipos \verb|Zero| y \verb|Suc n| sin constructores
con la finalidad de usarlos como \textit{valores} y de esta manera restringir
el tipo \verb|Vec|. A continuación podemos implementar la función que toma
el primer elemento de un vecto, como

\begin{verbatim}

first :: Vec a (Suc n) -> a
first (Const e _) = e
  
\end{verbatim}

la particularidad de esta implementación es que durante el checkeo de tipos
estamos eliminando la posibilidad de escribir \verb|first Empty|. Ahora bien, 
esta implementación parece razonable
y comoda de entender; el vector vacio tiene tamaño \verb|Zero| y si agrego
un elemento \verb|e| a un vector con tipo \verb|Vec a n| (de tamaño \verb|n|) esto
me construye un vector de tamaño \verb|Suc n|. Lamentablemente la utilización
de los tipos como valores no solo no parece una forma prolija de usar los
tipos, si no que utilizar una idea similar pero ahora donde los valores a
\textit{imitar} con tipos son mas complejos podría derivar en implementaciones
dificiles de entender o directamente malas.

Acá es donde la \textit{separación menos clara} entre tipos y valores de Agda
(y los lenguajes con tipado dependiente en general) que mencionabamos antes
nos puede resultar muy util.

A continuación introducimos distintos conceptos (\comment{no se si 
conceptos es la palabra que estoy buscando}) 
de Agda con el fin de implementar el tipo de los vectores de un cierto tipo
y tamaño, como anteriormente realizamos en Haskell.

\subsection{Tipos de datos y pattern matching}

Empezamos entonces introduciendo la forma de declarar tipos de datos
\textit{como los de Haskell}. Podemos definir el tipo \verb|Nat| de los 
números naturales de la siguiente manera

\begin{verbatim}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

\end{verbatim}

Haciendo la comparación con la implementación en Haskell, notar que ahora
\verb|zero| y \verb|suc| son valores de tipo \verb|Nat| y
no tipos en si mismos, además escribiendo \verb|Nat : Set| nos referimos a que \verb|Nat|
tendrá tipo \verb|Set| que bien podriamos
pensarlo como \textit{el tipo de los tipos}. Podemos definir funciones por
pattern matching como hacemos en haskell, pero con la importante salvedad de que
estamos obligados a cubrir todos los casos debido a que Agda no admite programas
que no terminen, de ser el caso el chequeador de tipos nos dará un error.

Como ejemplo de función, definimos la suma de dos naturales. Aprovechamos para mencionar que
Agda es muy flexible con los nombres de funcion (constructores, tipos, etc) cualquier
secuencia sin espacios de símbolos puede ser considerado un nombre valido, además
para declarar operadores infijos se hace uso del \verb|_| de manera tal que al
usar el operador se puede utilizar por ejemplo como \verb|n + m| o \verb|_+_ n m|.
Donde es importante la separación por espacios, escribir \verb|n+m| no es igual a
\verb|n + m| por lo dicho anteriormente; cualquier secuencia sin espacios de símbolos
es un nombre de variable valido.

\begin{verbatim}

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

\end{verbatim}

Teniendo en cuenta la exigencia de terminación que impone Agda, notar que en
el segundo caso de pattern matching es valido ya que el segundo argumento se
vuelve mas chico.

\subsection{Funciones dependientes y argumentos implicitos}

Hasta acá repasamos como escribir tipos de dato y funciones de Haskell, en Agda.
Introducimos ahora las funciones dependientes, como funciones en las que en su signatura
el tipo resultante puede depender de los valores de los argumento. En Agda podemos
escribir \verb|(a : A) → B| como el tipo de una función que toma un \verb|a : A| y
retorna algo de tipo \verb|B|, en el cual probablemente aparezca \verb|a|. Podemos
definir la función identidad por ejemplo como,

\begin{verbatim}

id : (A : Set) → A → A
id _ = λ x → x

\end{verbatim}

Esta función toma un tipo \verb|A| y retorna la función identidad para ese tipo. Algo que podría
ocurrir es que el tipo resultante dependa de muchos argumentos ocasionando que nuestra función
se sature de estos, cuando probablemente la gran mayoría no seán los argumentos
\textit{realmente esperados} de la función, para evitar esto y poder implementar funciones que toman
exactamente los parametros que \textit{necesitan}, es que en Agda se puede definir un tipo de argumento
que llamaremos implicito. Por ejemplo,
para el caso de la función identidad, deberíamos escribir \verb|id A a| en lugar de lo
posiblemente deseado \verb|id a|. Podemos escribir un argumento como implicitos simplemente encerrandolo entre
llaves y de esta manera dejar que el checkeador de tipos de Agda intente inferir su valor. 
Volviendo al ejemplo de la función identidad podemos escribir al argumento del tipo
de la función identidad como implicito de la siguiente manera

\begin{verbatim}

id : {A : Set} → A → A
id = λ x → x

\end{verbatim}

La declaración de los argumentos como implicitos nos exime de tener que pasarlos al
llamar a la función, pero existe la posibilidad de pasarlos si es que hiciera
falta o usarlos como un argumento normal en la declaración. La manera de usar a estos
argumentos implicitos es mediante llaves como cualquier otro argumento o además de las
llaves utilizando el nombre de la variable escrita en el tipo de la función

\begin{verbatim}

id'o'+1 : {b : Bool} → Nat → Nat
id'o'+1 {true} = λ x → x
id'o'+1 {b = false} = λ x → suc zero + x

zero' : Nat
zero' = id {Nat} zero

\end{verbatim}

\comment{El nombre de la función no parece muy bonito y el ejemplo tampoco}

\subsection{Familias de tipos de datos}

Veamos ahora como podemos definir familia de tipos indexadas implementando el
tipo de los vectores de un cierto tipo y tamaño

\begin{verbatim}

data Vec (A : Set) : Nat → Set where
  empty : Vec A zero
  const : {n : Nat} → A → Vec A n → Vec A (suc n)

\end{verbatim}

diremos que \verb|Vec| está paremetrizado por el tipo \verb|A|
e indexado por el tipo \verb|Nat|. Dado un tipo \verb|A|, \verb|Vec A| tendrá
tipo \verb|Nat → Set|, es decir será una familia de tipos indexada por \verb|Nat|, por
lo tanto tomando un \verb|n : Nat|, \verb|Vec A n| es un tipo; el de los vectores de tipo
\verb|A| y tamaño \verb|n|. Luego, \verb|empty| será un vector de tamaño cero con
tipo \verb|Vec A zero| y dado un elemento \verb|e : A| y un vector \verb|v : Vec A n|,
\verb|const e v| nos construye un vector de tamaño \verb|suc n| con tipo \verb|Vec A (suc n)|.

Esta implementación es bastante similar a la hecha anteriormente
en Haskell, pero con la diferencia importante que \verb|n| es un valor y no un tipo.

Ahora podemos implementar la función que toma el primer elemento

\begin{verbatim}

first : {A : Set} {n : Nat} → Vec A (suc n) → A
first (const x _) = x

\end{verbatim}

es importante notar que la condición de exhaustividad del checkeador de tipos
se cumple ya que no existe otra forma de construir algo de tipo \verb|Vec A (suc n)|
que no sea con el constructor \verb|const|.

\subsection{Dotted Patterns y Pattern Matching con \verb|with}

\subsection{Valores como pruebas}

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
podrá ser el tipo básico $\odot$ o dados dos tipos $\theta_1$ y $\theta_2$, el tipo $\theta_1 \mapsto \theta_2$.

Esto nos obliga a que en la abstracción lambda debemos anotar el tipo de la variable, caso contrario por ejemplo
para el término $id = \lambda\,x\,.\,x$ no podríamos distinguir si tiene tipo ($\odot \mapsto \odot$) ó 
$(\odot \mapsto \odot) \mapsto (\odot \mapsto \odot)$, etc. Anotando el tipo de la variable
los términos ($\lambda\,x_{\odot}\,.\,x$) y ($\lambda\,x_{\odot \mapsto \odot}\,.\,x$) son distintos
y evitan esta ambigüedad.


\subsection{Librerías auxiliares}

Para la implementación utilizaremos varias librerías de Agda:

\begin{code}
module Lambda where

open import Data.String
-- Para la equivalencia de tipos:
open import Relation.Binary.PropositionalEquality

-- Para el tipo Bottom y la negación de un tipo:
open import Relation.Nullary
-- Para las 2-uplas:
open import Data.Product
open import Data.Empty
open import Function


\end{code}

\agType{String}, para representar las variables de los términos. \agType{PropositionalEquality} tiene definido el tipo de la igualdad
proposicional entre dos tipos, tal como lo explicamos en la sección 2. \agType{Nullary} para tener el tipo vacío $\bot$ y
el tipo \agType{Dec}.
\agType{Product} lo necesitamos para representar los pares (variable, tipo) en los contextos. \agType{Empty} tiene definido
el eliminador de $\bot$, es decir, la función que dado $\bot$ retorna cualquier cosa. Por último
\agType{Function} tiene definido el símbolo de aplicación $\$$, el cual es útil para evitar paréntesis excesivos.

\subsection{Tipos del Cálculo Lambda}


Como dijimos previamente, un tipo del cálculo lambda podrá ser el tipo básico $\odot$ ó un tipo $\theta_1 \mapsto \theta_2$:

\begin{code}
data Type : Set where
  ⊙     : Type
  _⟼_  : Type → Type → Type

infixr 100 _⟼_
\end{code}

Dada esta definición de tipos podemos definir la propiedad que asegura que dados
dos tipos $\theta$ y $\theta'$ la igualdad entre ellos es decidible, es decir
ó bien $\theta \equiv \theta'$ ó bien $\theta \not \equiv \theta'$. 

Para la implementación procedemos de la misma manera en que definimos la igualdad
de los números naturales en la sección 3, mediante el tipo \agType{Dec}:

\begin{code}

cong⟼⁻¹ : ∀ {θ₁} {θ₂} {θ₁'} {θ₂'} → θ₁ ⟼ θ₂ ≡ θ₁' ⟼ θ₂' → θ₁ ≡ θ₁' × θ₂ ≡ θ₂'
cong⟼⁻¹ refl = refl , refl

_≟ₜ_ : (θ₁ : Type) → (θ₂ : Type) → Dec (θ₁ ≡ θ₂)
⊙ ≟ₜ ⊙                  = yes refl
⊙ ≟ₜ θ ⟼ θ'            = no (λ ())

θ₁ ⟼ θ₂ ≟ₜ ⊙           = no (λ ())
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' with θ₁ ≟ₜ θ₁' | θ₂ ≟ₜ θ₂'
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' | yes p | yes p' = yes (cong₂ _⟼_ p p')
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' | no ¬p | _      = 
      no (λ θ₁⟼θ₂≡θ₁'⟼θ₂' → ¬p (proj₁ (cong⟼⁻¹ θ₁⟼θ₂≡θ₁'⟼θ₂')))
θ₁ ⟼ θ₂ ≟ₜ θ₁' ⟼ θ₂' | _ | no ¬p      = 
      no (λ θ₁⟼θ₂≡θ₁'⟼θ₂' → ¬p (proj₂ (cong⟼⁻¹ θ₁⟼θ₂≡θ₁'⟼θ₂')))

\end{code}

Definimos la igualdad entre dos tipos mediante recursión. Observemos que en el caso
que tengamos dos tipos $θ₁ ⟼ θ₂$ y $θ₁' ⟼ θ₂'$, estos serán iguales si
$θ₁ \equiv θ₁'$ y $θ₂ \equiv θ₂'$. En el caso que alguna de estas dos igualdades no se cumpla,
tendremos que construir una función que dado un elemento de $θ₁ ⟼ θ₂ \equiv θ₁' ⟼ θ₂'$
devuelva $\bot$. 

Si no se cumple que $θ₁ \equiv θ₁'$ entonces tenemos una función que devuelve
$\bot$ a partir de $θ₁ \equiv θ₁'$, que en la implementación la llamamos $¬p$.
Entonces si pudiéramos obtener $θ₁ \equiv θ₁'$ a partir de $θ₁ ⟼ θ₂ \equiv θ₁' ⟼ θ₂'$
luego aplicamos $¬p$ y tenemos el resultado $\bot$ que queríamos.

Pero observemos que como el constructor $⟼$ es una función inyectiva, si se da que 
$θ₁ ⟼ θ₂ ≡ θ₁' ⟼ θ₂'$ entonces $θ₁ ≡ θ₁'$ y $θ₂ ≡ θ₂'$. La función $cong⟼⁻¹$ expresa
exactamente esto y nos permite completar la definición de la igualdad de tipos.

\subsection{Términos del Cálculo Lambda}

Ahora procedemos a definir los términos del cálculo lambda.

Un término del cálculo Lambda podrá ser un identificador (el cual consta de una variable), 
una abstracción (que consta de una variable, el tipo con el que está anotada dicha variable y un término) 
o una aplicación (dos términos):

\begin{code}
Var : Set
Var = String

data LambdaTerm : Set where
  ″_″        : Var → LambdaTerm
  λ'_∶_⟶_  : Var → Type → LambdaTerm → LambdaTerm
  _●_        : LambdaTerm → LambdaTerm → LambdaTerm
 
infixl 100 _●_

\end{code}


\subsection{Contextos de tipado}

Para poder dar un tipo a un término tenemos que asignarle tipos a las variables.
Necesitamos entonces definir un contexto de asignación de variables a tipos, en el cual no queremos que
una misma variable ocurra dos veces.

Definimos el tipo \agType{Ctx} junto con un tipo que dada una variable $x$ y un contexto $\pi$, expresa que 
$x$ no ocurre en $\pi$:

\begin{code}
mutual
  data Ctx : Set where
    ø      : Ctx
    _▷_｢_｣ : (t : Var × Type) → (π : Ctx) → (p : (proj₁ t) ∉ π) → Ctx

  data _∉_ : Var → Ctx → Set where
    ∉ø  : ∀ {x} → x ∉ ø
    ∉¬ø : ∀ {x'} {θ} {x} {π} {p} → 
            x ∉ π →  ¬ (x ≡ x') →
            x ∉ ((x' , θ) ▷ π ｢ p ｣)
\end{code}
 
Un contexto bien formado entonces será o bien el vacío, o un contexto 
$\pi$ al que se le agrega un par $(x,\theta)$ con una prueba de que $x$ no ocurre en $\pi$.
         
Si una variable $x$ no ocurre en un contexto $\pi$ es porque $\pi$ es vacío
o porque $x$ no ocurre en la cola y es distinta a la variable de la cabeza de $\pi$. Esto
expresan los constructores $∉ø$ y $∉¬ø$ respectivamente del tipo $∉$.
         
Con esta definición podemos definir una relación de equivalencia entre dos
contextos:

\begin{code}
data _≈_ : Ctx → Ctx → Set where
  emptyCtxEq : ø ≈ ø
  ctxEq      : ∀ {v} {θ} {π} {π'} → {p : v ∉ π} {p' : v ∉ π'} → 
               π ≈ π' → (v , θ) ▷ π ｢ p ｣ ≈ (v , θ) ▷ π' ｢ p' ｣

reflCtx : ∀ {π} → π ≈ π
reflCtx {ø}           = emptyCtxEq
reflCtx {t ▷ π ｢ p ｣} = ctxEq (reflCtx {π})

transCtx : ∀ {π₀} {π₁} {π₂} → π₀ ≈ π₁ → π₁ ≈ π₂ → π₀ ≈ π₂
transCtx emptyCtxEq emptyCtxEq        = emptyCtxEq
transCtx (ctxEq π₀≈π₁) (ctxEq π₁≈π₂) = ctxEq (transCtx π₀≈π₁ π₁≈π₂)

symCtx : ∀ {π₀} {π₁} → π₀ ≈ π₁ → π₁ ≈ π₀
symCtx emptyCtxEq    = emptyCtxEq
symCtx (ctxEq π₀≈π₁) = ctxEq (symCtx π₀≈π₁)
\end{code}

Esto nos permite considerar iguales a dos contextos que tengan los mismos
pares (variable,tipo) pero que las pruebas que aseguran que cada variable no ocurre
en el resto no sean exactamente las mismas (en la definción de $ctxEq$, $p$ puede
ser distinto de $p'$ pero ambos expresan que la variable no pertenece al resto del contexto).
\medskip

Para poder definir juicios de tipado necesitamos una noción más. Si pensamos en la regla
para tipar una variable tenemos que una variable $x$ tiene tipo $\theta$ si el par $(x,\theta)$
pertenece al contexto de tipado. Por lo tanto necesitamos definir cuándo un par pertenece
a un contexto:

\begin{code}
data _∈_ : Var × Type → Ctx → Set where
  inHead : ∀ {y} {θ'} {x} {θ} {π} {y∉π} → x ≡ y → θ ≡ θ' → 
              ( x  , θ ) ∈ (( y  , θ' ) ▷ π ｢ y∉π ｣)
  inTail : ∀ {x} {θ} {π} {y} {θ'} {y∉π} → (x  , θ ) ∈ π → 
                 ( x  , θ ) ∈ (( y  , θ' ) ▷ π ｢ y∉π ｣)
\end{code}

Si el par $(x,\theta)$ pertenece a $\pi$ es porque o bien está en la cabeza o bien está en la cola
y esto expresan ambos constructores.
\medskip

Observemos que este tipo de dato que acabamos de definir debería ser opuesto al que expresa que una variable
no pertenece a un contexto, que definimos previamente.
Es decir,  $x ∉ \pi$ si y solo si no existe $\theta$ tal que $(v , θ) ∈ π$. 

Dados una variable $v$ y un contexto $\pi$ podemos definir entonces un isomorfismo entre los tipos
$v ∉ \pi$ y $¬ (∃ (λ θ → (v , θ) ∈ π))$.

En uno de los lados del isomorfismo tenemos que obtener un elemento
de $¬ (∃ (λ θ → (v , θ) ∈ π))$ a partir de uno de $v ∉ π$. Esto es lo mismo
que obtener $\bot$ a partir de $v ∉ π$ y de un par $(\theta,p)$ (donde $\theta$ es algún tipo
y $p$ algún elemento de $(v,\theta)\in\pi$).

\begin{code}
∉↝ : ∀ {v} {π} → v ∉ π → ¬ (∃ (λ θ → (v , θ) ∈ π))
∉↝ {π = ø} ∉ø (_ , ())
∉↝ {v} {(v' , θ') ▷ π' ｢ v'∉π' ｣} 
   (∉¬ø v∉π' v≠v') (θ , inHead v=v' _) = v≠v' v=v'
∉↝ {v} {(v' , θ') ▷ π' ｢ v'∉π' ｣} 
   (∉¬ø v∉π' v≠v') (θ , inTail v∈π')   = (∉↝ v∉π') (θ , v∈π')
\end{code}
   
En la definición realizamos pattern matching sobre $v ∉ π$ y sobre
$∃ (λ θ → (v , θ) ∈ π)$.

El primero de los casos es cuando tenemos que $v$ no ocurre en $\pi$
porque éste es vacío, es decir, tenemos el constructor $∉ø$. Esto
nos deja un pattern absurdo para el segundo parámetro de la función ya
que no podemos construir un elemento de $(v , θ) ∈ ø$.

El siguiente caso a contemplar es cuando $v$ no está en el contexto $\pi = ( v'  , θ' ) ▷ π' ｢ v'∉π' ｣$,
representado por el constructor $∉¬ø$. Observemos que para definir este caso de pattern matching
tendremos un elemento de $\neg (v \equiv v')$ y uno de $v ∉ \pi'$.

Dentro de este caso tenemos dos opciones: $(v , θ) ∈ π$ para algún $\theta$ porque el par
se encuentra en la cabeza de $\pi$, o porque se encuentra en la cola, y esto está expresado en los dos
casos de pattern matching. En el primero de ellos observemos que tenemos un elemento de
$v \equiv v'$, por lo cual podremos obtener $\bot$ ya que teníamos también que $\neg (v \equiv v')$.

En el último caso el constructor $inTail$ contiene un elemento de $v \in \pi'$ pero también teníamos
uno de $v ∉ \pi'$ por lo que podremos obtener $\bot$ utilizando una llamada recursiva.
\medskip

En el otro lado del isomorfismo tenemos que obtener un elemento
de $v ∉ π$ a partir de $¬ (∃ (λ θ → (v , θ) ∈ π))$. Es decir, dado que tenemos
una función que obtiene $\bot$ a partir de un par $(\theta,p)$ (donde $p$ es un elemento
de $(v , θ) ∈ π$), tendremos que obtener uno de $v ∉ π$:

\begin{code}
   
∉↜ : ∀ {v} {π} → ¬ (∃ (λ θ → (v , θ) ∈ π)) → v ∉ π
∉↜ {v} {ø} t↑           = ∉ø
∉↜ {v} {(v' , θ') ▷ π' ｢ p ｣} t↑ = ∉¬ø (∉↜ (f t↑)) (g t↑)
  where
    f : ¬ (∃ (λ θ → (v , θ) ∈ ((v' , θ') ▷ π' ｢ p ｣))) →
        ¬ (∃ (λ θ → (v , θ) ∈ π'))
    f t↑ (θ , v∈π) = t↑ (θ , (inTail v∈π))
    g : ¬ (∃ (λ θ → (v , θ) ∈ ((v' , θ') ▷ π' ｢ p ｣))) →
        ¬ (v ≡ v')
    g t↑ v=v' = t↑ (θ' , inHead v=v' refl)
\end{code}

Aquí podemos hacer pattern matching en el parámetro implícito $\pi$. Si es vacío
entonces no tenemos otra opción para el valor de retorno que $∉ø$.

Si $\pi = (v' , θ') ▷ π' ｢ p ｣$ entonces el valor de retorno los construimos con 
$∉¬ø$. Para ello necesitamos dos elementos: uno de tipo $v ∉ π'$ y otro de $¬ (v ≡ v')$.
Observemos que con lo único que contamos es con una función $t↑$ que dado un elemento de
$(∃ (λ θ → (v , θ) ∈ π))$ retorna $\bot$. 

Si tenemos que no existe $\theta$ tal que $(v , θ) ∈ (v' , θ') ▷ π' ｢ p ｣$ entonces 
tampoco existe $\theta$ tal que $(v , θ) ∈ π'$. Podemos construir una función $f$ que exprese
esto: Dado un elemento de $¬(∃ (λ θ → (v , θ) ∈ π))$ obtiene uno de $¬(∃ (λ θ → (v , θ) ∈ π'))$ 
Luego aplicando $∉↜$ a $(f \,t↑)$ obtenemos el elemento de $v ∉ π'$ que necesitamos.

Por otro lado, como no existe $\theta$ tal que $(v , θ) ∈ (v' , θ') ▷ π' ｢ p ｣$, entonces
necesariamente $v$ debe ser distinto a $v'$ (pues de lo contrario podríamos tomar $θ = θ'$).
Construimos entonces una función $g$ que obtiene un elemento de $¬ (v ≡ v')$ y podemos completar
la definición.
\medskip

\subsubsection{Propiedades de los contextos de tipado}

Con las definiciones sobre contextos de tipado podemos definir algunas propiedades interesantes:

\begin{itemize}
  \item Si dos contextos $π₀$ y $π₁$ son equivalentes (es decir $π₀ ≈ π₁$) y
        la varible $v$ no pertenece a $π₀$, entonces $v$ no pertenece a $π₁$:
    
\begin{code}
change∉ : ∀ {v} {π₀} {π₁} → π₀ ≈ π₁ → v ∉ π₀ → v ∉ π₁
change∉ emptyCtxEq notInEmpty = notInEmpty
change∉ {v} {t ▷ π₀ ｢ p ｣} {.t ▷ π₁ ｢ p' ｣} 
            (ctxEq e) (∉¬ø p₀ x) = 
              ∉¬ø (change∉ e p₀) x
\end{code}

  \item Si dos contextos $π₀$ y $π₁$ son equivalentes, los tipos $θ₀$ y $θ₁$ son iguales
        y el par $(x , θ₀)$ pertenece a $π₀$, entonces el par $(x , θ₁)$ pertenece a $π₁$:
  
\begin{code}
changeCtxVar : ∀ {x} {π₀} {π₁} {θ₀} {θ₁} → 
               π₀ ≈ π₁ → θ₀ ≡ θ₁ → (x , θ₀) ∈ π₀ → (x , θ₁) ∈ π₁
changeCtxVar emptyCtxEq refl x∈π₀ = x∈π₀
changeCtxVar {x} {(x' , θ') ▷ π₀' ｢ p ｣} {(.x' , .θ') ▷ π₁' ｢ p' ｣}
             (ctxEq π₀'≈π₁') refl (inHead x≡x' θ₀≡θ') = inHead x≡x' θ₀≡θ'
changeCtxVar {x} {(x' , θ') ▷ π₀' ｢ p ｣} {(.x' , .θ') ▷ π₁' ｢ p' ｣} 
             (ctxEq π₀'≈π₁') refl (inTail x∈π₀') = 
                           inTail (changeCtxVar π₀'≈π₁' refl x∈π₀' )
\end{code}

  \item Si los pares $(x , θ)$ y $(x , θ')$ pertenecen al contexto $π$, entonces
        $θ ≡ θ'$:

\begin{code}
uniqueTypeVar : ∀ {π} {x} {θ} {θ'} → (x  , θ) ∈ π → (x , θ') ∈ π → θ ≡ θ'
uniqueTypeVar (inHead x≡a θ≡θₐ) 
              (inHead x≡a' θ'≡θₐ) = trans θ≡θₐ (sym θ'≡θₐ)
uniqueTypeVar {(a  , θₐ) ▷ π' ｢ a∉π' ｣} {x} {θ} {θ'}
              (inHead x≡a θ≡θₐ) 
              (inTail x,θ'∈π') = 
                    ⊥-elim (∉↝ a∉π' (θ' , subst (λ z → (z , θ') ∈ π') x≡a x,θ'∈π'))
uniqueTypeVar {(a  , θₐ) ▷ π' ｢ a∉π' ｣} {x} {θ} {θ'}
              (inTail x,θ∈π')
              (inHead x≡a θ'≡θₐ) = 
                    ⊥-elim (∉↝ a∉π' (θ , subst (λ z → (z , θ) ∈ π') x≡a x,θ∈π'))
uniqueTypeVar {(a  , θₐ) ▷ π' ｢ a∉π' ｣} {x} {θ} {θ'}
              (inTail x,θ∈π') 
              (inTail x,θ'∈π') = uniqueTypeVar x,θ∈π' x,θ'∈π'
\end{code}

\end{itemize}


\subsection{Juicios de tipado}

Definimos ahora los juicios de tipado.
Dados un contexto $\pi$, un término $t$ y un tipo $\theta$, el siguiente 
tipo de dato expresa que $t$ tiene tipo $\theta$ bajo $\pi$:

\begin{code}
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
\end{code}

Los tres constructores se corresponden con las reglas de tipado del cálculo lambda:

\begin{itemize}
  \item Si el término $t$ es una variable $v$, entonces $t$ tendrá tipo $\theta$ si el par
        $(x,\theta)$ pertenece a $\pi$.
  \item Si el término $t$ es una abstracción $λ' x ∶ θ ⟶ t'$, entonces $t$ tendrá tipo $θ ⟼ θ'$ bajo $\pi$ 
        si tenemos un juicio de tipado para $t'$ con tipo $θ'$ y el contexto $\pi$ donde agregamos
        el par $( x  , θ )$.
  \item Si el término $t$ es una aplicación $t₁ ● t₂$, entonces $t$ tendrá tipo $θ'$ bajo $\pi$ si 
        tenemos un juicio de tipado para $t₁$ con tipo $θ ⟼ θ'$ y contexto $\pi$, y un juicio
        para $t₂$ con tipo $θ$ y contexto $\pi$.
\end{itemize}


\begin{code}
changeCtx : ∀ {π₀} {π₁} {t} {θ} {θ'} → π₀ ≈ π₁ → θ ≡ θ' → π₀ ⊢ t ∷ θ → π₁ ⊢ t ∷ θ'
changeCtx π₀≈π₁ refl (x∈π₀ ∣ᵥ) = changeCtxVar π₀≈π₁ refl x∈π₀ ∣ᵥ
changeCtx {π₀} {π₁} {t = λ' v ∶ θᵥ ⟶ t₀} {θ = .θᵥ ⟼ θ}
          π₀≈π₁ refl (_∣ₗ {.t₀} {.v} {.θᵥ} {.θ} {.π₀} {x∉π₀} π₀⊢t∷θ) =
          _∣ₗ {p = change∉ π₀≈π₁ x∉π₀} (changeCtx (ctxEq π₀≈π₁) refl π₀⊢t∷θ) 
changeCtx π₀≈π₁ refl (π₀⊢t∷θ ∧ π₀⊢t∷θ₁ ∣ₐ) =
        (changeCtx π₀≈π₁ refl π₀⊢t∷θ) ∧ (changeCtx π₀≈π₁ refl π₀⊢t∷θ₁ ) ∣ₐ


-- Si un termino se puede tipar con θ y θ', estos son iguales
uniqueType : ∀ {π} {t} {θ} {θ'} → π ⊢ t ∷ θ → π ⊢ t ∷ θ' → θ ≡ θ'
uniqueType (x,θ∈π ∣ᵥ) (x,θ'∈π ∣ᵥ) = uniqueTypeVar x,θ∈π x,θ'∈π
uniqueType (_∣ₗ {θ = θ} π⊢t∷θ) (_∣ₗ {θ = .θ} π⊢t∷θ') = 
                cong (_⟼_ θ) $ uniqueType π⊢t∷θ $ changeCtx (ctxEq reflCtx) refl π⊢t∷θ'
uniqueType {θ = θ} {θ' = θ'} 
           (_∧_∣ₐ {θ' = .θ} π⊢t∷θ₁⟼θ₂ π⊢t∷θ₁)
           (_∧_∣ₐ π⊢t∷θ₁'⟼θ₂' π⊢t∷θ₁') = 
                           proj₂ $ cong⟼⁻¹ (trans (uniqueType π⊢t∷θ₁⟼θ₂ π⊢t∷θ₁'⟼θ₂') 
                                           (cong (λ θ → θ ⟼ θ') (sym (uniqueType π⊢t∷θ₁ π⊢t∷θ₁'))))
\end{code}

\subsection{Inferencia de tipos}

\begin{code}
-- En esta función probamos que si no existe θ' tal que (v,θ') ∈ π y
-- v≠w, entonces no existe θ' tal que (v,θ') ∈ ((w , θ) ▷ π)
aux'' : (π : Ctx) → (v : Var) → (w : Var) → (θ : Type) → ¬ (v ≡ w) →
        (w∉π : w ∉ π) →  (p : ¬ (∃ (λ θ → (v , θ) ∈ π))) → 
        ¬ (∃ (λ θ' → (v , θ') ∈ ((w , θ) ▷ π ｢ w∉π ｣)))
-- v≠w es una función que toma un elemento de (v ≡ w) y retorna ⊥
aux'' π v w θ v≠w w∉π p (θ' , inHead v=w q) = v≠w v=w
aux'' π v w θ v≠w w∉π p (θ' , inTail v∈π) = p (θ' , v∈π)


-- Dado un contexto π y una variable v decidimos si existe un tipo θ
-- tal que (v , θ) ∈ π.
v∈π? : (v : Var) → (π : Ctx) → Dec (∃ (λ θ → (v , θ) ∈ π))
v∈π? v ø = no (λ {(θ , ())})
v∈π?  v ( (w , θ) ▷ π ｢ w∉π ｣) with v ≟ w | v∈π? v π
... | yes p | _ = yes (θ , inHead p refl)
... | no _  | yes (θ' , v,θ'∈π) = yes (θ' , inTail v,θ'∈π)
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
                   t↑ (θ' , changeCtx (ctxEq reflCtx) refl t∷θ') 
inferL t↑ ( ⊙ , () )

inferL2 : ∀ {v} {θᵥ} {θ} {π} {t} → (v , θ) ∈ π → ¬ (∃ (λ θ' → π ⊢ λ' v ∶ θᵥ ⟶ t ∷ θ'))
inferL2 v∈π (⊙ , ())
inferL2 {θ = θ} v∈π (θᵥ ⟼ θ' , _∣ₗ {p = v∉π} π⊢λ't∷θ') = ∉↝ v∉π (θ , v∈π)

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
... | yes θ≡θ'' = yes (θ' , (π⊢t₁∷θ⟼θ' ∧ changeCtx reflCtx (sym θ≡θ'') π⊢t₂∷θ'' ∣ₐ))
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
