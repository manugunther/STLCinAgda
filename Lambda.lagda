\documentclass{article}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}

 \usepackage[greek,english]{babel}
 \usepackage{amsmath}
 \usepackage{ dsfont }

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
 \newcommand{\tjud}[2]
  {\ensuremath{#1\,:\,#2}}
 \newcommand{\depFun}[3] {
  {\ensuremath{\Pi_{\tjud{#1}{#2}}\,#3\,#1}}
 }

 
   
\title{Agda, un lenguaje con tipos dependientes}
\author{Alejandro Gadea, Emmanuel Gunther}

 \begin{document}

\maketitle

%% Referencias: Type Theory and Functional Programming Simon Thompson
%%              Homotopy Type Theory (Cap 1)

\section{Introducción}

%% Referencia: Type Theory and Functional Programming Simon Thompson

En cualquier sistema de computación se pretende obtener programas que satisfagan problemas
de manera \textbf{correcta}. Si bien esto parece obviamente deseable, es algo difícil de lograr,
y que en la práctica pocas veces sucede.

Un programa se escribe a partir de una especificación y se asume que la ejecución del mismo la satisfará. 
Pero esta asunción no es justificada: en la mayoría de los casos, el programa no satisface la especificación.

¿Cómo podemos entonces lograr tener software correcto? El testing podrá evidenciar errores pero nunca probar
su ausencia. Sólo una prueba formal de correctitud puede garantizar que un programa satisface una especificación.
Un enfoque para realizar este proceso podría ser desarrollar el programa, y luego dar una prueba de que satisface
una especificación, para lo cual deberíamos poder unir la implementación del programa con un sistema
formal de pruebas, o modelar el programa de tal manera de poder verificar formalmente su corrección. 

Pero otro enfoque más adecuado sería el de desarrollar el programa de manera tal que deba satisfacer una especificación
por la forma en que es construido.

Los sistemas de tipos en los lenguajes de programación permiten agregar restricciones para la construcción de
programas, de manera de poder expresar en los tipos propiedades que deben satisfacerse. Un lenguaje no tipado
permitiría construir programas con algunos errores, que si bien uno podría probar luego que éstos no ocurren,
no se puede asegurar su ausencia de antemano. En un lenguaje tipado, tal programa no podría construirse. 

Como ejemplo consideremos la función que toma el primer elemento de una lista. En un lenguaje sin tipos
fuertes como python podríamos escribirla de la siguiente forma:

\begin{verbatim}
  def head (l):
    return l[0]
\end{verbatim}

Dado que no tenemos un sistema de tipos fuerte, podríamos tener un programa que tenga la siguiente línea:

\begin{verbatim}
  head (True)
\end{verbatim}

Lo que llevaría a tener un error en tiempo de ejecución.

Consideremos ahora un lenguaje con tipos fuertes como Haskell:

\begin{verbatim}
  head :: [a] -> a
  head (x:xs) = x
\end{verbatim}

Con este lenguaje no podríamos escribir \verb|head True| como antes, pero sí podemos
escribir \verb|head []|, lo que nuevamente nos llevaría a un error en tiempo de ejecución.

Lo que necesitaríamos es restringir la función \verb|head| para que el tipo del parámetro
no sea cualquier lista, sino una lista que tenga al menos un elemento.

En un lenguaje con \textbf{tipos dependientes}, como Agda, podríamos definir la función
head que tome como parámetros la lista y además una ``prueba" de que la misma tiene longitud
mayor que cero:

\begin{verbatim}
  head : {a : Set}  → (xs : List a) → 0 < length xs → a
  head [] ()
  head (x ∷ xs) _ = x
\end{verbatim}

Con esta definición, para poder aplicar la función \verb|head| sobre una lista \verb|xs| tenemos que poder construir
un elemento de \verb|0 < length xs|, lo que representa la prueba de que la lista no es vacía. Por lo tanto
nunca podríamos tener en un programa una llamada a \verb|head []|.

Un lenguaje con estas características permite garantizar la correctitud mediante un sistema de tipos
que permite escribir proposiciones lógicas como tipos mismos del lenguaje.

\medskip

En este trabajo estudiaremos un lenguaje con tipos dependientes: Agda. Para ello, primero haremos
un breve repaso de las bases de la teoría de tipos de Martin-Löf. Luego revisaremos las características
y generalidades del lenguaje Agda. Por último realizaremos una implementación en Agda de la inferencia de tipos
para el cálculo lambda simplemente tipado asegurando su corrección.


\section{Teoría de tipos}

En esta sección daremos un vistazo a las bases de la teoría de tipos de Martin Löf, haciendo
un resumen del primer capítulo del libro (cita a homotopy types).

\subsection{Teoría de tipos vs. Teoría de conjuntos}

La teoría de tipos es una teoría fundacional de la matemática, alternativa a la de conjuntos de Zermelo-Fraenkel.
Difiere de esta última en algunos aspectos importantes:

\begin{itemize}
  \item En la teoría de conjuntos podemos identificar dos "capas": El sistema deductivo de la lógica de primer orden
        y, dentro de este sistema, los axiomas de una teoría particular como la de Zermelo-Fraenkel.
        
        En la teoría de tipos no tenemos esta distinción, la teoría \textbf{es} su propio sistema deductivo. En 
        lugar de tener dos nociones como "conjuntos" y "proposiciones", tiene solo una: los \textbf{tipos}.
        
  \item En el sistema deductivo de la teoría de conjuntos tenemos un solo tipo de juicios: Una proposición tiene una prueba. Las
        reglas para construir estos juicios son del estilo "A partir de $A$ y $B$ se infiere $A \wedge B$". Un juicio (como
        "$A$ tiene una prueba" existe a un nivel distinto al de una proposición en sí misma ($A$).
        
        En teoría de tipos el análogo a "$A$ tiene una prueba" es "$a\,:\,A$" ($a$ tiene tipo $A$). Si consideramos que el tipo
        $A$ representa una proposición, luego $a$ es la prueba que hace a la proposición $A$ cierta. De esta forma
        la teoría de tipos es un sistema \textbf{constructivista}, ya que para probar la validez de una propiedad se debe
        encontrar el testigo que la hace cierta.
        
  \item Si bien un juicio de tipado "$a\,:\,A$" puede interpretarse como que $a$ es la prueba de cierta proposición $A$, también
        puede ser considerado como el análogo a "$a \in A$" de la teoría de conjuntos, es decir, considerar al tipo $A$ como un conjunto
        de elementos. Sin embargo hay una diferencia escencial en el hecho de que "$a\,:\,A$" es un juicio, mientras que "$a \in A$"
        es una proposición. En particular, en la teoría de tipos no podemos construir proposiciones del tipo "si $a\,:\,A$ luego ..."
        La existencia de $a$ sólo puede considerarse dentro de un tipo, y no por sí solo, ya que cada elemento por su propia naturaleza
        debe tener un tipo. En cambio en la teoría de conjuntos esto no es así.
        
  \item Una última diferencia a considerar es el concepto de \text{igualdad}. La noción de igualdad usual en matemática es considerarla
        una proposición. Dado que en la teoría de tipos las proposiciones son tipos, luego la igualdad también será un tipo. Dados 
        dos elementos $a\,:\,A$, $b\,:\,A$, tenemos el tipo $a\,=_{A}\,b$. Si existe un elemento del tipo $a\,=_{A}\,b$, luego tenemos
        que $a$ y $b$ son proposicionalmente iguales.
        
        Sin embargo en la teoría de tipos también tenemos otro tipo de igualdad, la igualdad por definición (o judgamental equality), la cual
        existe al mismo nivel que un juicio de tipado. Si definimos una función $f\,:\,\mathds{N} \rightarrow \mathds{N}$ mediante
        la ecuación $f(x)\,=\,x^2$, luego la expresión $f\,3$ es igual a $3^2$ \textbf{por definición}. Esta igualdad es algorítmicamente
        decidible y el chequeo es parte de la meta-teoría.
        
\end{itemize}

\subsection{Tipos funcionales}

Dados dos tipos $A$ y $B$ se puede construir un tipo $A \rightarrow B$ que representa funciones con dominio
en $A$ y codominio en $B$. Las funciones son un concepto primitivo en la teoría de tipos.

Dada un elemento $\tjud{f}{A \rightarrow B}$ y un $\tjud{a}{A}$, luego se puede \textit{aplicar} la función
$f$ a $a$, lo cual notamos con $f\,a$ y cuyo tipo es $\tjud{f\,a}{B}$.

Para construir elementos de un tipo funcional $A \rightarrow B$ se puede realizar una definición o utilizar la abstracción lambda. La
definición
\begin{align*}
  f\,x\,=\,\Phi
\end{align*}

donde $x$ es una variable y $\Phi$ una expresión que puede contener a $x$, es válida si se chequea que $\tjud{\Phi}{B}$ 
asumiendo $\tjud{x}{A}$.

La misma definición mediante la abstacción lambda sería:
\begin{align*}
  \lambda\,(\tjud{x}{A}).\Phi
\end{align*}

\noindent que cumple el juicio $\tjud{\lambda\,(\tjud{x}{A}).\Phi}{A \rightarrow B}$ bajo las mismas condiciones detalladas previamente
sobre $x$ y $\Phi$. A partir de que la expresión tiene tipo $A \rightarrow B$, el tipo de la variable $x$ puede inferirse, por lo
cual podemos omitir ponerlo explícitamente.

Con la definición de funciones se introduce una \textbf{regla de computación}, la cual es una igualdad por definición (judgamental equality):
\begin{align*}
  (\lambda\,x.\Phi)\,a\;\equiv\;\Phi'
\end{align*}

\noindent donde $\Phi'$ es igual a $\Phi$ en la cual todas las ocurrencias de $x$ son reemplazadas por $a$.

Otra regla que se introduce es la también conocida como \textbf{regla Eta}. Dado que tenemos definida una función 
$\tjud{f}{A \rightarrow B}$, se da la siguiente igualdad por definición:
\begin{align*}
  f \equiv \lambda\,x.f\,x
\end{align*}

\subsection{Universos y familias}

Como dijimos previamente, en teoría de tipos un elemento no existe en sí mismo si no que debe tener un tipo. Por lo tanto
¿qué son los tipos mismos? Un tipo $A$ también deberá tener un tipo. Usualmente se utiliza el término \textbf{universo}
para referir al tipo cuyos elementos son tipos. Esto podría dar lugar a una paradoja, ya que si tenemos un tipo que contiene
a todos los tipos, luego se contendría a sí mismo (la paradoja de Russell).

Para evitar la paradoja se introduce una jerarquía en los universos
\begin{align*}
  \tjud{U_0}{\tjud{U_1}{\tjud{U_2}{...}}}
\end{align*}

\noindent donde cada $U_i$ es un elemento de $U_{i+1}$, y más aún si $\tjud{A}{U_i}$, luego también $\tjud{A}{U_{i+1}}$.
Si no es necesario conocer a qué nivel de universo explícitamente pertenece un tipo, se lo suele omitir anotando simplemente   
$\tjud{A}{U}$.

Notemos entonces que podríamos tener una función que a partir de un valor de algún tipo retorne no un valor sino un tipo.
A este tipo de funciones se las suele llamar también \textbf{familia de tipos}:
\begin{align*}
  \tjud{B}{A \rightarrow U}
\end{align*}

\noindent Si se aplica $B$ a algún valor de tipo $A$, se obtiene un tipo.

\subsection{Funciones dependientes}

En la teoría de tipos podemos definir funciones más generales que las usuales, en donde el codominio puede depender
de valores del dominio. Al tipo de las funciones dependientes se las llama $\Pi-type$ en CITA.

Dado un tipo $\tjud{A}{U}$ y una familia $\tjud{B}{A \rightarrow U}$ podemos definir el tipo de las funciones dependientes
\begin{align*}
 \tjud{\depFun{x}{A}{B}}{U}
\end{align*}

\noindent un elemento de este tipo será una función que tome un valor $x$ de tipo $A$ y retorne uno de tipo $B\,x$. 
Notemos que si $B$ es constante tenemos el tipo de las funciones como lo definimos previamente.

Las reglas para este tipo son las mismas que definimos para las funciones comunes.

Si tenemos una función $\tjud{f}{\depFun{x}{A}{B}}$, \textit{para cada} elemento $\tjud{x}{A}$ podemos obtener
un elemento de $B\,x$, es decir, aplicando $f$ a cualquier $\tjud{x}{A}$ tenemos un habitante del tipo $B\,x$.
Notemos que si pensamos a los tipos como proposiciones, y consideramos que una proposición es válida cuando
el tipo que la representa tiene un elemento, el tipo de la función $f$ representa que \textit{para todo $\tjud{x}{A}$
vale $B\,x$}.

\subsection{Producto}

Dados dos tipos $\tjud{A}{U}$ y $\tjud{B}{U}$, introducimos el tipo $\tjud{A \times B}{U}$, al cual se lo suele llamar
\textbf{producto cartesiano}.

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
el primer elemento de un vector, como

\begin{verbatim}

head :: Vec a (Suc n) -> a
head (Const e _) = e
  
\end{verbatim}

la particularidad de esta implementación es que durante el checkeo de tipos
estamos eliminando la posibilidad de escribir \verb|head Empty|, donde 
si recordamos la implementación de \verb|head| realizada en la introducción,
esta nueva implementación sobre listas de cierto tamaño nos ahorra la prueba de 
que el tamaño de la lista es mayor que 0. Ahora bien, 
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
el segundo caso de pattern matching es valido ya que el primer argumento de
la suma se vuelve mas chico.

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

Esta función toma un tipo \verb|A| y retorna la función identidad para ese tipo. Ahora bien, algo que podría
ocurrir es que el tipo resultante dependa de muchos argumentos ocasionando que nuestra función
se sature de estos, cuando probablemente la gran mayoría no seán los argumentos
\textit{realmente esperados} de la función, para evitar esto y poder implementar funciones que toman
exactamente los parametros que \textit{esperamos}, es que en Agda se puede definir un tipo de argumento
que llamaremos implicito. Por ejemplo,
para el caso de la función identidad, deberíamos escribir \verb|id A a| en lugar de lo
posiblemente esperado \verb|id a|. Podemos escribir un argumento como implicitos simplemente encerrandolo entre
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

map : {A : Set} {B : Set} → (A → B) → List A → List B
map {A} {B} _ [] = []
map {B = B} f (x ∷ xs) = f x ∷ map f xs

mapFromNat : {B : Set} → (Nat → B) → List Nat → List B
mapFromNat = map {Nat}

mapToNat : {A : Set} → (A → Nat) → List A → List Nat
mapToNat = map {B = Nat}

\end{verbatim}

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

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (const x _) = x

\end{verbatim}

es importante notar que la condición de exhaustividad del checkeador de tipos
se cumple ya que no existe otra forma de construir algo de tipo \verb|Vec A (suc n)|
que no sea con el constructor \verb|const|.

\subsection{Dotted Patterns y Pattern Matching con with}

Consideremos la función \verb|zip| sobre vectores que dados dos vectores
de igual tamaño nos construye un vector de pares. Donde es importante
notar la restricción interesante que impone el hecho de que los vectores
sean de igual tamaño, el \verb|zip| implementado sobre listas permite
realizarlo sobre listas de distinto tamaño generando el probable recorte
de elementos al no tener estos con quien emparejarse.

\begin{verbatim}

zip : {A B : Set} {n : Nat} → Vec A n → Vec B n → Vec (A × B) n
zip empty empty = empty
zip (const a as) (const b bs) = const (a , b) (zip as bs)

\end{verbatim}

Podemos pensar ahora que ocurre si hacemos pattern matching en el 
argumento \verb|n : Nat| en el segundo caso

\begin{verbatim}

zip {n = (suc n)} (const {ma} a as) (const {mb} b bs) = ...

\end{verbatim}

notar que el \verb|n| del lado izquiero se refiere al nombre de variable
del tipo y el \verb|n| del lado derecho es una variable nueva donde hacer
pattern matching, cada vez que hablemos de \verb|n| nos referiremos a este
mismo. Ahora bien, este \verb|n| debería ser (y lo es) el único tamaño posible
de las listas \verb|as| y \verb|bs|, es decir \verb|ma = n = mb|.
¿cómo podemos remarcar esto en el caso de pattern matching?; la solución esta en
usar dotted patterns, para esto prefijamos el caso de pattern matching con un punto
(\verb|.|) de manera de marcar que el valor fue deducido por el chequeo de tipos
y no por pattern matching. Luego podemos escribir

\begin{verbatim}

zip {n = (suc n)} (const {.n} a as) (const {.n} b bs) = ...

\end{verbatim}

\comment{Esto es choreadisimo, pero esta bueno}

La regla para saber si un argumento debe tener prefijado el punto es: \textit{Si existe
un único valor para un argumento, este debe estar prefijado por el punto}.

Introduzcamos ahora la sentencia \verb|with| que nos permite agregar mas
argumentos a la función y realizar pattern matching de la forma usual, asi por ejemplo
esto nos permite combinar dos o mas argumentos y hacer pattern matching sobre su
resultado. La siguiente siguiente función de ejemplo retona la cantidad de elementos
que cumplen una cierta propiedad sobre un vector.

\begin{verbatim}

#-filter : {n : ℕ} {A : Set} → (A → Bool) → Vec A n → ℕ
#-filter p empty = zero
#-filter p (const x xs) with p x
... | true  = suc (#-filter p xs)
... | false = #-filter p xs

\end{verbatim}

Luego habiendo definido la función \verb|#-filter| podemos implementar la función
filter sobre los vectores.

\begin{verbatim}

filter : {n : ℕ} {A : Set} → (p : A → Bool) → (xs : Vec A n) → Vec A (#-filter p xs)
filter p empty = empty
filter p (const x xs) with p x
... | true  = const x (filter p xs)
... | false = filter p xs

\end{verbatim}

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
