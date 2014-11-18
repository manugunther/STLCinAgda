\documentclass[spanish]{article}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}

 \usepackage[spanish]{babel}
 \usepackage{amsmath}
 \usepackage{dsfont}
  \usepackage[]{hyperref}
  \hypersetup{
    pdftitle={Tipos dependientes y Agda},
    pdfauthor={Alejandro Gadea, Emmanuel Gunther},
    pdfsubject={},
    pdfkeywords={Teoría de tipos,Programación funcional,Tipos dependientes,Cálculo Lambda,Agda},
    bookmarksnumbered=true,     
    bookmarksopen=true,         
    bookmarksopenlevel=1,       
    colorlinks=false,            
    pdfstartview=Fit,           
    pdfpagemode=UseOutlines,    % this is the option you were lookin for
    pdfpagelayout=TwoPageRight
  }
  
 \addto\captionsspanish{
  \renewcommand{\contentsname}%
    {Indice}%
}
 
 % This handles the translation of unicode to latex:

 \usepackage{ucs}
 \usepackage[utf8x]{inputenc}
 \usepackage{autofe}

 \date{}
 
 \usepackage{listings}

% Para escribir las reglas de tipado.
\usepackage{bussproofs} 

\usepackage{bigfoot}
 
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
 \DeclareUnicodeCharacter{964}{\ensuremath{\tau}}
 \DeclareUnicodeCharacter{960}{\ensuremath{\pi}}
 \DeclareUnicodeCharacter{955}{\ensuremath{\lambda}}
 \DeclareUnicodeCharacter{931}{\ensuremath{\Sigma}}
 \DeclareUnicodeCharacter{916}{\ensuremath{\Delta}}
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
  {\ensuremath{\Pi_{(\tjud{#1}{#2})}\,#3\,#1}}
 }
 \newcommand{\cprod}[2]
  {\ensuremath{#1 \times #2}
 }
 \newcommand{\depPair}[3]
 {\ensuremath{\Sigma_{(\tjud{#1}{#2})}\,#3\,#1}
 }

 
   
\title{Programación certificada mediante lenguajes con tipos dependientes}
\author{Alejandro Gadea, Emmanuel Gunther}

 \begin{document}


\maketitle

\tableofcontents
\newpage
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

Sin entrar en demasiados detalles, la línea \verb|head [] ()| expresa que este caso
es absurdo. Teniendo esta definición vemos que para poder aplicar la función \verb|head| sobre una lista \verb|xs|
tenemos que poder construir un elemento de \verb|0 < length xs|, lo que representa la
prueba de que la lista no es vacía. Por lo tanto nunca podríamos tener en un programa una llamada a \verb|head []|.

Un lenguaje con estas características permite garantizar la correctitud mediante un sistema de tipos
que permite escribir proposiciones lógicas como tipos mismos del lenguaje.

\medskip

En este trabajo estudiaremos un lenguaje con tipos dependientes: Agda. Para ello, primero haremos
un breve repaso de las bases de la teoría de tipos de Martin-Löf. Luego revisaremos las características
y generalidades del lenguaje Agda. Por último realizaremos una implementación en Agda de la inferencia de tipos
para el cálculo lambda simplemente tipado asegurando su corrección.


\section{Teoría de tipos}

Los sistemas de tipos más complejos que permiten expresar propiedades
sobre los programas se basan en la \textbf{teoría de tipos}. En ésta los tipos no son meros
representantes para conjuntos de elementos como en la mayoría de los lenguajes de programación, 
sino que proveen un poder expresivo más grande.
\medskip

La teoría de tipos es una teoría fundacional de la matemática, alternativa a la de conjuntos de Zermelo-Fraenkel.
El concepto principal en la teoría es el de \textbf{tipo}, el cual puede representar un conjunto de elementos
o también una proposición lógica. En este último caso, los elementos de un tipo serán pruebas de que la misma
es válida. 

En la teoría de tipos un elemento $x$ no puede existir en sí mismo si no es dentro de un tipo. Por lo tanto no se puede 
expresar algo como ``sea $x$ tal que cumple alguna propiedad", sino que $x$ debe introducirse junto con algún tipo: 
$\tjud{x}{A}$ significa que $x$ es un elemento de tipo $A$.

\subsection{Universos}

Puesto que un elemento no puede existir si no es dentro de un tipo, podríamos plantearnos qué son los tipos mismos. 
Un tipo $A$ también deberá tener algún tipo. Usualmente se utiliza el término \textbf{universo}.
para referir al tipo cuyos elementos son tipos. Esto podría dar lugar a una 
paradoja (ya que el tipo que contenga a todos los tipos en particular debería contenerse a sí mismo) y para evitarla se introduce una jerarquía en los universos:
\begin{align*}
  \tjud{U_0}{\tjud{U_1}{\tjud{U_2}{...}}}
\end{align*}

\noindent donde cada $U_i$ es un elemento de $U_{i+1}$, y más aún si $\tjud{A}{U_i}$, luego también $\tjud{A}{U_{i+1}}$.
Si no es necesario conocer a qué nivel de universo explícitamente pertenece un tipo, se lo suele omitir anotando simplemente   
$\tjud{A}{U}$.

\subsection{Definición de tipos}

La teoría se construye en base a la definición de tipos. Para introducir un nuevo tipo se debe especificar lo siguiente:

\begin{itemize}
  \item \textbf{reglas de formación}, que definen la manera en que se forma el tipo (bajo qué condiciones
       se puede formar).
  \item \textbf{constructores}, que definen cómo construir elementos del tipo que se está definiendo.
  \item \textbf{eliminadores}, los cuales representan cómo usar los elementos del tipo. Un eliminador 
        será un objeto que permite descomponer al tipo en otros tipos.
  \item \textbf{regla de computación}, que corresponde a la definición del eliminador, es decir, expresa cómo 
       un eliminador actúa sobre un constructor.
  \item \textbf{principio de unicidad} opcional, que permite expresar para algunos tipos que todo elemento
       está únicamente determinado por los resultados de aplicar eliminadores y que luego puede ser
       reconstruido a partir de esos resultados aplicando un constructor (puede pensarse como el dual de la regla
       de computación).
\end{itemize}

Para introducir entonces un nuevo tipo especificaremos al menos sus reglas de formación, sus constructores y 
sus eliminadores junto con las reglas de computación.

\subsection{Funciones}

\textbf{Regla de formación}:
Dados dos tipos $A$ y $B$ se puede construir un tipo $A \rightarrow B$ que representa funciones con dominio
en $A$ y codominio en $B$. Las funciones son un concepto primitivo en la teoría de tipos.
\smallskip

\textbf{Constructor}:
Para construir elementos de un tipo funcional $A \rightarrow B$ se puede realizar una definición o utilizar la abstracción lambda. La
definición
\begin{align*}
  f\,x\,=\,E
\end{align*}

\noindent donde $x$ es una variable y $E$ una expresión que puede contener a $x$, es válida si se chequea que $\tjud{E}{B}$ 
asumiendo $\tjud{x}{A}$.

La misma definición mediante la abstracción lambda sería:
\begin{align*}
  \lambda\,(\tjud{x}{A}).E
\end{align*}

\noindent que cumple el juicio $\tjud{\lambda\,(\tjud{x}{A}).E}{A \rightarrow B}$ bajo las mismas condiciones detalladas previamente
sobre $x$ y $E$. A partir de que la expresión tiene tipo $A \rightarrow B$, el tipo de la variable $x$ puede inferirse, por lo
cual podemos omitir ponerlo explícitamente.
\smallskip

\textbf{Eliminador}:
Dada una función $\tjud{f}{A \rightarrow B}$ y un elemento $\tjud{a}{A}$, luego se puede \textit{aplicar} la función
$f$ a $a$, lo cual notamos con $f\,a$ y cuyo tipo es $\tjud{f\,a}{B}$.

Con la definición de funciones se introduce una \textbf{regla de computación}:
\begin{align*}
  (\lambda\,x.E)\,a\;\equiv\;E [x \longrightarrow a]
\end{align*}

\textbf{Unicidad}:
Otra regla que se introduce es la también conocida como \textbf{regla Eta}. Dado que tenemos definida una función 
$\tjud{f}{A \rightarrow B}$, se da la siguiente igualdad por definición:
\begin{align*}
  f \equiv \lambda\,x.f\,x
\end{align*}

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

\subsection{Familias de tipos}

Podríamos tener una función que tome un valor de un tipo $A$ y retorne un elemento de $U$, es decir, que retorne
a su vez un tipo. A estas funciones se las suele llamar \textbf{familia de tipos}:
\begin{align*}
  \text{Dado } \tjud{A}{U} \text{, podemos definir }\tjud{B}{A \rightarrow U}
\end{align*}

\noindent Si se aplica $B$ a algún valor de tipo $A$, se obtiene un tipo.

\subsection{Otros tipos de datos}

Veremos como ejemplo algunos tipos de datos de la teoría de tipos:
\medskip

\noindent \textbf{Producto}
\smallskip

\textbf{Regla de formación:} Dados dos tipos $\tjud{A}{U}$ y $\tjud{B}{U}$, introducimos el tipo $\tjud{\cprod{A}{B}}{U}$, al cual se lo suele llamar
\textit{producto cartesiano}. 
\smallskip

\textbf{Constructor:} A partir de un elemento $\tjud{a}{A}$ y un $\tjud{b}{B}$ podemos construir el elemento
$\tjud{(a,b)}{\cprod{A}{B}}$. 
\smallskip

\textbf{Eliminadores y regla de computación:} Podemos definir dos eliminadores del tipo:
\begin{align*}
  &\tjud{pr_1}{\cprod{A}{B} \rightarrow A}\\
  &\tjud{pr_2}{\cprod{A}{B} \rightarrow B}\\
\end{align*}
\noindent mediante las reglas de computación
\begin{align*}
  &pr_1\,(a,b)\,=\,a\\
  &pr_2\,(a,b)\,=\,b\\
\end{align*}

\medskip

\noindent \textbf{Pares dependientes}
\medskip

De la misma forma que generalizamos el tipo de las funciones, podemos generalizar el de los pares, teniendo que el tipo
del segundo componente del par, \textit{dependa} del primer componente.
\smallskip

\textbf{Regla de formación:} Dados un tipo $\tjud{A}{U}$ y una familia $\tjud{B}{A \rightarrow U}$ definimos el tipo de pares dependientes
\begin{align*}
\depPair{x}{A}{B}
\end{align*}
\smallskip

\textbf{Constructores:} Para construir elementos de este tipo lo hacemos de la misma forma que con el producto, si tenemos $\tjud{a}{A}$, 
en el segundo componente tendremos algún $\tjud{b}{B\,a}$. 
\smallskip

\textbf{Eliminadores y regla de computación:} Las proyecciones tal como las definimos para el producto también podemos definirlas
aquí.
\smallskip

En el caso particular donde $B$ es constante, el tipo será el producto cartesiano.

Observemos que para poder obtener un elemento del tipo $\depPair{x}{A}{B}$, necesitaremos encontrar
un $\tjud{x}{A}$ de tal forma que el tipo $B\,x$ contenga un elemento. Es decir, el tipo $\depPair{x}{A}{B}$
será habitado si \textit{existe} un elemento $\tjud{x}{A}$ tal que $B\,x$ es habitado. De la misma manera
que pensamos al tipo de las funciones dependientes como el análogo al cuantificador universal de la teoría
de conjuntos, el tipo de los pares dependientes es análogo al cuantificador existencial.
\medskip

\noindent \textbf{Coproducto}
\smallskip

\textbf{Regla de formación:} Dados $\tjud{A}{U}$, $\tjud{B}{U}$, introducimos el tipo $\tjud{A + B}{U}$, normalmente llamado como \textbf{coproducto} y
que representa la unión disjunta en la teoría de conjuntos.
\smallskip

\textbf{Constructores:} Para construir un elemento de $\tjud{A + B}{U}$ tenemos dos maneras, a partir de un elemento $\tjud{a}{A}$, o a partir
de uno $\tjud{b}{B}$ con los constructores $inl\,:\,A \rightarrow A + B$ y $inr\,:\,B \rightarrow A + B$ respectivamente
(inyección izquierda o inyección derecha).
\smallskip

\textbf{Eliminadores y regla de computación:} Observemos que si tenemos una función $\tjud{g_0}{A \rightarrow C}$ (es decir, que obtiene un elemento de $C$ a partir de uno
de $A$) y otra función $\tjud{g_1}{B \rightarrow C}$ (obtiene un elemento de $C$ a partir de uno de $B$) podemos 
definir una función $f$ que a partir de un elemento del coproducto $A + B$ obtenga un elemento de $C$:
\begin{align*}
  &\tjud{f}{A + B \rightarrow C}\\
  &f\,(inl\,a)\,=\,g_0\,a\\
  &f\,(inr\,b)\,=\,g_1\,a\\
\end{align*}

\noindent \textbf{Tipo vacío}
\smallskip

\textbf{Regla de formación:} Podemos considerar el tipo que no tiene ningún elemento, el tipo vacío $\mathbf{0}$.
\smallskip

\textbf{Constructores:} Puesto que no hay ningún elemento que tenga tipo $\mathbf{0}$, no tenemos constructores.
\smallskip

\textbf{Eliminadores y regla de computación:} Mediante un eliminador podemos obtener un elemento de algún tipo $C$ a partir
de los constructores del tipo que se está definiendo. Observemos que como no tenemos constructores podemos pensar que
cualquier elemento puede obtenerse a partir del tipo vacío. Tenemos entonces un eliminador del tipo vacío que es una función
que no toma argumentos y construye un elemento de cualquier tipo.
\medskip

\noindent \textbf{Tipo unario}
\smallskip

\textbf{Regla de formación:} Podemos considerar el tipo que contiene exactamente un elemento: $\mathbf{1}$.
\smallskip

\textbf{Constructores:} El tipo contendrá un solo constructor: $\tjud{*}{\mathbf{1}}$.
\smallskip

\textbf{Eliminadores y regla de computación:} La única manera de obtener un elemento de un tipo $C$ a partir del tipo
unario es si ese elemento es tomando como argumento de la función de eliminación al mismo elemento. Entonces el eliminador
del tipo $\mathbf{1}$ será una función $\tjud{g}{C \rightarrow \mathbf{1} \rightarrow C}$.

\subsection{Proposiciones como tipos}

En la introducción de esta sección vimos que podemos tener una analogía entre
las proposiciones lógicas y los tipos. Si un tipo representa una proposición, la misma será válida si se encuentra un elemento
del tipo. Tenemos entonces una correspondencia entre la lógica constructivista y un lenguaje de programación con tipos de datos
con las características que vimos previamente. Esta correspondencia fue observada por primera vez por Haskell Curry y William
Howard y se la conoce como \textbf{``isomorfismo de Curry-Howard''}.

Si observamos las reglas de la lógica proposicional podemos ver que las reglas de formación,
de introducción y eliminación de los conectivos lógicos se corresponden con tipos. Por ejemplo
la fórmula $A \wedge B$ se puede probar si se pueden probar las fórmulas $A$ y $B$. Podemos ver que
el constructor del tipo $\cprod{A}{B}$ se corresponde directamente con esta regla: Para construir
un elemento de $\cprod{A}{B}$, se necesita un elemento $\tjud{a}{A}$ y un $\tjud{b}{B}$. 

De la misma manera que lo hicimos con el conectivo $\wedge$, podemos hacer una analogía con el resto de la lógica
proposicional:

\begin{itemize}
  \item $\mathbf{True}$ se corresponde con $\mathbf{1}$.
  \item $\mathbf{False}$ se corresponde con $\mathbf{0}$.
  \item $\mathbf{A \wedge B}$ se corresponde con $\cprod{A}{B}$.
  \item $\mathbf{A \vee B}$ se corresponde con $A + B$.
  \item $\mathbf{A \Rightarrow B}$ se corresponde con $A \rightarrow B$.
  \item $\mathbf{A \Leftrightarrow B}$ se corresponde con $\cprod{(A \rightarrow B)}{(B \rightarrow A)}$.
  \item $\mathbf{\neg A}$ se corresponde con $A \rightarrow \mathbf{0}$.
\end{itemize}

Si consideramos la lógica de predicados, agregando los cuantificadores universal y existencial, tenemos
también la siguiente correspondencia, como lo observamos previamente:

\begin{itemize}
  \item ($\forall x$, $P\,x$) se corresponde con $\depFun{x}{A}{B}$.
  \item ($\exists x$, $P\,x$) se corresponde con $\depPair{x}{A}{B}$.
\end{itemize}


\section{Agda}

En esta sección presentaremos el lenguaje de programación con tipos dependientes \textbf{Agda}
(referencia a Agda). Estudiaremos brevemente alguna de sus características y la manera
de expresar los principales conceptos de la teoría de tipos.

Se pretende que la sección sea autocontenida, salvo algunas
menciones a la sección anterior, y por lo tanto una introducción para quien
se esté iniciando en la programación en Agda. Por otro lado, si el lector
conoce conceptos como; tipos de datos, pattern matching, funciones dependientes,
familias de tipos de datos, sentencia \verb|with|, argumentos implícitos,
dotted patterns, etc. una opción puede ser dirigirse directo a la sección
siguiente.

Es importante mencionar que todos los ejemplos fueron compilados con
Agda 2.4.2.

\subsection{Introduciendo Agda}

En lenguajes como Haskell existe una división bien marcada entre los tipos
(\verb|Int|, \verb|Bool|, \verb|String|, etc) y los valores (\verb|0|,
{\verb|True|, {\verb|"Haskell"|, etc). En cambio en lenguajes con
tipos dependientes, como Agda, esta separación es menos clara. 

Para ejemplificar esto consideremos los clásicos vectores de algún tipo
con tamaño fijo. Podemos pensar en la siguiente implementación en
Haskell,

\begin{verbatim}

data Zero

data Suc n

data Vec a n where
    Empty :: Vec a Zero
    Const :: a -> Vec a n -> Vec a (Suc n)

\end{verbatim}

\noindent donde definimos los tipos \verb|Zero| y \verb|Suc n| sin constructores
con la finalidad de usarlos como \textit{valores} y de esta manera restringir
el tipo \verb|Vec|. A continuación podemos implementar la función que toma
el primer elemento de un vector, como

\begin{verbatim}

head :: Vec a (Suc n) -> a
head (Const e _) = e
  
\end{verbatim}

La particularidad de esta implementación es que durante el chequeo de tipos
estamos eliminando la posibilidad de escribir \verb|head Empty|, donde 
si recordamos la implementación de \verb|head| realizada en la introducción,
esta nueva implementación sobre listas de cierto tamaño nos ahorra la prueba de 
que el tamaño de la lista es mayor que 0. Ahora bien, 
esta implementación parece razonable
y cómoda de entender; el vector vacío tiene tamaño \verb|Zero| y si agrego
un elemento \verb|e| a un vector con tipo \verb|Vec a n| (de tamaño \verb|n|) esto
me construye un vector de tamaño \verb|Suc n|. Lamentablemente la utilización
de los tipos como valores no sólo no parece una forma prolija de usar los
tipos, si no que para utilizar una idea similar pero ahora donde los valores a
\textit{imitar} con tipos son mas complejos, podría derivar en implementaciones
difíciles de entender o directamente malas.

En este punto es donde la \textit{separación menos clara} entre tipos y valores de Agda
(y los lenguajes con tipado dependiente en general) que mencionábamos antes
nos puede resultar muy útil.

A continuación introducimos distintas características del lenguaje Agda 
con el fin de implementar el tipo de los vectores de un cierto tipo y tamaño, 
como anteriormente realizamos en Haskell.

\subsection{Tipos de datos y pattern matching}

Empecemos introduciendo la forma de declarar tipos de datos
\textit{como los de Haskell}. Podemos definir el tipo \verb|Nat| de los 
números naturales de la siguiente manera:
\begin{verbatim}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

\end{verbatim}
\verb|Nat| tendrá el tipo \verb|Set|, que representa el tipo de los tipos de datos
(en la sección 2 le llamamos $U$) y sus constructores serán \verb|zero| y \verb|suc|, 
mediante los cuales podemos obtener elementos del tipo que estamos definiendo.

Podemos definir funciones por
pattern matching como hacemos en haskell, pero con la importante salvedad de que
estamos obligados a cubrir todos los casos debido a que Agda no admite programas
que no terminen, de ser el caso el chequeador de tipos nos dará un error.

Como ejemplo de función, definimos la suma de dos naturales. Aprovechamos para mencionar que
Agda es muy flexible con los nombres de función (constructores, tipos, etc) cualquier
secuencia de símbolos sin espacios puede ser considerado un nombre válido, además
para declarar operadores infijos se hace uso del \verb|_| de manera tal que al
usar el operador se puede utilizar por ejemplo como \verb|n + m| o \verb|_+_ n m|.

\begin{verbatim}

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

\end{verbatim}

Teniendo en cuenta la exigencia de terminación que impone Agda, notar que
el segundo caso de pattern matching es válido ya que el primer argumento de
la suma se vuelve más chico.

\subsection{Funciones dependientes y argumentos implícitos}

Hasta acá repasamos como escribir tipos de datos y funciones de Haskell, en Agda.
Introducimos ahora las funciones dependientes, como funciones en las que en su signatura
el tipo resultante puede depender de los valores de los argumentos. 

En Agda podemos escribir \verb|(a : A) → B| como el tipo de una función que toma un \verb|a : A| y
retorna algo de tipo \verb|B|, en el cual probablemente aparezca \verb|a|(lo que se corresponde
con el tipo $\depFun{x}{A}{B}$ que introdujimos en la sección 2). Podemos definir la 
función identidad por ejemplo como,

\begin{verbatim}

id : (A : Set) → A → A
id _ = λ x → x

\end{verbatim}

Esta función toma un tipo \verb|A| y retorna la función identidad para ese tipo. 
Ahora bien, la implementación de la función identidad que dimos toma como primer
argumento un tipo con el fin de modelar el polimorfismo de tipos, pero ahora sucede
que para utilizar la función \verb|id| tenemos que suministrarle el tipo y la idea
de las funciones polimórficas es evitar esto, dejando que el tipo sea inferido por
el chequeador de tipos. Este problema se soluciona utilizando argumentos implícitos
los cuales se escriben encerrándolos entre llaves. Siguiendo con el ejemplo ahora
podemos implementar la función identidad de la siguiente manera

\begin{verbatim}

id : {A : Set} → A → A
id = λ x → x
\end{verbatim}

La declaración de los argumentos como implícitos nos exime de tener que pasarlos al
llamar a la función, pero existe la posibilidad de pasarlos si es que hiciera
falta o usarlos como un argumento normal en la declaración. La manera de usar a estos
argumentos implícitos es mediante llaves como cualquier otro argumento o además de las
llaves utilizando el nombre de la variable escrita en el tipo de la función

\begin{verbatim}

map : {A : Set} {B : Set} → (A → B) → List A → List B
map {A} {B} _ [] = []
map {B = B} f (x ∷ xs) = f x ∷ map f xs

\end{verbatim}

En este ejemplo se puede ver que para el caso de pattern matching en la lista vacía estamos usando
ambos argumentos implícitos utilizando el orden en el que aparecen en el tipo
de nuestra función. Otra posibilidad es, como mencionamos antes, utilizar
el nombre de la variable del tipo, por ejemplo en el caso en que la lista tiene
al menos un elemento podemos utilizar el nombre de variable \verb|B|,
de manera de evitar tener que utilizar el orden y como consecuencia tener
que mencionar todos los argumentos implícitos (previos) para referencia al argumento deseado.

\begin{verbatim}

mapFromNat : {B : Set} → (Nat → B) → List Nat → List B
mapFromNat = map {Nat}

mapToNat : {A : Set} → (A → Nat) → List A → List Nat
mapToNat = map {B = Nat}

\end{verbatim}

Como antes, para pasar argumentos implícitos a una función podemos de nuevo
utilizar el orden que determina el tipo de la función y el nombre de la variable
en el tipo. Así entonces, en \verb|mapFromNat| estamos fijando el tipo \verb|A|
y en \verb|mapToNat| estamos fijando el tipo \verb|B|.

\subsection{Familias de tipos de datos}

Veamos ahora cómo podemos definir familia de tipos indexadas implementando el
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
en Haskell, pero con la diferencia importante de que \verb|n| es un valor y no un tipo. 

Ahora podemos implementar la función que toma el primer elemento

\begin{verbatim}

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (const x _) = x

\end{verbatim}

Es importante notar que la condición de exhaustividad del checkeador de tipos
se cumple ya que no existe otra forma de construir algo de tipo \verb|Vec A (suc n)|
que no sea con el constructor \verb|const|.

\subsection{Más sobre pattern matching}

\subsubsection{Dotted patterns}
Consideremos la función \verb|zip| sobre vectores que dados dos vectores
de igual tamaño nos construye un vector de pares. El tipo \verb|Vec| nos permite
agregar la restricción de que el tamaño de los vectores sea el mismo (a diferencia
de la implementación de \verb|zip| con listas, donde no podríamos tener esta restricción).

\begin{verbatim}

zip : {A B : Set} {n : Nat} → Vec A n → Vec B n → Vec (A × B) n
zip empty empty = empty
zip (const a as) (const b bs) = const (a , b) (zip as bs)

\end{verbatim}

Notar que el tipo de los elementos del vector resultante de haber
aplicado \verb|zip| a dos vectores es \verb|A × B|, este tipo
se corresponde con el producto cartesiano definido en \comment{referencia
a la sección 2.5}.

Podemos pensar ahora qué ocurre si hacemos pattern matching en el 
argumento \verb|n : Nat| en el segundo caso

\begin{verbatim}

zip {n = (suc n)} (const {ma} a as) (const {mb} b bs) = ...

\end{verbatim}

Es importante mencionar que, teniendo en cuenta la igualdad que se encuentra 
entre llave en uno de los casos de pattern matching, el \verb|n| del 
lado izquierdo se refiere al nombre de variable
del tipo y el \verb|n| del lado derecho es una variable fresca donde hacer
pattern matching, cada vez que hablemos de \verb|n| nos referiremos a este
último. Ahora bien, este \verb|n| debería ser (y lo es) el único tamaño posible
de las listas \verb|as| y \verb|bs|, es decir \verb|ma = n = mb|.
¿cómo podemos remarcar esto en el caso de pattern matching?; la solución esta en
usar dotted patterns, para esto prefijamos el caso de pattern matching con un punto
(\verb|.|) de manera de marcar que el valor fue deducido por el chequeo de tipos
y no por pattern matching. Luego podemos escribir

\begin{verbatim}

zip {n = (suc n)} (const {.n} a as) (const {.n} b bs) = ...

\end{verbatim}

Como se menciona en \textit{citar Dependently Typed Programming in Agda}:

La regla para saber si un argumento debe tener prefijado el punto es: \textit{Si existe
un único valor para un argumento, este debe estar prefijado por el punto}.

\subsubsection{Pattern con with}
Introduzcamos ahora la sentencia \verb|with| que nos permite agregar mas
argumentos a la función y realizar pattern matching de la forma usual, teniendo
en cuenta la condición de exhaustividad. Así por ejemplo
esto nos permite combinar dos o mas argumentos y hacer pattern matching sobre su
resultado. La siguiente siguiente función de ejemplo retorna la cantidad de elementos
que cumplen una cierta propiedad sobre un vector.

\begin{verbatim}

#-filter : {n : Nat} {A : Set} → (A → Bool) → Vec A n → Nat
#-filter p empty = zero
#-filter p (const x xs) with p x
... | true  = suc (#-filter p xs)
... | false = #-filter p xs

\end{verbatim}

Luego habiendo definido la función \verb|#-filter| podemos implementar la función
filter sobre los vectores.

\begin{verbatim}

filter : {n : Nat} {A : Set} → 
         (p : A → Bool) → (xs : Vec A n) → Vec A (#-filter p xs)
filter p empty = empty
filter p (const x xs) with p x
... | true  = const x (filter p xs)
... | false = filter p xs

\end{verbatim}

\subsubsection{Pattern absurdo}

En la introducción se muestra la implementación de la función \verb|head| que
retorna el primer elemento de una lista con tipo \verb|List A| y se sugiere ignorar
el primer caso de pattern (\verb|head [] ()|). A este tipo de casos de pattern
los llamaremos patterns absurdos y se escriben como \verb|()|, la idea es que; así
como con dotted patterns podíamos simbolizar la existencia de un único valor, el 
pattern absurdo nos permite decir que ese caso nunca puede ocurrir ya que es 
imposible construir un valor de este tipo.

Así por ejemplo, introduciendo rápidamente una posible implementación para el
tipo \verb|≤|

\begin{verbatim}

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat}                  → zero ≤ n
  s≤s : {m n : Nat} (m≤n : m le n) → suc m ≤ suc n

\end{verbatim}

y definiendo al \verb|<| como

\begin{verbatim}

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

\end{verbatim}

podemos analizar el ejemplo de la función \verb|head|, el pattern
absurdo es ocasionado por \verb|head []| cuyo tipo, reemplazando valores,
será \verb|head [] : zero < zero → a|. Donde es claro notar que es imposible
construir un valor para el tipo \verb|zero < zero| o \verb|suc zero ≤ zero|
\footnote{Usamos \verb|zero| y \verb|suc zero| para evidenciar de forma mas clara
la imposibilidad de construir un valor de tal tipo. Sin embargo, escribir \verb|0| y \verb|1|
sería totalmente valido.} .

Finalmente, cuando sucede que existe un pattern absurdo no tenemos que
preocuparnos por dar una definición de función para ese caso.

\subsection{Tipos proposicionales y valores como pruebas}

Al comienzo de la sección anterior se menciona que, considerando a un tipo
\verb|A| como una proposición podemos decir que esta proposición es
cierta si podemos construir un valor \verb|a| que tenga tipo \verb|A|.

Podemos pensar entonces como será la implementación de la proposición \verb|False| (\verb|⊥|) 
como tipo de dato, la idea es que nunca podamos construirnos un valor de este tipo y
por lo tanto podemos implementarlo simplemente como un tipo vacío

\begin{verbatim}

data ⊥ : Set where

\end{verbatim}

El hecho de nunca poder construir un elemento del tipo \verb|⊥| y con ayuda del pattern absurdo,
podemos definir la función que llamaremos \verb|⊥-elim| y que implementará la idea
de que \textit{falso implica cualquier cosa}

\begin{verbatim}

⊥-elim : {Whatever : Set} → ⊥ → Whatever
⊥-elim ()

\end{verbatim}

Por otro lado, ¿cómo será la implementación de la proposición \verb|True| (\verb|⊤|)?; esta
vez necesitamos poder construir siempre un elemento, podemos entonces implementarlo de la siguiente
manera \footnote{La implementación original se realiza utilizando records en \verb|Data.Unit|}

\begin{verbatim}

data ⊤ : Set where
  tt : ⊤

\end{verbatim}

Siguiendo los pasos de la sección anterior, podemos introducir la igualdad de valores de un tipo,
es decir que dados dos valores de un mismo tipo, \verb|a : A| y \verb|b : A| vamos
a escribir \verb|a ≡ b : Set| para decir que los valores son iguales.

\begin{verbatim}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

\end{verbatim}

Es importante notar que la definición de igualdad que estamos dando dice, dado
un tipo \verb|A| y un elemento \verb|x : A| obtenemos una familia de 
\textit{pruebas} o \textit{valores} tal que se es igual a \verb|x|.

Podemos también implementar la negación proposicional, dado que tenemos
un tipo \verb|P|, escribimos \verb|¬ P| para referirnos a la negación del tipo.
Su implementación es directa de pensar en \textit{Principio de explosión}, es
decir, cualquier cosa es demostrable a partir de una contradicción

\begin{verbatim}

¬_ : Set → Set
¬ P = P → ⊥

\end{verbatim}

Ahora bien, habiendo definido \verb|¬| podemos definir un tipo de dato
que implemente la idea de que una proposición, o bien es cierta, o bien es falsa,
construyendo la prueba que corresponda. Podemos pensar a este tipo de dato
como el tipo \verb|Bool| pero con el agregado de que acarrea el valor o prueba
del por qué la proposición es cierta o porque es falsa.

\begin{verbatim}

data Dec (P : Set) : Set where
  yes :   P → Dec P
  no  : ¬ P → Dec P

\end{verbatim}

Por otro lado, podemos presentar además la noción de cuantificador existencial,
la cual como mencionamos antes, en la sección \comment{alguna referencia acá} se
corresponde con la idea de producto dependiente.\\

Mostrar la implementación esta fuera de la idea de esta sección;\footnote{Un 
lector mas interesado puede encontrar la definición en el módulo Data.Product} y
por esta razón simplemente presentamos la sintaxis necesaria y algunas
funciones útiles. Considerando los tipos \verb|A : Set| y \verb|B : A → Set| 
podemos escribir el tipo del producto dependiente como 
\verb|Σ[ x ∈ A ] B x|\footnote{Otra posibilidad
es escribir \verb|∃ (λ x → B x)|, que se puede leer 
como \textit{existe un x tal que B x}}, donde el constructor será \verb|_,_| y además
dispondremos de dos funciones \verb|proj₁| y \verb|proj₂| que nos
retornaran la primera y segunda componente de un par.

Podemos entonces usando el producto dependiente implementar una
versión del \verb|filter| mejorada, la cual no requiere calcular
de antemano el tamaño del nuevo vector con los elementos filtrados.

Tomando entonces \verb|Nat : Set| y \verb|Vec A : Nat → Set| podemos
escribir el producto dependiente \verb|Σ[ m ∈ Nat ] Vec A m|.

\begin{verbatim}

filter : {n : Nat} {A : Set} → 
         (A → Bool) → Vec A n → Σ[ m ∈ Nat ] Vec A m
filter p empty = zero , empty
filter {n = suc n'} p (const y vec) with p y
... | false = filter p vec
... | true  = let (m , vec') = filter p vec
              in (suc m , const y vec')

\end{verbatim}

\subsubsection{Pruebas}

Hasta acá hemos hablado de las proposiciones y los tipos, pero poco acerca
de los valores y las pruebas. Haciendo uso de lo que tenemos definido hasta
el momento y definiendo algunas cosas nuevas probemos algunas propiedades.

Podemos comenzar definiendo el tipo \textit{ser par} que nos permite construir
una prueba de que un natural es par, si este efectivamente lo es.

\begin{verbatim}

data IsEven : Nat → Set where
  pz   : IsEven zero
  psuc : {n : Nat} → IsEven n → IsEven (suc (suc n))

\end{verbatim}

Veamos algunos ejemplos para entender este tipo de dato, podemos
empezar probando que el \verb|0|\footnote{En general usaremos las versiones
sintácticamente azucaradas, salvo cuando haga falta mencionar su
construcción original} es par, escribiendo una función con tipo
\verb|IsEven zero|, donde la prueba es utilizar el constructor
\verb|pz| directamente

\begin{verbatim}

zeroIsEven : IsEven zero
zeroIsEven = pz

\end{verbatim}

pensemos ahora en probar que \verb|2| y \verb|4| son pares teniendo
en cuenta que \verb|2 = suc (suc zero)| y que \verb|4 = suc (suc 2)|
de igual manera que con el \verb|0|, nos podemos construir funciones con tipos 
\verb|IsEven 2| y \verb|IsEven 4|. Enfoquémonos en probar paso por paso
que dos es par; tenemos que construir un valor de tipo \verb|IsEven (suc (suc zero))|,
el constructor \verb|pz| no nos ayuda, pero si nos sirve el constructor \verb|psuc|, ahora
bien este constructor nos construye algo de tipo \verb|IsEven (suc (suc zero))| siempre
y cuando podamos suministrarle algo de tipo \verb|IsEven zero|, afortunadamente \verb|pz| ahora
sí nos sirve, por lo tanto la prueba queda

\begin{verbatim}

twoIsEven : IsEven 2
twoIsEven = psuc pz

\end{verbatim}

Si pensamos ahora la prueba de que \verb|4| es par, pasa algo parecido; necesitamos
construir un valor de tipo \verb|IsEven (suc (suc (suc (suc zero))))|, para esto
podemos utilizar de nuevo \verb|psuc| para lo cual necesitamos una prueba o valor de
tipo \verb|IsEven (suc (suc zero))|, por suerte esta es la prueba de que dos es par

\begin{verbatim}

fourIsEven : IsEven 4
fourIsEven = psuc twoIsEven

\end{verbatim}

Por otro lado, es interesante ver que no podemos probar que, por ejemplo, \verb|3| es
par. Utilicemos el mismo razonamiento que para \verb|2| y \verb|4|, necesitamos
construirnos un valor de tipo \verb|IsEven (suc (suc (suc zero)))|.
Usar \verb|pz| es imposible, pero podemos utilizar \verb|psuc|, luego necesitamos
construirnos un valor de tipo \verb|IsEven (suc zero)|; pero acá no podemos usar
\verb|pz|, ni \verb|psuc|.

Esta forma de pensar la manera de construir los valores o pruebas nos induce una
noción inductiva, ¿será posible entonces implementar una función que dado un
natural nos construya una prueba, si es que puede, de que este natural es par?; La
respuesta es sí y para esto podemos hacer uso del tipo \verb|Dec|. Con el cual
vamos a tener, o bien una prueba de que el natural es par o bien una prueba de 
la negación.

Comencemos definiendo el tipo de nuestra función, \verb|isEven|, que determina si un natural
es par o no, \verb|isEven : (n : Nat) → Dec (IsEven n)| recordamos que este tipo
tiene dos constructores con los siguientes tipos (ya pensando con \verb|IsEven| como
proposición)

\begin{verbatim}

- yes :    IsEven n  → Dec (IsEven n)
- no  : ¬ (IsEven n) → Dec (IsEven n)

\end{verbatim}

El primer caso de pattern matching es directo, esto es porque usando el constructor
\verb|yes : IsEven zero  → Dec (IsEven zero)| necesitamos una prueba de tipo
\verb|IsEven zero|, pero esto es utilizar el constructor \verb|pz|

\begin{verbatim}

isEven : (n : Nat) → Dec (IsEven n)
isEven zero = yes pz

\end{verbatim}

\noindent notar que el siguiente caso de pattern matching es preguntarse que sucede con \verb|suc zero|,
es decir \verb|zero| podría considerarse como el caso base para los pares y \verb|suc zero| como
el caso base para los impares, analicemos esto detenidamente:

\begin{verbatim}

isEven : (n : Nat) → Dec (IsEven n)
isEven (suc zero) = no (λ ())
\end{verbatim}

Necesitamos construir un valor de tipo \verb|IsEven (suc zero)|, vimos antes que esto es imposible
por lo tanto usamos el constructor \verb|no| que tiene tipo 
\verb|¬ IsEven (suc zero) → Dec (IsEven (suc zero))|.
Necesitamos entonces construir un valor de tipo \verb|¬ IsEven (suc zero)|, pero si recordamos la
definición de este tipo, tenemos que construirnos un valor de tipo \verb|IsEven (suc zero) → ⊥|. Es
decir, necesitamos construir una función que toma algo de tipo \verb|IsEven (suc zero)| y retorna
algo de tipo \verb|⊥|, por suerte ya vimos que es imposible construir un valor del tipo que requiere
el argumento de la función, así que podemos usar el pattern absurdo utilizando la notación lambda
para escribir funciones sin nombre\footnote{λ x → x, por ejemplo define la función identidad}.

Pasamos ahora al caso final de pattern matching, \verb|suc (suc n)|, tenemos que construirnos
un valor de tipo \verb|Dec (IsEven (suc (suc n)))|. Acá la solución ya no es tan directa y
tenemos que hacer uso de la recursión. Presentemos la implementación incompleta, donde solo
figura el caso en el que \verb|n| resulta ser par

\begin{verbatim}

isEven : (n : Nat) → Dec (IsEven n)
isEven (suc (suc n)) with isEven n
... | yes even = yes (psuc even)
... | no ¬even = no ¿?

\end{verbatim}

bien, usando \verb|with| podemos preguntarnos si \verb|n| es par o no. En caso de serlo
es interesante notar que el tipo de la prueba es \verb|even : IsEven n|, donde nosotros
necesitamos construir algo de tipo \verb|IsEven (suc (suc n))|. Por lo tanto usando \verb|psuc|
y \verb|even| nos construimos algo del tipo buscado y con \verb|yes| terminamos de construir
la prueba de tipo \verb|Dec (IsEven (suc (suc n)))|. Ahora bien, ¿qué tipo tiene la prueba que
necesitamos construir para el caso en el que \verb|n| no es par?; necesitamos una prueba de tipo
\verb|¬ IsEven (suc (suc n))| y tenemos además una prueba de que \verb|¬even : ¬ IsEven n|.

Utilizando \verb|¬even| podemos construirnos una función de tipo \verb|¬ IsEven (suc (suc n))|,
recordando, de nuevo, que podemos ver a la negación como una función del tipo en \verb|⊥|. Luego
podemos definir una función con tipo \verb|IsEven (suc (suc n)) → ⊥| de la siguiente manera

\begin{verbatim}

¬isEven : ¬ IsEven (suc (suc n))
¬isEven (psuc pn) = ¬even pn

\end{verbatim}

\noindent notar que como nuestra función toma algo de tipo \verb|IsEven (suc (suc n))| el único
constructor posible es el \verb|psuc| y por lo tanto el único caso de pattern matching
es \verb|psuc pn|, donde \verb|pn : IsEven n|. Recordemos que necesitamos construir
algo de tipo \verb|⊥|, teniendo en cuenta ahora \verb|pn|. Por suerte disponemos de
\verb|¬even : IsEven n → ⊥|, luego solo nos resta aplicar para obtener el tipo deseado.
\smallskip

Concluyendo, si juntamos todos los casos tenemos la implementación final de una función
que dado un natural retorna la prueba de si este es par o no.

\begin{verbatim}

isEven : (n : Nat) → Dec (IsEven n)
isEven zero = yes pz
isEven (suc zero) = no (λ ())
isEven (suc (suc n)) with isEven n
... | yes even = yes (psuc even)
... | no ¬even = no ¬isEven
  where
    ¬isEven : ¬ IsEven (suc (suc n))
    ¬isEven (psuc pn) = ¬even pn

\end{verbatim}

Finalizando con esta sección podemos pensar en dar una prueba de que
la asociatividad de la suma es válida. Para esto primero vamos a definirnos
la función \verb|cong|(ruence) para el tipo \verb|Nat|

\begin{verbatim}

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y

\end{verbatim}

La implementación de esta función se puede encontrar en el módulo 
\verb|Relation.Binary.PropositionalEquality| y escapa
al fin de esta sección presentarla. Por lo tanto, simplemente diremos que 
esta función dada una \verb|f : A → B| y una prueba de igualadad \verb|x ≡ y|
nos construye una prueba de la igualdad \verb|f x ≡ f y|.

Luego podemos definir la función \verb|plusAssoc|

\begin{verbatim}

plusAssoc : (a : Nat) → (b : Nat) → (c : Nat) → (a + b) + c ≡ a + (b + c)
plusAssoc zero b c = refl
plusAssoc (suc a) b c = cong suc (plusAssoc a b c)

\end{verbatim}

\noindent donde el primer caso de pattern matching es directo de notar que queremos
construir una prueba que tenga tipo \verb|(zero + b) + c ≡ zero + (b + c)|
pero que al aplicar la definición de la suma en ambos lados obtenemos que
necesitamos una prueba de tipo \verb|b + c ≡ b + c|, por lo cual podemos
utilizar \verb|refl|. Para el segundo caso de pattern matching necesitamos
construirnos una prueba de tipo \verb|((suc a) + b) + c ≡ (suc a) + (b + c)|,
de nuevo, aplicando la definición de la suma, dos veces del lado izquierdo y una del
lado derecho, obtenemos que necesitamos una prueba de tipo 
\verb|suc ((a + b) + c) ≡ suc (a + (b + c))|. 

Ahora bien, usando recursión tenemos que \verb|plusAssoc a b c| es una
prueba de tipo \verb|(a + b) + c ≡ a + (b + c)|, por lo tanto podemos utilizar
\verb|cong| aplicada a la función \verb|suc| y la prueba \verb|plusAssoc a b c|
para obtener la prueba del tipo que buscamos.

\section{Un inferidor de tipos para el cálculo lambda certificado}

Como dijimos en la introducción de este trabajo, los lenguajes con tipos dependientes permiten
asegurar propiedades del software en la construcción del mismo, mediante un sistema de tipos
fuerte.

Como ejercicio para ejemplificar el poder de expresividad de estos lenguajes, realizaremos
una implementación de la inferencia de tipos para una versión del cálculo lambda simplemente tipado
en el lenguaje \textbf{Agda}.

Para esta sección se asume que el lector conoce los conceptos básicos del cálculo lambda.

\subsection{Descripción del problema}

El cálculo lambda es la base de los lenguajes de programación funcionales. En el mismo
se puede representar la computación mediante la transformación de expresiones utilizando
una única regla de reducción (la regla beta) lo que lo convierte en un sencillo y poderoso
sistema formal para estudiar los principales conceptos de computación.

Una expresión o un término del cálculo lambda se define mediante las siguientes reglas:

\begin{itemize}
  \item Una variable es un término.
  \item Dados un término $t$ y una variable $x$, la abstracción $\lambda\,x.t$ es un término.
  \item Dados dos términos $t_0$, $t_1$, la aplicación $t_0\;t_1$ es un término.
\end{itemize}

A este lenguaje de expresiones podemos agregarle un sistema de tipos sencillo:

\begin{itemize}
  \item $\odot$ es un tipo.
  \item Si $\theta_0$ y $\theta_1$ son tipos, $\theta_0 \mapsto \theta_1$ es un tipo.
\end{itemize}

Un juicio de tipado expresará si un término $t$ bajo un contexto de asignaciones 
de tipos a variables $\pi$ tiene algún tipo $\theta$, el cual es único. Normalmente a un juicio
de tipado lo escribimos $\pi \vdash t :: \theta$.

Observemos que al contar solamente con un tipo básico $\odot$ la unicidad del tipado de expresiones
no podemos asegurarla: Consideremos como ejemplo la expresión ``identidad" $\lambda\,x\,.\,x$. Este término representa
la función que toma un valor y lo retorna. Observemos que podríamos pensar que tiene tipo ($\odot \mapsto \odot$), pero
también podría ser $(\odot \mapsto \odot) \mapsto (\odot \mapsto \odot)$, con lo cual violaríamos la noción
de unicidad que queremos tener en nuestros juicios de tipado.
Por esta razón modificamos la definición de términos del cálculo lambda agregando en la abstracción una anotación del tipo que debe tener
la variable:
\begin{itemize}
  \item Una variable es un término.
  \item Dados un término $t$, una variable $x$ y un tipo $\theta$ la abstracción $\lambda\,x_{\theta}\,.\,x$ es un término.
  \item Dados dos términos $t_0$, $t_1$, la aplicación $t_0\;t_1$ es un término.
\end{itemize}
Ahora entonces los términos ($\lambda\,x_{\odot}\,.\,x$) y ($\lambda\,x_{\odot \mapsto \odot}\,.\,x$) son distintos
y evitan cualquier tipo de ambigüedad para definir su tipado.
\medskip

Teniendo esta definición de los términos y tipos del cálculo lambda podemos definir los juicios de tipado 
mediante las siguientes reglas:

\begin{center}
\AxiomC{$(x,θ) ∈ π$}
\UnaryInfC{$ π ⊢ x : θ$}
\DisplayProof
\quad
\AxiomC{$π , (x,θ) ⊢ t : θ'$}
\UnaryInfC{$ π ⊢ λ x_θ\,.\,t : θ → θ'$}
\DisplayProof
\quad
\AxiomC{$π ⊢ t₀ : θ' → θ$}
\AxiomC{$π ⊢ t₁ : θ'$}
\BinaryInfC{$ π ⊢ t₀ \ t₁ : θ$}
\DisplayProof
\end{center}

Implementaremos entonces esta versión del cálculo lambda simplemente tipado en Agda y una función $infer$ que
dado un contexto $\pi$ y un término $t$, retorne si existe un tipo $\theta$ tal que $\pi \vdash t :: \theta$.

El tipo de la función que pretendemos implementar será entonces:

\begin{verbatim}
infer : (π : Ctx) → (t : LambdaTerm) → Dec (∃ (λ θ → π ⊢ t ∷ θ))
\end{verbatim}

\noindent asumiendo definidos los contextos y los términos lambda. Como vimos en la sección previa, el tipo
\verb|Dec| parametrizado en algún tipo \verb|A| permite representar o bien un elemento de \verb|A| (mediante el constructor
\verb|yes|), o bien un tipo de \verb|¬ A| (mediante el constructor \verb|no|). Notemos entonces que el resultado
de la implementación que buscamos contendrá una prueba de si existe o no un tipo que permita tener
un juicio de tipado válido.

\subsection{Librerías auxiliares}

Para la implementación utilizaremos varias librerías de Agda:

\begin{code}
module Lambda where

open import Data.String
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Function
\end{code}

\verb|String|, para representar las variables de los términos. \verb|PropositionalEquality| tiene definido el tipo de la igualdad
proposicional entre dos tipos, tal como lo explicamos en la sección 3. \verb|Nullary| para tener el tipo vacío $\bot$ y
el tipo \verb|Dec|.
\verb|Product| lo necesitamos para representar los pares (variable, tipo) en los contextos. \verb|Empty| tiene definido
el eliminador de $\bot$, es decir, la función que dado $\bot$ retorna cualquier cosa. Por último
\verb|Function| tiene definido el símbolo de aplicación $\$$, el cual es útil para evitar paréntesis excesivos.

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
$θ₁ ⟼ θ₂ ≡ θ₁' ⟼ θ₂'$ entonces $θ₁ ≡ θ₁'$ y $θ₂ ≡ θ₂'$. La función \verb|cong⟼⁻¹| expresa
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

Algunos ejemplos de términos del cálculo lambda según nuestra definición son:

\begin{code}

identity : LambdaTerm
identity = λ' "x" ∶ ⊙  ⟶  ″ "x" ″ 

twice : LambdaTerm
twice = λ' "f" ∶ (⊙ ⟼ ⊙) ⟶ λ' "x" ∶ ⊙  ⟶ ″ "f" ″ ● (″ "f" ″ ● ″ "x" ″)

dtwice : LambdaTerm
dtwice = twice ● twice

thrice : LambdaTerm
thrice = λ' "f" ∶ (⊙ ⟼ ⊙) ⟶ λ' "x" ∶ ⊙  ⟶ ″ "f" ″ ● (″ "f" ″ ● (″ "f" ″ ● ″ "x" ″))

\end{code}

\subsection{Contextos de tipado}

Para poder dar un tipo a un término tenemos que asignarle tipos a las variables.
Necesitamos entonces definir un contexto de asignación de variables a tipos, en el cual no queremos que
una misma variable ocurra dos veces. Esta restricción es muy importante y forma parte de la especificación
para definir contextos de tipado. Como veremos a continuación, esta restricción puede expresarse en
un lenguaje como Agda.

Definimos el tipo \verb|Ctx| junto con un tipo que dada una variable $x$ y un contexto $\pi$, expresa que 
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
expresan los constructores \verb|∉ø| y \verb|∉¬ø| respectivamente del tipo \verb|_∉_|.

\subsubsection{Equivalencia de contextos}

Con la definición que tenemos de los contextos podemos definir una relación de equivalencia:

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
en el resto no sean exactamente las mismas (en la definción de \verb|ctxEq|, $p$ puede
ser distinto de $p'$ pero ambos expresan que la variable no pertenece al resto del contexto).
\medskip

\subsubsection{Pertenencia a contextos}

Para poder definir juicios de tipado necesitamos una noción más. Si pensamos en la regla
para tipar una variable tenemos que una variable $x$ tiene tipo $\theta$ si el par $(x,\theta)$
pertenece al contexto de tipado. Por lo tanto necesitamos definir cuándo un par \textbf{pertenece}
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

En la definición del caso \verb|inTail| vemos que sólo se pide que el par se encuentra en la cola
de un contexto. Uno podría preguntarse ¿qué pasa si el par también ocurre en la cabeza? Es decir, 
¿por qué razón no pedimos también en la definición de \verb|inTail| que la variable \verb|x| sea
distinta de \verb|y|?
Por la manera en que definimos el tipo de los contextos sabemos que eso no puede pasar, ya que si un par
está en la cabeza de un contexto, tenemos una prueba de que no puede estar en la cola.

Observemos también que hemos definido separadamente dos tipos cuyo significado está muy relacionado:
el tipo \verb|_∉_| y el tipo \verb|_∈_|, de hecho deberían ser uno opuesto al otro. Esto es algo que queremos
que suceda pero no tenemos explícitamente nada definido que lo asegure. Pensemos entonces cómo podemos
expresar que una variable no pertenece a un contexto, sólo utilizando el tipo \verb|_∈_|. Recordemos
el tipo para expresar negación: Dado un tipo $A$, el tipo $\neg A$ es igual a $A \rightarrow \bot$, es decir
el tipo de las funciones que toman un elemento de $A$ y retornan algo en $\bot$, que es el tipo
vacío.

Si una variable $v$ no pertenece a un contexto $\pi$, esto quiere decir que ``no existe tipo $\theta$ tal que
$(v,\theta)$ pertenece a $\pi$". Podemos escribir un tipo en Agda que represente exactamente esto:
\verb|¬ (∃ (λ θ → (v , θ) ∈ π))| y definir algunas propiedades.

\begin{itemize}
  \item Si tenemos que no existe \verb|θ| tal que el par \verb|(v,θ)| no pertenece a un contexto
        extendido \verb|(w , θ') ▷ π' ｢ p ｣|, podemos deducir que tampoco pertenece al contexto
        \verb|π'| y que \verb|v| es distinto a \verb|w|:

\begin{code}
prop∈₁ : ∀ {v} {π} {v'} {θ'} {p} → 
         ¬ (∃ (λ θ → (v , θ) ∈ ((v' , θ') ▷ π ｢ p ｣))) →
         ¬ (∃ (λ θ → (v , θ) ∈ π)) × ¬ (v ≡ v')
prop∈₁ {θ' = θ'} t↑ = (t↑ ∘ map id inTail , 
                       λ v=v' → t↑ (θ' , inHead v=v' refl))
\end{code}

  \item Conversamente a lo anterior, si tenemos que no existe \verb|θ| tal que el par 
        \verb|(v,θ)| no pertenece al contexto \verb|π| y además \verb|v| es distinto
        a \verb|w| entonces tampoco pertenece al contexto extendido \verb|(w , θ') ▷ π' ｢ p ｣|:

\begin{code}
prop∈₂ : ∀ {π} {v} {w} {θ} {w∉π} → ¬ (v ≡ w) → 
          ¬ (∃ (λ θ → (v , θ) ∈ π)) → 
          ¬ (∃ (λ θ' → (v , θ') ∈ ((w , θ) ▷ π ｢ w∉π ｣)))
prop∈₂ v≠w p (θ' , inHead v=w _) = v≠w v=w
prop∈₂ v≠w p (θ' , inTail v∈π)   = p (θ' , v∈π)
\end{code}

% Dentro de este caso tenemos dos opciones: \verb|(v , θ) ∈ π| para algún \verb|θ| porque el par
% se encuentra en la cabeza de \verb|π|, o porque se encuentra en la cola, y esto está expresado en los dos
% casos de pattern matching. En el primero de ellos observemos que tenemos un elemento de
% \verb|v ≡ v'|, por lo cual podremos obtener $\bot$ ya que teníamos también \verb|¬ (v ≡ v')|.
% 
% En el último caso el constructor \verb|inTail| contiene un elemento de \verb|(v , θ) ∈ π'| pero también teníamos
% uno de \verb|v ∉ π'| por lo que podremos obtener $\bot$ utilizando una llamada recursiva.
% \medskip        

\end{itemize}

Definamos entonces una propiedad que exprese lo siguiente: Una variable $v$ no pertenece a un contexto $\pi$ si y solo si
no existe un tipo $\theta$ tal que $(v,\theta)$ pertenezca a $\pi$.

Queremos definir dos funciones que expresan estas implicaciones. La primera, a la que llamamos
\verb|∉↝| obtiene un elemento del tipo \verb|¬ (∃ (λ θ →| \\ \verb|(v , θ) ∈ π))| a partir de uno de 
\verb|v ∉ π|. 

\begin{code}

∉↝ : ∀ {v} {π} → v ∉ π → ¬ (∃ (λ θ → (v , θ) ∈ π))
∉↝ {π = ø} ∉ø (_ , ())
∉↝ {v} {(v' , θ') ▷ π' ｢ v'∉π' ｣} 
   (∉¬ø v∉π' v≠v') t = prop∈₂ v≠v' (∉↝ v∉π') t
   
\end{code}

En la definición realizamos pattern matching sobre \verb|v ∉ π| y sobre
\verb|∃ (λ θ →|\\ \verb|(v , θ) ∈ π)|.

El primero de los casos es cuando tenemos que \verb|v| no ocurre en \verb|π|
porque éste es vacío, es decir, tenemos el constructor \verb|∉ø|. Esto
nos deja un pattern absurdo para el segundo parámetro de la función ya
que no podemos construir un elemento de \verb|(v , θ) ∈ ø|.

El siguiente caso a contemplar es cuando \verb|v| no está en el contexto \verb|π = |\\ \verb|( v'  , θ' ) ▷ π' ｢ v'∉π' ｣|,
representado por el constructor \verb|∉¬ø|. Observemos que para definir este caso de pattern matching
tendremos un elemento de \verb|¬ (v ≡ v')| y uno de \verb|v ∉ π'|. A partir de este último podemos
hacer una llamada recursiva para obtener \verb|¬ (∃ (λ θ → (v , θ) ∈ π')| y entonces podemos utilizar
la propiedad que definimos previamente \verb|prop∈₂|.
\medskip

La otra implicación que queremos definir es que si no existe un tipo $\theta$ tal que
el par $(v,\theta)$ pertenece al contexto $\pi$, entonces $v$ no pertenece a $\pi$. Definimos una función
que llamamos \verb|∉↜| para expresar esto:

\begin{code}
   
∉↜ : ∀ {v} {π} → ¬ (∃ (λ θ → (v , θ) ∈ π)) → v ∉ π
∉↜ {π = ø} t↑           = ∉ø
∉↜ {π = (v' , θ') ▷ π' ｢ p ｣} t↑ = ∉¬ø (∉↜ (proj₁ $ prop∈₁ t↑)) 
                                       (proj₂ $ prop∈₁ t↑)
\end{code}

Aquí podemos hacer pattern matching en el parámetro implícito \verb|π|. Si es vacío
entonces no tenemos otra opción para el valor de retorno que \verb|∉ø|.

Si \verb|π = (v' , θ') ▷ π' ｢ p ｣| entonces el valor de retorno necesariamente tendremos que
construirlo con \verb|∉¬ø|. 
Para ello necesitamos dos elementos: uno de tipo \verb|v ∉ π'| y otro de \verb|¬ (v ≡ v')|. Pero
como tenemos un contexto extendido podemos utilizar la propiedad \verb|prop∈₁| y obtener
un elemento de \verb|¬ (∃ (λ θ → (v , θ) ∈ π))| y otro de \verb|¬ (v ≡ v')|, que es casi
lo que necesitamos, solo que al primero de estos tenemos que transformarlo mediante una llamada
recursiva a \verb|∉↜|.
\medskip



\subsubsection{Propiedades de los contextos de tipado}

Podemos definir otras propiedades interesantes sobre los contextos de tipado, que nos serán
útiles para definir la inferencia de tipos:

\begin{itemize}
  \item Si dos contextos $π₀$ y $π₁$ son equivalentes (es decir $π₀ ≈ π₁$) y
        la varible $v$ no pertenece a $π₀$, entonces $v$ no pertenece a $π₁$:
    
\begin{code}
substCtx∉ : ∀ {v} {π₀} {π₁} → π₀ ≈ π₁ → v ∉ π₀ → v ∉ π₁
substCtx∉ emptyCtxEq notInEmpty = notInEmpty
substCtx∉ {v} {t ▷ π₀ ｢ p ｣} {.t ▷ π₁ ｢ p' ｣} 
            (ctxEq e) (∉¬ø p₀ x=x') = 
              ∉¬ø (substCtx∉ e p₀) x=x'
\end{code}

  \item Si dos contextos $π₀$ y $π₁$ son equivalentes, los tipos $θ₀$ y $θ₁$ son iguales
        y el par $(x , θ₀)$ pertenece a $π₀$, entonces el par $(x , θ₁)$ pertenece a $π₁$:
  
\begin{code}
substCtx∈ : ∀ {x} {π₀} {π₁} {θ₀} {θ₁} → 
               π₀ ≈ π₁ → θ₀ ≡ θ₁ → (x , θ₀) ∈ π₀ → (x , θ₁) ∈ π₁
substCtx∈ emptyCtxEq refl x∈π₀ = x∈π₀
substCtx∈ {x} {(x' , θ') ▷ π₀' ｢ p ｣} {(.x' , .θ') ▷ π₁' ｢ p' ｣}
             (ctxEq π₀'≈π₁') refl (inHead x≡x' θ₀≡θ') = inHead x≡x' θ₀≡θ'
substCtx∈ {x} {(x' , θ') ▷ π₀' ｢ p ｣} {(.x' , .θ') ▷ π₁' ｢ p' ｣} 
             (ctxEq π₀'≈π₁') refl (inTail x∈π₀') = 
                           inTail (substCtx∈ π₀'≈π₁' refl x∈π₀' )
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

  \item Una última propiedad que queremos definir es que la pertenencia de una variable
        en un contexto es decidible, es decir dada una variable $v$ y un contexto $\pi$
        es decidible si existe un tipo $\theta$ tal que el par $(v,\theta)$ pertenece
        a $\pi$:
        
\begin{code}
v∈π? : (v : Var) → (π : Ctx) → Dec (∃ (λ θ → (v , θ) ∈ π))
v∈π? v ø = no (λ {(θ , ())})
v∈π?  v ( (w , θ) ▷ π' ｢ w∉π' ｣) with v ≟ w | v∈π? v π'
... | yes p   | _ = yes (θ , inHead p refl)
... | no _    | yes (θ' , v,θ'∈π') = yes (θ' , inTail v,θ'∈π')
... | no v≠w  | no p = no (prop∈₂ v≠w p)
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

De la misma forma que definimos algunas propiedades interesantes de los contextos de tipado, podemos
definir propiedades de los juicios. Observemos que si tenemos que dos contextos $π₀$ y $π₁$ son equivalentes
(bajo la noción de equivalencia que definimos), y que dos tipos $θ$ y $θ'$ son iguales, luego a partir
del juicio $π₀ ⊢ t ∷ θ$ podríamos obtener el juicio $π₁ ⊢ t ∷ θ'$. Esto lo expresamos en la función
\verb|substCtx|:

\begin{code}
substCtx : ∀ {π₀} {π₁} {t} {θ} {θ'} → 
           π₀ ≈ π₁ → θ ≡ θ' → π₀ ⊢ t ∷ θ → π₁ ⊢ t ∷ θ'
substCtx π₀≈π₁ refl (x∈π₀ ∣ᵥ) = substCtx∈ π₀≈π₁ refl x∈π₀ ∣ᵥ
substCtx {π₀} {π₁} {t = λ' v ∶ θᵥ ⟶ t₀} {θ = .θᵥ ⟼ θ}
          π₀≈π₁ refl (_∣ₗ {.t₀} {.v} {.θᵥ} {.θ} {.π₀} {x∉π₀} π₀⊢t∷θ) =
          _∣ₗ {p = substCtx∉ π₀≈π₁ x∉π₀} (substCtx (ctxEq π₀≈π₁) refl π₀⊢t∷θ) 
substCtx π₀≈π₁ refl (π₀⊢t∷θ ∧ π₀⊢t∷θ₁ ∣ₐ) =
        (substCtx π₀≈π₁ refl π₀⊢t∷θ) ∧ (substCtx π₀≈π₁ refl π₀⊢t∷θ₁ ) ∣ₐ
\end{code}

También podemos dar una propiedad que expresa que si se puede tipar una expresión, 
el tipo es único. A esta propiedad la llamamos \verb|uniqueType|:

\begin{code}
uniqueType : ∀ {π} {t} {θ} {θ'} → π ⊢ t ∷ θ → π ⊢ t ∷ θ' → θ ≡ θ'
uniqueType (x,θ∈π ∣ᵥ) (x,θ'∈π ∣ᵥ) = uniqueTypeVar x,θ∈π x,θ'∈π
uniqueType (_∣ₗ {θ = θ} π⊢t∷θ) (_∣ₗ {θ = .θ} π⊢t∷θ') = 
              cong (_⟼_ θ) $ uniqueType π⊢t∷θ $ substCtx (ctxEq reflCtx) refl π⊢t∷θ'
uniqueType {θ = θ} {θ' = θ'} 
           (_∧_∣ₐ {θ' = .θ} π⊢t∷θ₁⟼θ₂ π⊢t∷θ₁)
           (_∧_∣ₐ π⊢t∷θ₁'⟼θ₂' π⊢t∷θ₁') = 
                   proj₂ $ cong⟼⁻¹ (trans (uniqueType π⊢t∷θ₁⟼θ₂ π⊢t∷θ₁'⟼θ₂') 
                           (cong (λ θ → θ ⟼ θ') (sym (uniqueType π⊢t∷θ₁ π⊢t∷θ₁')))) --$
\end{code}

\subsection{Inferencia de tipos}

Con todo lo que hemos definido ahora podemos definir la inferencia de tipos. A partir 
de un contexto de asignaciones y de un término del cálculo lambda queremos obtener
si existe un tipo tal que se pueda construir juicio de tipado válido.

Para implementar la función \verb|infer|, haremos pattern matching en el término. Dividimos
entonces nuestra implementación de acuerdo a si tenemos una variable, una abstracción o una
aplicación:

\subsubsection{Variable}

La regla para el juicio de tipado de una variable es la siguiente:

\begin{center}
\AxiomC{$(x,θ) ∈ π$}
\UnaryInfC{$ π ⊢ x : θ$}
\DisplayProof
\end{center}

Observemos que para poder concluir que la variable $x$ tiene tipo $θ$
bajo el contexto $π$ necesitamos que el par $(x,θ)$ se encuentre en 
$π$. Podremos entonces inferir el tipo si esto se satisface: 

\begin{code}

inferVar : (π : Ctx) → (v : Var) → Dec (∃ (λ θ → π ⊢ ″ v ″ ∷ θ))
inferVar π v with v∈π? v π
inferVar π v | yes (θ' , v∈π) = yes (θ' , v∈π ∣ᵥ)
inferVar π v | no  v∈π↑ = no (λ { (θ' , v∈π ∣ᵥ) → v∈π↑ (θ' , v∈π) })

\end{code}

Utilizamos la función \verb|v∈π?| que definimos previamente para decidir
si la variable pertenece al contexto. Si es así obtendremos
un par con el tipo que tiene la variable en el contexto y la prueba, y es justo
lo que necesitamos para construir el juicio de tipado.

En el caso en que la variable no pertenezca al contexto retornaremos que no se puede tipar
el término, es decir construimos una función que dado un par con un tipo y un juicio 
de tipado retorna $\bot$.

\subsubsection{Abstracción lambda}

Para inferir una abstracción lambda tenemos la siguiente regla:

\begin{center}
\AxiomC{$π , (x,θ) ⊢ t : θ'$}
\UnaryInfC{$ π ⊢ λ x_θ\,.\,t : θ → θ'$}
\DisplayProof
\end{center}

Observemos que para poder inferir que el término $λ x_θ\,.\,t$ tiene tipo
$θ → θ'$ se tienen que dar dos cosas:

\begin{itemize}
  \item Que la variable $x$ no pertenezca al contexto $\pi$. Puesto que tenemos que los contextos
        bien construidos no repiten variables, para poder construir $π , (x,θ)$ necesariamente
        $x$ no podrá estar en $\pi$.
        
  \item Que bajo el contexto $π , (x,θ)$ el subtérmino $t$ tenga tipo $\theta'$.
\end{itemize}

Si alguna de estas dos condiciones no se cumple no podremos inferir un tipo para la abstracción. Definamos
entonces dos funciones que retornen que no existe un juicio de tipado bajo estas situaciones:

\begin{code}

noInferAbs₁ :  ∀ {v} {θᵥ} {θ} {π} {t} → (v , θ) ∈ π → 
             ¬ (∃ (λ θ' → π ⊢ λ' v ∶ θᵥ ⟶ t ∷ θ'))
noInferAbs₁ v∈π (⊙ , ())
noInferAbs₁ {θ = θ} v∈π (θᵥ ⟼ θ' , _∣ₗ {p = v∉π} π⊢λ't∷θ') = ∉↝ v∉π (θ , v∈π)

\end{code}

Si se da que \verb|(v , θ) ∈ π| entonces no existe tipo que permita construir un juicio válido
para el término \verb|π ⊢ λ' v ∶ θᵥ ⟶ t| bajo el contexto \verb|π|.

Como ya hicimos previamente, para negar un tipo existencial tenemos que construir $\bot$ a partir
de un par. En este caso, el segundo componente del par es un juicio de tipado para la abstracción.
Si recordamos la definición de los juicios de tipado vemos que uno de los parámetros necesarios
para poder construirlo es un elemento de \verb|v ∉ π|. A partir de éste, utilizando \verb|∉↝| obtenemos
una función que dado que existe \verb|θ| tal que \verb|(v , θ) ∈ π| retorna $\bot$ y entonces podemos aplicarla
al par \verb|(θ , v∈π)|.
\noindent

\begin{code}

noInferAbs₂ : {v : Var} {θ : Type} {π : Ctx} {t : LambdaTerm}
            {p : v ∉ π} → 
            ¬ (∃ (λ θ' → (v , θ) ▷ π ｢ p ｣ ⊢ t ∷ θ')) →
            ¬ (∃ (λ θ'' → π ⊢ λ' v ∶ θ ⟶ t ∷ θ''))
noInferAbs₂ {v} {θ} {π} {t} {p} 
            π⁺⊢t∷_↑ (.θ ⟼ θ' , _∣ₗ {.t} {.v} {.θ} {.θ'} {.π} {p'} t∷θ' ) = 
                   π⁺⊢t∷_↑ (θ' , substCtx (ctxEq reflCtx) refl t∷θ') 
noInferAbs₂ π⁺⊢t∷_↑ ( ⊙ , () )

\end{code}

Si se da que no existe un tipo \verb|θ'| tal que el término \verb|t| tiene tipo
\verb|θ'| bajo el contexto extendido \verb|π⁺| = \verb|(v , θ) ▷ π ｢ p ｣| (donde \verb|p| es una prueba
de que \verb|v ∉ π|) entonces tampoco existe un tipo para construir un juicio de tipado
válido para el término \verb|λ' v ∶ θ ⟶ t| bajo el contexto \verb|π|.

Para esta definición contamos con una función a la que llamamos \verb|π⁺⊢t∷_↑| que obtiene $\bot$ a partir de 
un par formado por un tipo \verb|θ'| y un juicio de tipado \verb|(v , θ) ▷ π ｢ p ｣ ⊢ t ∷ θ'|.
Lo que necesitamos es construir $\bot$ a partir de un par formado por algún tipo \verb|θ ⟼ θ'|
y un juicio de tipado \verb|π ⊢ λ' v ∶ θ ⟶| \verb|t ∷ θ ⟼ θ'|. Pero si vemos la definición de los juicios
de tipado, si tenemos este juicio para la abstracción, entonces tenemos un juicio 
\verb|(v , θ) ▷ π ｢ p' ｣ ⊢| \verb|t ∷ θ'| (donde \verb|p'| es una prueba de que \verb|v ∉ π|), que es casi
el mismo juicio que necesitamos para poder aplicar \verb|π⁺⊢t∷_↑|, sólo que el contexto no es exactamente el mismo
(puesto que no podemos asegurar que \verb|p| y \verb|p'| son iguales). Pero como tenemos definidas propiedades sobre
la equivalencia de contextos, podemos substituir uno por otro mediante la función \verb|substCtx| completando
la definición.
\medskip


Con estas dos funciones tenemos definido qué sucede cuando las condiciones necesarias para inferir una abstracción
no se cumplen. En el caso que sí se cumplan podemos inferir la abstracción:

\begin{code}
inferAbs : ∀ {v} {θ} {θ'} {π} {v∉π} {t} → ((v , θ) ▷ π ｢ v∉π ｣) ⊢ t ∷ θ' →
           ∃ (λ θ'' → π ⊢ λ' v ∶ θ ⟶ t ∷ θ'')
inferAbs {θ = θ} {θ' = θ'} π⁺⊢t∷θ' = (θ ⟼ θ' , π⁺⊢t∷θ' ∣ₗ)
\end{code}

Dado que las condiciones se dan, podemos concluir que existe un tipo, el cual es \verb|θ ⟼ θ'|, tal que
\verb|π ⊢ λ' v ∶ θ ⟶ t ∷ θ ⟼ θ'|.

\subsubsection{Aplicación}

Para inferir el tipo de una aplicación tenemos la siguiente regla:

\begin{center}
\AxiomC{$π ⊢ t₀ : θ' → θ$}
\AxiomC{$π ⊢ t₁ : θ'$}
\BinaryInfC{$ π ⊢ t₀ \ t₁ : θ$}
\DisplayProof
\end{center}

Tenemos entonces que para que el término $t₀ \ t₁$ tenga tipo $\theta$ bajo $\pi$ 
deben existir juicios de tipado para los subtérminos como lo expresa la regla. 

Como hicimos para la abstracción, pensemos qué condiciones deben darse para poder inferir
el tipo de la aplicación:

\begin{itemize}
  \item[1] Pueda inferirse un tipo para $t_0$ bajo $\pi$.
  \item[2] Pueda inferirse un tipo para $t_1$ bajo $\pi$.
  \item[3] El tipo inferido para $t_0$ no sea $⊙$.
  \item[4] El tipo de $t_0$ es algún $θ_0 ⟼ θ_0'$ y el de $t_1$
            es $θ_0$.
\end{itemize}

Definamos funciones para cuando estas cuatro condiciones no se cumplan:

\begin{code}

noInferApp₁ : ∀ {π} {t₀} {t₁} → ¬ (∃ (λ θ₀ → π ⊢ t₀ ∷ θ₀)) → 
              ¬ (∃ (λ θ → π ⊢ (t₀ ● t₁)  ∷ θ))
noInferApp₁ π⊢t₀∷_↑
            (θ' , _∧_∣ₐ {θ = θ} {θ' = .θ'} π⊢t₀∷θ⟼θ' π⊢t₁∷θ' ) = 
                                                 π⊢t₀∷_↑ (θ ⟼ θ' , π⊢t₀∷θ⟼θ')

\end{code}

\noindent Si no existe tipo \verb|θ| tal que \verb|π ⊢ t₀ ∷ θ| entonces podemos construir
$\bot$ asumiendo que tenemos un tipo \verb|θ'| y un juicio \verb|π ⊢ (t₀ ● t₁)  ∷ θ'|.
                                                 
\begin{code}

noInferApp₂ : ∀ {π} {t₀} {t₁} → ¬ (∃ (λ θ₁ → π ⊢ t₁ ∷ θ₁)) → 
              ¬ (∃ (λ θ → π ⊢ (t₀ ● t₁)  ∷ θ))
noInferApp₂ π⊢t₁∷_↑
            (θ' , _∧_∣ₐ {θ = θ} {θ' = .θ'} π⊢t₀∷θ⟼θ' π⊢t₁∷θ') = 
                                                  π⊢t₁∷_↑ (θ , π⊢t₁∷θ')

\end{code}

\noindent El caso para cuando no se puede inferir un tipo para \verb|t₁| es análogo.

\begin{code}

noInferApp₃ : ∀ {π} {t₀} {t₁} → π ⊢ t₀ ∷ ⊙ →
              ¬ ∃ (λ θ → π ⊢ (t₀ ● t₁) ∷ θ)
noInferApp₃ π⊢t₀∷⊙ (θ' , _∧_∣ₐ {θ = θ} π⊢t₁∷θ⟼θ' _) with ⊙ ≟ₜ θ ⟼ θ'
... | yes ()
... | no ⊙≡θ⟼θ'↑ = ⊙≡θ⟼θ'↑ $ uniqueType π⊢t₀∷⊙ π⊢t₁∷θ⟼θ' --$

\end{code}

\noindent Si tenemos un juicio \verb|π ⊢ t₀ ∷ ⊙| no podremos construir un juicio
\verb|π ⊢ (t₀ ● t₁) ∷ θ| ya que en la definición tenemos un elemento de
\verb|π ⊢ t₀ ∷ θ ⟼ θ'|, es decir, el tipo del subtérmino \verb|t₀| debe ser
uno construido con \verb|⟼|. Como tenemos definida la igualdad de tipos y como el tipado
de los términos es único, obtenemos el absurdo que necesitamos.
          

\begin{code}

noInferApp₄ : ∀ {π} {t₀} {t₁} {θ₀} {θ₀'} {θ₁} → π ⊢ t₀ ∷ θ₀ ⟼ θ₀' →
              π ⊢ t₁ ∷ θ₁ → ¬ (θ₀ ≡ θ₁) →
              ¬ ∃ (λ θ → π ⊢ (t₀ ● t₁) ∷ θ)
noInferApp₄ π⊢t₀∷θ₀⟼θ₀' π⊢t₁∷θ₁ θ₀≡θ₁↑ 
             (θ , π⊢t₀∷τ₀⟼τ₀' ∧ π⊢t₁∷τ₁ ∣ₐ) = 
              θ₀≡θ₁↑ $ trans (proj₁ $ cong⟼⁻¹ $ 
                              uniqueType π⊢t₀∷θ₀⟼θ₀' π⊢t₀∷τ₀⟼τ₀') 
                             (uniqueType π⊢t₁∷τ₁ π⊢t₁∷θ₁) --$

\end{code}

\noindent En este último caso tenemos que \verb|θ₀| es distinto de \verb|θ₁|, es decir
tenemos una función que dado un elemento \verb|θ₀ ≡ θ₁| obtiene $\bot$. Podemos
utilizar propiedades que definimos previamente para obtener este elemento y aplicar la función.
\medskip

Finalmente, si se dan las condiciones necesarias podemos inferir la aplicación:

\begin{code}

inferApp : ∀ {π} {t₀} {t₁} {θ₀} {θ} → 
           π ⊢ t₀ ∷ θ₀ ⟼ θ → π ⊢ t₁ ∷ θ₀ → 
           ∃ (λ θ' → π ⊢ (t₀ ● t₁) ∷ θ')
inferApp {θ = θ} π⊢t₀∷θ₀⟼θ π⊢t₁∷θ₀ = (θ , π⊢t₀∷θ₀⟼θ ∧ π⊢t₁∷θ₀ ∣ₐ)

\end{code}

\subsubsection{Definición de la función infer}

Ahora sí podemos definir la función \verb|infer|. Para hacerlo 
utilizamos pattern matching analizando si el término es una variable,
una abstracción o una aplicación. En el caso de estas dos últimas utilizamos
la sentencia \verb|with| para analizar cada una de las condiciones que deben satisfacerse
para poder construir el juicio de tipado tal como lo explicamos previamente y utilizamos
las funciones que definimos:

\begin{code}

infer : (π : Ctx) → (t : LambdaTerm) → Dec (∃ (λ θ → π ⊢ t ∷ θ))
infer π ″ v ″ = inferVar π v

infer π (λ' v ∶ θ ⟶ t) with v∈π? v π
... | yes (θᵥ , v∈π) = no (noInferAbs₁ v∈π)
... | no v∉π with infer ((v , θ) ▷ π ｢ ∉↜ v∉π ｣) t
...       | no t↑ = no (noInferAbs₂ t↑)
...       | yes (θ' , t∷θ') = yes (inferAbs t∷θ')

infer π (t₀ ● t₁) with infer π t₀ | infer π t₁
... | no ¬π⊢t₀∷θ⟼θ' | _ = no (noInferApp₁ ¬π⊢t₀∷θ⟼θ')
... | _ | no ¬π⊢t₁∷θ = no (noInferApp₂ ¬π⊢t₁∷θ)
... | yes (⊙ , π⊢t₀∷⊙) | yes _ = no (noInferApp₃ π⊢t₀∷⊙)
... | yes (θ₀ ⟼ θ₀' , π⊢t₀∷θ₀⟼θ₀') | yes (θ₁ , π⊢t₁∷θ₁) with θ₀ ≟ₜ θ₁
...            | no ¬θ₀≡θ₁ = no (noInferApp₄ π⊢t₀∷θ₀⟼θ₀' π⊢t₁∷θ₁ ¬θ₀≡θ₁)
...            | yes θ₀≡θ₁ = yes (inferApp π⊢t₀∷θ₀⟼θ₀' 
                                 (substCtx reflCtx (sym θ₀≡θ₁) π⊢t₁∷θ₁))

\end{code}

Si queremos considerar solo términos cerrados (sin variables libres) podemos utilizar la siguiente
función:

\begin{code}

inferType : (t : LambdaTerm) → Dec (∃ (λ θ → ø ⊢ t ∷ θ))
inferType = infer ø 

\end{code}

Obtuvimos entonces (luego de un poco de trabajo) un inferidor de tipos
para la definición del cálculo lambda que dimos, el cual no solo retorna un tipo
para un término en el caso que se pueda tipar, sino que si se puede construir
un juicio de tipado obtenemos el árbol de tipado y en el caso que no, obtenemos una prueba
de por qué no se puede tipar. 

Decimos que esta implementación está certificada, ya que tenemos una prueba formal de que el resultado
de nuestro programa es el correcto.

 \end{document}
