
\section{Introducción}

El desarrollo de compiladores correctos es un tema de interés en Ciencias de la Computación
que se ha estudiado desde épocas tempranas. Morris (\cite{morris-73}) presentó un esquema
en el cual propone utilizar álgebras universales heterogéneas (\cite{birkhoff-70}) para probar la corrección
de un compilador, trabajo que luego extendió Thatcher (\cite{thatcher-80}). En
\cite{janssen-98} se realiza un análisis de los distintos trabajos existentes en el momento
con el objetivo de dar un esquema general para la traducción de lenguajes (no sólo lenguajes
de programación, sino que abarca distintas áreas). En este trabajo formalizamos un framework
similar al que propone Janssen.
El enfoque se basa en considerar la sintaxis abstracta de un lenguaje como el álgebra inicial
de una signatura multisort, y a cualquier otra álgebra como un posible dominio semántico,
teniendo definido por inicialidad un único homomorfismo (la semántica). El grupo conocido
como ADJ presentan esta manera de ver la sintaxis y semántica de los lenguajes en \cite{goguen-77}.

Introduzcamos un ejemplo sencillo para explicar el enfoque que formalizaremos, un compilador
de expresiones aritméticas en un código de máquina que manipula un stack.

\paragraph{Lenguaje fuente}
El lenguaje fuente son expresiones aritméticas simples: constantes, variables y suma. 

\begin{quote}
$ Expr  ::=  \;\; Nat  \;\; || \;\;  \mathit{Var} \;\; || \;\; Expr ⊕ Expr $
\end{quote}

\paragraph{Lenguaje target}
El lenguaje target es un código de máquina cuya ejecución manipulará una pila de números naturales. 

\begin{quote}
$ Code  ::=  \;\; push\,Nat  \;\; || \;\; load\, Var \;\; || \;\; Code \,;\, Code \;\; || \;\; add $
\end{quote}

\noindent En ambos casos, $Nat$ corresponde a las constantes naturales y $Var$ a variables.


\paragraph{Semántica fuente}
La semántica del lenguaje fuente podemos definirla como una función que asigna a cada expresión
una función que va de un estado de asignación de valores a variables, a un natural:

\begin{align*}
  &eval     :\;Expr \rightarrow State \rightarrow \mathds{N}\\
  &eval\;n \;=\; \lambda\,\upsigma \rightarrow n\\
  &eval\;v \;=\;\lambda\,\upsigma \rightarrow \upsigma\,v\\
  &eval\;(e_1 \oplus e_2)\;=\;\lambda\,\upsigma \rightarrow (eval\,e_1\,\upsigma) + (eval\,e_1\,\upsigma)\\
\end{align*}

\paragraph{Semántica target}
La semántica del lenguaje target asignará a cada código una función que va de un par consistente de un estado
y una pila, a otra pila. Podemos representar la pila con una lista de naturales:

\begin{align*}
  &exec     :\;Code \rightarrow Stack \times State \rightarrow Stack\\
  &exec\;(push\,n) \;=\; \lambda\,(s , \upsigma) \rightarrow (s : n)\\
  &exec\;(load\,v) \;=\;\lambda\,(s , \upsigma) \rightarrow (\upsigma\,v\,:\,s)\\
  &exec\;(c_1\,;\,c_2)\;=\;\lambda\,(s , \upsigma) \rightarrow exec\;c_2\;(\upsigma,exec\;c_1\;(\upsigma,s))\\
  &exec\;add \;\;\;\;\;\;\;=\;\lambda\,(n \, : \, m \, : \, s , \upsigma) \rightarrow (n \, + \, m \, : \, s)\\
\end{align*}

\noindent Observemos que $exec$ es una función parcial, ya que para el caso de $add$ sólo está definida
si en la pila hay por lo menos dos elementos.

\paragraph{Compilador}
El compilador llevará expresiones en $Expr$ a códigos en $Code$:

\begin{align*}
  &comp     :\;Expr \rightarrow Code\\
  &comp\;n \;=\; push\,n\\
  &comp\;v \;=\;load\,v\\
  &comp\;(e_1 \oplus e_2)\;=\;comp\,e_2\,;\,comp\,e_1\,;\,add\\
\end{align*}

\paragraph{Corrección}
Este compilador es correcto si se puede probar:
    \begin{center}
      $exec\,(comp\,e)\,(\upsigma,s)\,=\,eval\,e\,:\,s$
    \end{center}

En el enfoque que presentamos los lenguajes están definidos a partir
de dos signaturas $\Sigma_e$ y $\Sigma_c$, obteniendo sus álgebras de términos
$T_e$ y $T_c$. Los dominios semánticos, digamos $Sem$ y $Exec$, serán álgebras de
cada signatura respectivamente. En el primer caso cada elemento del carrier
del álgebra $Sem$ será una función con tipo $State \rightarrow \mathds{N}$, en el
segundo una función con tipo $Stack \times State \rightarrow Stack$. Las semánticas
quedan determinadas por el único homomorfismo que existe entre el álgebra de términos
y cada álgebra, por inicialidad. Tenemos entonces el siguiente diagrama:

\begin{diagram}
  T_e     &     &   &  &    &T_c\\
  \dTo_{hsem} &     &   &  &   &\dTo_{hexec}\\
  Sem      &     &   &  &    &Exec\\
\end{diagram}

La clave del enfoque consiste en poder ver a las álgebras (y homomorfismos) de la signatura $\Sigma_c$
como álgebras (y homomorfismos) de la signatura fuente $\Sigma_e$, para ello introduciremos
el concepto de \textit{transformador de álgebras} (similar a \textit{polynomial derivor},
que nombra Janssen, o \textit{derived signature morphism} en teoría de instituciones, \cite{mossakowski-15}).
Si $A$ es una $\Sigma_c$-álgebra, llamemos $A\sim$ a su transformada en $\Sigma_e$. Tenemos
entonces el siguiente diagrama:

\begin{diagram}
  T_e     &\rTo^{comp}    &T_c\sim\\
  \dTo_{hsem} & &\dTo_{hexec\sim}\\
  Sem      &  &Exec\sim\\
\end{diagram}

El compilador queda definido por el único homomorfismo que existe entre $T_e$ y $T_c\sim$.
Si podemos definir un homomorfismo $enc$ (o $dec$) entre $Sem$ y $Exec\sim$ (o viceversa), el diagrama conmuta
por inicialidad de $T_e$:

\begin{diagram}
  T_e     &\rTo^{comp}    &T_c\sim\\
  \dTo_{hsem} & &\dTo_{hexec\sim}\\
  Sem      & \pile{\rTo^{enc} \\ \lTo_{dec}}   &Exec\sim\\
\end{diagram}

\paragraph{Organización del texto}

En la segunda sección de este artículo formalizamos los conceptos de signatura, álgebra,
homomorfismo, inicialidad y álgebra de términos, obteniendo
una librería en Agda para el uso de álgebras universales en general. Se discuten
algunas decisiones de implementación. El resultado es similar al que obtiene
Venanzio Capretta en \cite{capretta-99}.

En la tercera sección introducimos el concepto de transformación de álgebras,
para llevar álgebras de la signatura target a la signatura source,
y probamos que los homomorfismos se preservan. Este concepto no está
en la bibliografía existente sobre formalización de álgebras universales.

En la cuarta sección damos el ejemplo completo del compilador de un lenguaje
de expresiones aritméticas simple presentado anteriormente, utilizando el
framework.
