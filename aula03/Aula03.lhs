---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lógica proposicional
---

Objetivos
=========

<!--
\begin{code}
module Aula03 where
\end{code}
-->

- Apresentar a visão intuicionista para a lógica proposicional.

- Apresentar o sistema de dedução natural para lógica proposicional.

Objetivos
=========

- Apresentar o cálculo de sequentes para a lógica proposicional.

- Apresentar o conceito de _corte_ e sua relação com computação.

Objetivos
=========

- Apresentar algoritmos para construção de provas da lógica proposicional.

Introdução
==========

Introdução
==========

- Um conceito central neste curso é o de _tipo_.

- Mas, o que é um tipo em uma linguagem de programaçãp?

Introdução
==========

- Diferentes autores apresentam as mais variadas definições
para o conceito de tipo.

Introdução
==========

- De acordo com Pierce:

"A type system is a tractable syntactic method for proving the
absence of certain program behaviors by classifying phrases
according to the kinds of values they compute."

Introdução
==========

- Implícito na definição de sistema de tipos de Pierce está
o conceito de tipo.
    - Tipo: classificação de trecho de programa de acordo com
      os valores que eles calculam.


Introdução
==========

- Dessa forma, podemos entender que um tipo consiste em uma
representação sintática do conjunto de valores por ele
representado.

Introdução
==========

- Podemos entender o tipo `Bool` como o conjunto

$$
\mathbb{B} = \{F, T\}
$$

Introdução
==========

- Mas e tipos funcionais, $A \to B$ ?

- Podemos interpretar como o conjunto de funções entre os conjuntos
$A$ e $B$.

Introdução
==========

- Essa visão remonta à tradição de definição do
significado de programas usando _semântica denotacional_.

Introdução
==========

- Semântica denotacional: definir o significado
utilizando uma função que associa a sintaxe a um objeto
matemático conhecido.

Introdução
==========

- Em um primeiro curso sobre lógica, é normal que
a abordagem denotacional seja utilizada para
definir o significado de fórmulas da lógica
proposicional.

Introdução
==========

- Semântica denotacional para lógica proposicional:
   - Tabelas verdade.

$$
\begin{array}{cc|c}
   A & B & A \supset B \\ \hline
   F & F & T \\
   F & T & T \\
   T & F & F \\
   T & T & T \\
\end{array}
$$

Introdução
==========

- Utilizando tabelas verdade, sabemos que a fórmula
$A \supset A$ é uma tautologia.

Introdução
==========

- A principal ideia a ser apresentada ao longo deste
curso é que proposições da lógica correspondem a
tipos em uma linguagem de programação.

Introdução
==========

- Conectivos da lógica serão entendidos como
diferentes construtores de tipos.

Introdução
==========

- Exemplo: A implicação lógica $A \supset B$ é interpretada
como o tipo funcional $A \to B$.


Introdução
==========

- Porém...
   - Proposições são entendidas como valores lógicos.
   - Tipos são entendidos como um conjunto de valores
     (não necessariamente lógicos).

- Como compatibilizar essas visões?

Introdução
==========

- A intepretação booleana de proposições é muito limitada.
- Sob essa visão, temos que tipos são essencialmente _vazios_
ou _não vazios_.

Introdução
==========

- Exemplo: O tipo `Int`, denota o conjunto de número inteiros.
   - Sob a interpretação booleana, ele seria entendido como
     uma proposição.

Introdução
==========

- Exemplo: Dessa forma, o  tipo Int $\to$ Int é interpretado
como uma implicação Int $\supset$ Int.

Introdução
==========

- Usando uma tabela verdade, podemos determinar quando o conjunto
Int $\to$ Int é ou não vazio:

$$
\begin{array}{c|c}
  \textrm{Int} & \textrm{Int} \supset \textrm{Int}\\ \hline
  \emptyset    & \{\bullet\} \\
  \{\bullet\}  & \{\bullet\} \\
\end{array}
$$

Introdução
==========

- Entendendo a tabela anterior...

$$
\begin{array}{c|c}
  \textrm{Int} & \textrm{Int} \supset \textrm{Int}\\ \hline
  \emptyset    & \{\bullet\} \\
\end{array}
$$

- Se a proposição $Int$ é falsa (representado por $\emptyset$), existe
uma função $\emptyset \to \emptyset$.
   - O próprio conjunto $\emptyset$!

Introdução
==========

- Entendendo a tabela anterior...

$$
\begin{array}{c|c}
  \textrm{Int} & \textrm{Int} \supset \textrm{Int}\\ \hline
  \{\bullet\}  & \{\bullet\} \\
\end{array}
$$

- Se Int é verdadeiro (representado por $\{\bullet\}$), o
conjunto Int $\to$ Int é não vazio.


Introdução
==========

- Porém, essa interpretação de proposições como valores
lógicos não permite diferenciarmos entre diferentes funções
de mesmo tipo.


Introdução
==========

- Exemplo: Considere o seguinte tipo Haskell

```haskell
[Int] -> [Int]
```

- Existem várias funções com esse tipo.
    - Exemplo concreto: algoritmos de ordenação.

Introdução
==========

- Logo, para um mesmo tipo, temos diferentes
funções com diferentes características.

Introdução
==========

- Dessa forma, se desejamos estabelecer uma
correspondência entre a lógica e linguagens,
devemos levar em consideração características
computacionais das demonstrações.

Introdução
==========

- Jean Yves Girard, importante lógico francês,
argumenta que existem 3 níveis de interpretação
da lógica: booleano, extensional e intencional.

Introdução
==========

- No nível booleano interpretamos proposições
como valores lógicos e estamos interessados na
existência ou não de provas.

Introdução
==========

- No nível extensional interpretamos proposições
como conjuntos e estamos interessados em quais
funções podem ou não ser definidas.

Introdução
==========

- No nível intensional estamos interessados nas
provas em si e como essas se comportam
computacionalmente.

Introdução
==========

- Nesse curso estamos interessados nas provas em si
e não somente se uma proposição é ou não demonstrável.

Introdução
==========

- Por isso, vamos estudar formalismos que definem a lógica
em termos do que pode ser demonstrado: a dedução natural e
o cálculo de sequentes.

Intuicionismo
=============

Intuicionismo
=============

- Lógica clássica: toda proposição é verdadeira ou falsa.
   - Princípio do 3$^o$ excluído.

Intuicionismo
=============

- Na lógica clássica, o significado de uma proposição
é dado pelos valores lógicos que esta pode assumir e não
se esta é demonstrável.

Intuicionismo
=============

- Na lógica intuicionista consideramos que uma proposição
é verdadeira somente se esta é demonstrável.

Intuicionismo
=============

- Seguinte essa interpretação, a demonstração de $A \land B$
consiste de um par de demonstrações: uma para $A$ e outra para $B$.

Intuicionismo
=============

- A demonstração de $A \lor B$ consiste da demonstração de $A$ ($B$)
e um marcador de que esta proposição é verdadeira.

Intuicionismo
=============

- A demonstração de $A \to B$ consiste de um processo que produz uma
demonstração de $B$ a partir de uma para $A$.

Intuicionismo
=============

- A demonstração de $\neg A$ consiste de um processo que produz um
absurdo a partir de uma demonstração de $A$.

Intuicionismo
=============

- Essa interpretação informal é exatamente a descrita pelo formalismo
conhecido como _dedução natural_.


Dedução Natural
===============


Dedução Natural
===============
