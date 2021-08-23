---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lógica proposicional - parte I
---

# Objetivos

## Objetivos

- Apresentar a visão intuicionista para a lógica proposicional.

- Apresentar o sistema de dedução natural para lógica proposicional.

## Objetivos

- Apresentar o cálculo de sequentes para a lógica proposicional.

- Apresentar o conceito de _corte_ e sua relação com computação.

# Introdução

## Introdução

- Um conceito central neste curso é o de _tipo_.

- Mas, o que é um tipo em uma linguagem de programação?

## Introdução

- Diferentes autores apresentam as mais variadas definições
para o conceito de tipo.

## Introdução

- De acordo com Pierce:

"A type system is a tractable syntactic method for proving the
absence of certain program behaviors by classifying phrases
according to the kinds of values they compute."

## Introdução

- Implícito na definição de sistema de tipos de Pierce está
o conceito de tipo.
    - Tipo: classificação de trecho de programa de acordo com
      os valores que eles calculam.


## Introdução

- Dessa forma, podemos entender que um tipo consiste em uma
representação sintática do conjunto de valores por ele
representado.

## Introdução

- Podemos entender o tipo `Bool` como o conjunto

$$
\mathbb{B} = \{F, T\}
$$

## Introdução

- Mas e tipos funcionais, $A \to B$ ?

- Podemos interpretar como o conjunto de funções entre os conjuntos
$A$ e $B$.

## Introdução

- Essa visão remonta à tradição de definição do
significado de programas usando _semântica denotacional_.

## Introdução

- Semântica denotacional: definir o significado
utilizando uma função que associa a sintaxe a um objeto
matemático conhecido.

## Introdução

- Em um primeiro curso sobre lógica, é normal que
a abordagem denotacional seja utilizada para
definir o significado de fórmulas da lógica
proposicional.

## Introdução

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

## Introdução

- Utilizando tabelas verdade, sabemos que a fórmula
$A \supset A$ é uma tautologia.

## Introdução

- A principal ideia a ser apresentada ao longo deste
curso é que proposições da lógica correspondem a
tipos em uma linguagem de programação.

## Introdução

- Conectivos da lógica serão entendidos como
diferentes construtores de tipos.

## Introdução

- Exemplo: A implicação lógica $A \supset B$ é interpretada
como o tipo funcional $A \to B$.

## Introdução

- Porém...
   - Proposições são entendidas como valores lógicos.
   - Tipos são entendidos como um conjunto de valores
     (não necessariamente lógicos).

- Como compatibilizar essas visões?

## Introdução

- A intepretação booleana de proposições é muito limitada.
- Sob essa visão, temos que tipos são essencialmente _vazios_
ou _não vazios_.

## Introdução

- Exemplo: O tipo `Int`, denota o conjunto de número inteiros.
   - Sob a interpretação booleana, ele seria entendido como
     uma proposição.

## Introdução

- Exemplo: Dessa forma, o  tipo Int $\to$ Int é interpretado
como uma implicação Int $\supset$ Int.

## Introdução

- Usando uma tabela verdade, podemos determinar quando o conjunto
Int $\to$ Int é ou não vazio:

$$
\begin{array}{c|c}
  \textrm{Int} & \textrm{Int} \supset \textrm{Int}\\ \hline
  \emptyset    & \{\bullet\} \\
  \{\bullet\}  & \{\bullet\} \\
\end{array}
$$

## Introdução

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

## Introdução

- Entendendo a tabela anterior...

$$
\begin{array}{c|c}
  \textrm{Int} & \textrm{Int} \supset \textrm{Int}\\ \hline
  \{\bullet\}  & \{\bullet\} \\
\end{array}
$$

- Se Int é verdadeiro (representado por $\{\bullet\}$), o
conjunto Int $\to$ Int é não vazio.


## Introdução

- Porém, essa interpretação de proposições como valores
lógicos não permite diferenciarmos entre diferentes funções
de mesmo tipo.


## Introdução

- Exemplo: Considere o seguinte tipo Haskell

```haskell
[Int] -> [Int]
```

- Existem várias funções com esse tipo.
    - Exemplo concreto: algoritmos de ordenação.

## Introdução

- Logo, para um mesmo tipo, temos diferentes
funções com diferentes características.

## Introdução

- Dessa forma, se desejamos estabelecer uma
correspondência entre a lógica e linguagens,
devemos levar em consideração características
computacionais das demonstrações.

## Introdução

- Jean Yves Girard, importante lógico francês,
argumenta que existem 3 níveis de interpretação
da lógica: booleano, extensional e intencional.

## Introdução

- No nível booleano interpretamos proposições
como valores lógicos e estamos interessados na
existência ou não de provas.

## Introdução

- No nível extensional interpretamos proposições
como conjuntos e estamos interessados em quais
funções podem ou não ser definidas.

## Introdução

- No nível intensional estamos interessados nas
provas em si e como essas se comportam
computacionalmente.

## Introdução

- Nesse curso estamos interessados nas provas em si
e não somente se uma proposição é ou não demonstrável.

## Introdução

- Por isso, vamos estudar formalismos que definem a lógica
em termos do que pode ser demonstrado: a dedução natural e
o cálculo de sequentes.

# Intuicionismo

## Intuicionismo

- Lógica clássica: toda proposição é verdadeira ou falsa.
   - Princípio do 3$^o$ excluído.

## Intuicionismo

- Na lógica clássica, o significado de uma proposição
é dado pelos valores lógicos que esta pode assumir e não
se esta é demonstrável.

## Intuicionismo

- Na lógica intuicionista consideramos que uma proposição
é verdadeira somente se esta é demonstrável.

## Intuicionismo

- Seguinte essa interpretação, a demonstração de $A \land B$
consiste de um par de demonstrações: uma para $A$ e outra para $B$.

## Intuicionismo

- A demonstração de $A \lor B$ consiste da demonstração de $A$ ($B$)
e um marcador de que esta proposição é verdadeira.

## Intuicionismo

- A demonstração de $A \supset B$ consiste de um processo que produz uma
demonstração de $B$ a partir de uma para $A$.

## Intuicionismo

- A demonstração de $\neg A$ consiste de um processo que produz um
absurdo a partir de uma demonstração de $A$.

## Intuicionismo

- Essa interpretação informal é exatamente a descrita pelo formalismo
conhecido como _dedução natural_.


# Dedução Natural


## Dedução Natural

- Sintaxe

$$
\begin{array}{lcll}
  \varphi & \to  & \bot & \textrm{falso}\\
          & \mid & \top & \textrm{verdadeiro}\\
          & \mid & A    & \textrm{variáveis}\\
          & \mid & \varphi \supset \varphi & \textrm{implicação}\\
          & \mid & \varphi \land \varphi & \textrm{conjunção}\\
          & \mid & \varphi \lor \varphi & \textrm{disjunção}\\
          & \mid & \neg \varphi & \textrm{negação}\\
\end{array}
$$


## Dedução Natural

- Precedência: $\neg, \land, \lor, \supset$.

- Associatividade: $\supset$ à direita.

## Dedução Natural

- Denominamos por _contexto_ uma lista de
fórmulas.

$$
\Gamma = [\varphi_1, ... \varphi_n]
$$

## Dedução Natural

- Um _sequente_ é um par formado por um contexto e uma
fórmula.

$$\Gamma \vdash \varphi$$


- Um sequente $\Gamma \vdash \varphi$ pode ser lido
como "usando as hipóteses em $\Gamma$ é possível
deduzir $\varphi$."

## Dedução Natural

- O sistema de dedução natural é apresentado como
um conjunto de _regras de inferência_.

## Dedução Natural

- Uma regra de inferência possui a forma
   - $\Gamma \vdash\varphi_i$ : premissas.
   - $\Gamma\vdash \varphi$ : conclusão.

$$
\dfrac{\Gamma \vdash \varphi_1\,\,...\,\,\Gamma\vdash\varphi_n}
      {\Gamma \vdash \varphi}
$$


## Dedução Natural

- Regras de inferência são formadas por um axioma e
dois tipos de regras para cada um dos conectivos.

## Dedução Natural

- _Regras de eliminação_: Permitem o uso de uma
fórmula com um certo conectivo.
    - Premissa principal é a mais à esquerda em
      regras.

## Dedução Natural

- _Regras de introdução_: Permite deduzir uma fórmula
com um certo conectivo.

## Dedução Natural

- Axioma

$$
\dfrac{}{\Gamma, \varphi, \Gamma' \vdash \varphi}
$$

## Dedução Natural

- Regra de introdução da conjunção.

$$
\dfrac{\Gamma\vdash \varphi_1\,\,\,\,\Gamma\vdash\varphi_2}
      {\Gamma\vdash\varphi_1 \land \varphi_2}
$$

## Dedução Natural

- Regras de eliminação da conjunção.

$$
\begin{array}{c}
  \dfrac{\Gamma \vdash \varphi_1 \land \varphi_2}
        {\Gamma \vdash \varphi_1} \\ \\
  \dfrac{\Gamma \vdash \varphi_1 \land \varphi_2}
        {\Gamma \vdash \varphi_2}
\end{array}
$$

## Dedução Natural

- Regra de introdução da implicação

$$
\dfrac{\Gamma, \varphi_1 \vdash \varphi_2}
      {\Gamma \vdash \varphi_1 \supset \varphi_2}
$$

## Dedução Natural

- Regra de eliminação da implicação

$$
\dfrac{\Gamma \vdash \varphi_1 \supset \varphi_2\,\,\,\,\,\,\,\Gamma\vdash\varphi_1}
      {\Gamma\vdash \varphi_2}
$$


## Dedução Natural

- Exemplo: $\{A \land B \supset C\} \vdash A \supset B \supset C$.


## Dedução Natural

- Exemplo: $\{A \land B \supset C\} \vdash A \supset B \supset C$.

$$
\dfrac{}{A \supset B \supset C}
$$

## Dedução Natural

- Exemplo: $\{A \land B \supset C\} \vdash A \supset B \supset C$.

$$
\dfrac{
   \dfrac{}
         {B \supset C}
}{A \supset B \supset C}
$$

## Dedução Natural

- Exemplo: $\{A \land B \supset C\} \vdash A \supset B \supset C$.

$$
\dfrac{
   \dfrac{
      \dfrac{
      }{C}
   }{B \supset C}
}{A \to B \supset C}
$$


## Dedução Natural

- Exemplo: $\{A \land B \supset C\} \vdash A \supset B \supset C$.

$$
\dfrac{
   \dfrac{
      \dfrac{
         \dfrac{}
               {A \land B \supset C}
         \,\,\,\,
         \dfrac{}
               {A \land B}
      }{C}
   }{B \supset C}
}{A \to B \supset C}
$$


## Dedução Natural

- Exemplo: $\{A \land B \supset C\} \vdash A \supset B \supset C$.

$$
\dfrac{
   \dfrac{
      \dfrac{
         \dfrac{}
               {A \land B \supset C}
         \,\,\,\,
         \dfrac{
            \dfrac{}{A} \,\,\,\,\dfrac{}{B}
         }{A \land B}
      }{C}
   }{B \supset C}
}{A \to B \supset C}
$$

## Dedução Natural

- Regras de introdução da disjunção.

$$
\begin{array}{cc}
  \dfrac{\Gamma\vdash \varphi_1}
        {\Gamma\vdash \varphi_1 \lor \varphi_2} &
  \dfrac{\Gamma\vdash \varphi_2}
        {\Gamma\vdash \varphi_1 \lor \varphi_2}
\end{array}
$$

## Dedução Natural

- Regras de eliminação da disjunção.

$$
\dfrac{\Gamma\vdash \varphi_1\lor \varphi_2\,\,\,\,\,\,
       \Gamma,\varphi_1\vdash\varphi\,\,\,\,\,\,
       \Gamma,\varphi_2\vdash\varphi}
      {\Gamma\vdash \varphi}
$$

## Dedução Natural

- Regra de eliminação do falso.

$$
\dfrac{\Gamma \vdash \bot}
      {\Gamma \vdash \varphi}
$$

## Dedução Natural

- Regra de introdução do verdadeiro.

$$
\dfrac{}{\Gamma\vdash \top}
$$

## Dedução Natural

- Mas não estão faltando regras?
   - Introdução do falso...
   - Eliminação do verdadeiro...

## Dedução Natural

- Não! Está ok.
   - Não é possível introduzir $\bot$.
   - Não é possível eliminar $\top$.

## Dedução Natural

- Negação é tratada como a implicação.
    - Logo, não há necessidade de regras para
      a negação.

$$
\neg \varphi \equiv \varphi \supset \bot
$$

## Dedução Natural

Exemplo: $\{A \supset B\}\vdash \neg B \supset \neg A$


## Dedução Natural

Exemplo: $\{A \supset B\}\vdash \neg B \supset \neg A$

$$
\dfrac{}
      {\neg B \supset \neg A}
$$

## Dedução Natural

Exemplo: $\{A \supset B\}\vdash \neg B \supset \neg A$

$$
\dfrac{
  \dfrac{}{\neg A}
}{\neg B \supset \neg A}
$$

## Dedução Natural

Exemplo: $\{A \supset B\}\vdash \neg B \supset \neg A$

$$
\dfrac{
  \dfrac{
     \dfrac{}{\bot}
  }{\neg A}
}{\neg B \supset \neg A}
$$

## Dedução Natural

Exemplo: $\{A \supset B\}\vdash \neg B \supset \neg A$

$$
\dfrac{
  \dfrac{
     \dfrac{
        \dfrac{}{\neg B}\,\,\,\,
        \dfrac{}{B}
     }{\bot}
  }{\neg A}
}{\neg B \supset \neg A}
$$

## Dedução Natural

Exemplo: $\{A \supset B\}\vdash \neg B \supset \neg A$

$$
\dfrac{
  \dfrac{
     \dfrac{
        \dfrac{}{\neg B}\,\,\,\,
        \dfrac{
          \dfrac{}{A \supset B}\,\,\,\,
          \dfrac{}{A}
        }{B}
     }{\bot}
  }{\neg A}
}{\neg B \supset \neg A}
$$

## Dedução Natural

- Além das regras apresentadas, a dedução
natural conta com regras _estruturais_.

- Essas regras lidam com o contexto de hipóteses.

## Dedução Natural

- Weakening

$$
\dfrac{\Gamma,\Gamma'\vdash\varphi}
      {\Gamma,\varphi',\Gamma' \vdash \varphi}
$$

## Dedução Natural

- Exchange

$$
\dfrac{\Gamma,\varphi_1,\varphi_2,\Gamma'\vdash\varphi}
      {\Gamma,\varphi_2,\varphi_1,\Gamma' \vdash \varphi}
$$

## Dedução Natural

- Contraction

$$
\dfrac{\Gamma,\varphi',\varphi',\Gamma'\vdash\varphi}
      {\Gamma,\varphi',\Gamma' \vdash \varphi}
$$

## Dedução Natural

- O uso de regras estruturais é necessário por considerarmos
contextos como listas de fórmulas.

- Ao se considerar contextos como conjuntos de fórmulas
não é necessário considerar essas regras.

# Eliminação de Corte

## Eliminação de Corte 

- Um conceito muito importante na lógica é o de _corte_.

- Intuitivamente, o corte permite o uso de resultados
auxiliares (lemas) em provas.

## Eliminação de Corte 

- Para ilustrar o conceito de corte e sua estrutura computacional
vamos considerar um exemplo simples.

## Eliminação de Corte 

- Teorema: todo número $n\in\mathbb{N}$ par, existe $m$ tal que $n = m + m$.

    - Caso base ($n = 0$). Basta considerar que $m = 0$, pois $0 = 0 + 0$.

## Eliminação de Corte 

- Teorema: todo número $n\in\mathbb{N}$ par, existe $m$ tal que $n = m + m$.

    - Passo indutivo ($n = n' + 2$). Suponha $n' \in\mathbb{N}$ um número 
      par arbitrário tal que $n' = m' + m'$. Seja $m = m' + 1$. Temos:
     
$$
n = n' + 2 = (m' + m') + 2 = (m' + 1) + (m' + 1).
$$

## Eliminação de Corte 

- Dado o teorema anterior e o fato de que $4$ é par, podemos deduzir
qual é a "metade" de 4.

- É possível calcular o valor de $m$ a partir dos fatos de que 
$4$ é par e do teorema anterior.

## Eliminação de Corte

- O teorema nos diz que se $n$ é par...
   - Existe $n'$ par tal que $n = n' + 2$.

## Eliminação de Corte

- O teorema nos diz que se $n$ é par...
   - Existe $n'$ par tal que $n = n' + 2$.
   - Se $n'$ é par então $n' = m' + m'$ 

## Eliminação de Corte

- O teorema nos diz que se $n$ é par...
   - Existe $n'$ par tal que $n = n' + 2$.
   - Se $n'$ é par então $n' = m' + m'$ 
   - Portanto, $n = m + m$ e $m = m' + 1$.

## Eliminação de Corte 

- Se $4$ é par...
   - Existe $n'$ par tal que $4 = n' + 2$.

## Eliminação de Corte 

- Se $4$ é par...
   - Existe $n'$ par tal que $4 = n' + 2$.
   - Logo $n' = 2$.

## Eliminação de Corte 

- Recursivamente: Se $2$ é par ...
   - Existe $n'$ par tal que $2 = n' + 2$.
   - Logo $n' = 0$
   
- Caso base: $0$ é par e $m = 0$

## Eliminação de Corte 

- Recursivamente: Se $2$ é par ...
   - Existe $n'$ par tal que $2 = n' + 2$.
   - Logo $n' = 0$ e $m' = 0$
- Logo, $m = m' + 1 = 1$.

## Eliminação de Corte 

- Como, $4$ é par ...
   - Existe $n'$ par tal que $4 = n' + 2$.
   - Logo $n' = 2$ e $m' = 1$.
- Temos que $m = m' + 1 = 2$.

## Eliminação de Corte 

- Logo, como $4$ é par, pelo teorema anterior 
conseguimos calcular que $4 = 2 + 2$, ou seja
que $2$ é a metade de $4$.

## Eliminação de Corte

- Formalmente, a eliminação do corte consiste 
em remover redundâncias em provas. 

- Redundância $\Rightarrow$ uso de uma regra de introdução 
seguido de uma eliminação para um mesmo conectivo.

## Eliminação de Corte

- Exemplo de redundância

$$
\begin{array}{ccc}
    \dfrac{\dfrac{
          \dfrac{\pi}{\Gamma\vdash A}\:\:\:\:
          \dfrac{\pi'}{\Gamma\vdash B}
       }{\Gamma\vdash A \land B}}
      {\Gamma\vdash A} 
\end{array}
$$


## Eliminação de Corte

- Exemplo de redundância

$$
\begin{array}{ccc}
    \dfrac{\dfrac{
          \dfrac{\pi}{\Gamma\vdash A}\:\:\:\:
          \dfrac{\pi'}{\Gamma\vdash B}
       }{\Gamma\vdash A \land B}}
      {\Gamma\vdash A} & \leadsto &
\end{array}
$$

## Eliminação de Corte

- Exemplo de redundância

$$
\begin{array}{ccc}
    \dfrac{\dfrac{
          \dfrac{\pi}{\Gamma\vdash A}\:\:\:\:
          \dfrac{\pi'}{\Gamma\vdash B}
       }{\Gamma\vdash A \land B}}
      {\Gamma\vdash A} & \leadsto &
    \dfrac{\pi}
          {\Gamma\vdash A}
\end{array}
$$

## Eliminação de Corte

- Mas, porque utilizar essa estrutura em provas?

## Eliminação de Corte

- Mas, porque utilizar essa estrutura em provas?

- Simples: modularização!

## Eliminação de Corte

- A remoção de cortes é uma propriedade crucial 
da lógica pois ela implica a sua _consistência_.

## Eliminação de Corte

- Consistência: Não é possível deduzir $\bot$ a 
partir de um conjunto vazio de hipóteses.

- Isto é, $\vdash \bot$ não é demonstrável.

## Eliminação de Corte

- Qual a importância desse fato? 

## Eliminação de Corte

- Qual a importância desse fato? 

- Consistência implica que a lógica é **útil**. 

## Eliminação de Corte

- Consistência implica que a lógica é **útil**. 

- Isso ocorre devido a regra: 

$$
\dfrac{\Gamma\vdash \bot}{\Gamma\vdash \varphi}
$$

## Eliminação de Corte

- Isso ocorre devido a regra: 

$$
\dfrac{\Gamma\vdash \bot}{\Gamma\vdash \varphi}
$$

- Se é possível demonstrar $\vdash \bot$ então 
toda fórmula $\varphi$ é demonstrável usando a
regra de eliminação de $\bot$. 

## Eliminação de Corte

- Formalmente, representamos o corte pela seguinte
propriedade possuída pela lógica.

$$
\dfrac{\Gamma \vdash \varphi'\:\:\:\:\Gamma',\varphi' \vdash \varphi}
      {\Gamma,\Gamma' \vdash \varphi}
$$

## Eliminação de Corte

- A remoção de cortes em provas consiste em substituir 
referências à hipótese $\varphi'$ em $\Gamma',\varphi'\vdash\varphi$
pela demonstração $\Gamma\vdash\varphi'$.


## Eliminação de Corte 

- Exemplo: $\{A \land B, A \to B \to C\} \vdash C$

$$
\dfrac{
   \dfrac{}{B \to C}\:\:\:\:
   \dfrac{}{B}
 }{C}
$$


## Eliminação de Corte 

- Exemplo: $\{A \land B, A \to B \to C\} \vdash C$

$$
\dfrac{
   \dfrac{\dfrac{}
                {A \to B \to C}\:\:\:\:
          \dfrac{
          }{A}
    }{B \to C}\:\:\:\:
   \dfrac{}
         {B}
 }{C}
$$


## Eliminação de Corte 

- Exemplo: $\{A \land B, A \to B \to C\} \vdash C$

$$
\dfrac{
   \dfrac{\dfrac{}
                {A \to B \to C}\:\:\:\:
          \dfrac{
             \dfrac{}{A \land B}
          }{A}
    }{B \to C}\:\:\:\:
   \dfrac{}
         {B}
 }{C}
$$



## Eliminação de Corte 

- Exemplo: $\{A \land B, A \to B \to C\} \vdash C$

$$
\dfrac{
   \dfrac{\dfrac{}
                {A \to B \to C}\:\:\:\:
          \dfrac{
             \dfrac{}{A \land B}
          }{A}
    }{B \to C}\:\:\:\:
   \dfrac{\dfrac{}{A\land B}}
         {B}
 }{C}
$$

## Eliminação de Corte 

- Exemplo $\{A, B\} \vdash A \land B$

$$
\dfrac{
   \dfrac{}{A}\:\:\:\:
   \dfrac{}{B}
}{A \land B}
$$

## Eliminação de Corte

- Exemplo:
   - Temos demonstração de $\{A \land B, A \to B \to C\} \vdash C$.
   - Temos demonstração de $\{A, B\}\vdash A \land B$
   
## Eliminação de Corte 

- Logo, é possível construir uma demonstração

$$
\{A,B,A \to B \to C\}\vdash C 
$$

substituindo a hipótese $A \land B$ pela demonstração 
de $A \land B$.

## Eliminação de Corte

- Construindo a demonstração $\{A,B,A \to B \to C\}\vdash C$.

- Demonstração original:

$$
\dfrac{
   \dfrac{\dfrac{}
                {A \to B \to C}\:\:\:\:
          \dfrac{
             \dfrac{}{A \land B}
          }{A}
    }{B \to C}\:\:\:\:
   \dfrac{\dfrac{}{A\land B}}
         {B}
 }{C}
$$

## Eliminação de Corte

- Substituindo a primeira hipótese $A \land B$ por sua demonstração.

$$
\dfrac{
   \dfrac{\dfrac{}
                {A \to B \to C}\:\:\:\:
          \dfrac{
             \dfrac{
                 \dfrac{}{A}\:\:\:\:
                 \dfrac{}{B}
             }{A \land B}
          }{A}
    }{B \to C}\:\:\:\:
   \dfrac{\dfrac{}{A\land B}}
         {B}
 }{C}
$$

## Eliminação de Corte

- Substituindo a segunda hipótese $A \land B$ por sua demonstração.

$$
\dfrac{
   \dfrac{\dfrac{}
                {A \to B \to C}\:\:\:\:
          \dfrac{
             \dfrac{
                 \dfrac{}{A}\:\:\:\:
                 \dfrac{}{B}
             }{A \land B}
          }{A}
    }{B \to C}\:\:\:\:
   \dfrac{\dfrac{
                 \dfrac{}{A}\:\:\:\:
                 \dfrac{}{B}   
          }{A\land B}}
         {B}
 }{C}
$$

## Eliminação de Corte

- Se $\varphi$ é demonstrável então existe uma demonstração 
sem cortes (redundância).
   - Obtemos a demonstração sem corte, eliminando-os.

## Eliminação de Corte

- Se $\vdash \varphi$ é uma dedução sem cortes, então 
essa dedução termina com uma regra de introdução.


## Eliminação de Corte

- Teorema: O sistema de dedução natural é consistente.

## Eliminação de Corte

- Demonstração: 
    1. Suponha que a dedução natural não seja consistente.

## Eliminação de Corte

- Demonstração: 
    1. Suponha que a dedução natural não seja consistente.
    2. Logo, existe uma dedução $\pi:\:\vdash \bot$.


## Eliminação de Corte

- Demonstração: 
    1. Suponha que a dedução natural não seja consistente.
    2. Logo, existe uma dedução $\pi:\: \vdash \bot$.
    3. Existe então uma dedução $\pi':\: \vdash\bot$ sem corte.

## Eliminação de Corte

- Demonstração: 
    1. Suponha que a dedução natural não seja consistente.
    2. Logo, existe uma dedução $\pi:\:\vdash \bot$.
    3. Existe então uma dedução $\pi':\:\vdash\bot$ sem corte.
    4. Assim, a dedução $\pi'$ deve terminar com uma regra de introdução.


## Eliminação de Corte

- Demonstração: 
    1. Suponha que a dedução natural não seja consistente.
    2. Logo, existe uma dedução $\pi:\:\vdash \bot$.
    3. Existe então uma dedução $\pi':\:\vdash\bot$ sem corte.
    4. Assim, a dedução $\pi'$ deve terminar com uma regra de introdução.
    5. Porém, não há regra de introdução para $\bot$. Contradição!
    
# Referências

## Referências

1. MIMRAM, Samuel. Program = Proof.

2. GIRARD, Jean Y. Proofs and Types.
