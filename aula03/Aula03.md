---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lógica proposicional
---

# Objetivos

## Objetivos

- Apresentar a visão intuicionista para a lógica proposicional.

- Apresentar o sistema de dedução natural para lógica proposicional.

## Objetivos

- Apresentar o cálculo de sequentes para a lógica proposicional.

- Apresentar o conceito de _corte_ e sua relação com computação.

## Objetivos

- Apresentar algoritmos para construção de provas da lógica proposicional.

# Introdução

## Introdução

- Um conceito central neste curso é o de _tipo_.

- Mas, o que é um tipo em uma linguagem de programaçãp?

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

- A demonstração de $A \to B$ consiste de um processo que produz uma
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
\dfrac{}{\Gamma, A, \Gamma' \vdash A}
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

- Exemplo: $\{A \land B \to C\} \vdash A \to B \to C$.


## Dedução Natural

- Exemplo: $\{A \land B \to C\} \vdash A \to B \to C$.

$$
\dfrac{}{A \to B \to C}
$$

## Dedução Natural

- Exemplo: $\{A \land B \to C\} \vdash A \to B \to C$.

$$
\dfrac{
   \dfrac{}
         {B \to C}
}{A \to B \to C}
$$

## Dedução Natural

- Exemplo: $\{A \land B \to C\} \vdash A \to B \to C$.

$$
\dfrac{
   \dfrac{
      \dfrac{
      }{C}
   }{B \to C}
}{A \to B \to C}
$$


## Dedução Natural

- Exemplo: $\{A \land B \to C\} \vdash A \to B \to C$.

$$
\dfrac{
   \dfrac{
      \dfrac{
         \dfrac{}
               {A \land B \to C}
         \,\,\,\,
         \dfrac{}
               {A \land B}
      }{C}
   }{B \to C}
}{A \to B \to C}
$$


## Dedução Natural

- Exemplo: $\{A \land B \to C\} \vdash A \to B \to C$.

$$
\dfrac{
   \dfrac{
      \dfrac{
         \dfrac{}
               {A \land B \to C}
         \,\,\,\,
         \dfrac{
            \dfrac{}{A} \,\,\,\,\dfrac{}{B}
         }{A \land B}
      }{C}
   }{B \to C}
}{A \to B \to C}
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

Exemplo: $\{A \to B\}\vdash \neg B \to \neg A$


## Dedução Natural

Exemplo: $\{A \to B\}\vdash \neg B \to \neg A$

$$
\dfrac{}
      {\neg B \to \neg A}
$$

## Dedução Natural

Exemplo: $\{A \to B\}\vdash \neg B \to \neg A$

$$
\dfrac{
  \dfrac{}{\neg A}
}{\neg B \to \neg A}
$$

## Dedução Natural

Exemplo: $\{A \to B\}\vdash \neg B \to \neg A$

$$
\dfrac{
  \dfrac{
     \dfrac{}{\bot}
  }{\neg A}
}{\neg B \to \neg A}
$$

## Dedução Natural

Exemplo: $\{A \to B\}\vdash \neg B \to \neg A$

$$
\dfrac{
  \dfrac{
     \dfrac{
        \dfrac{}{\neg B}\,\,\,\,
        \dfrac{}{B}
     }{\bot}
  }{\neg A}
}{\neg B \to \neg A}
$$

## Dedução Natural

Exemplo: $\{A \to B\}\vdash \neg B \to \neg A$

$$
\dfrac{
  \dfrac{
     \dfrac{
        \dfrac{}{\neg B}\,\,\,\,
        \dfrac{
          \dfrac{}{A \to B}\,\,\,\,
          \dfrac{}{A}
        }{B}
     }{\bot}
  }{\neg A}
}{\neg B \to \neg A}
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
\dfrac{\Gamma,\varphi_1,\varphi_2\Gamma'\vdash\varphi}
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

- Outra regra estrutural da dedução natural é a de _corte_.

- Intuitivamente, a regra de corte permite o uso de resultados
auxiliares em provas.

## Eliminação de Corte 

- Para ilustrar o conceito de corte e sua estrutura computacional
vamos considerar um exemplo simples.

## Eliminação de Corte 

- Teorema: todo número $n\in\mathbb{N}$ par, existe $m$ tal que $n = m + m$.

    - Caso base ($n = 0$). Basta considerar que $m = 0$, pois $0 = 0 + 0$.

## Eliminação de Corte 

- Teorema: todo número $n\in\mathbb{N}$ par, existe $m$ tal que $n = m + m$.

    - Passo indutivo ($n = n' + 2$). Suponha $n' \in\mathbb{N}$ um número par arbitrário
     tal que $n' = m' + m'$. Seja $m = m' + 1$. Temos:
$$
n = n' + 2 = (m' + m') + 2 = (m' + 1) + (m' + 1).
$$

## Eliminação de Corte 

- Regra de corte.

$$
\dfrac{\Gamma\vdash \varphi'\,\,\,\,\Gamma,\varphi',\Gamma'\vdash \varphi}
      {\Gamma,\Gamma' \vdash \varphi}
$$
