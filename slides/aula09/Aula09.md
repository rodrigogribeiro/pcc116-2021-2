---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lógica de Predicados
---

# Objetivos

## Objetivos

- Revisar a sintaxe e semântica da lógica de predicados.

## Objetivos

- Apresentar os sistemas de dedução natural e cálculo de sequentes
para a lógica de predicados.

# Introdução

## Introdução

- A lógica de predicados estende a lógica proposicional para descrever
propriedades sobre elementos de um conjunto.

## Introdução

- A lógica proposicional não é capaz de representar propriedades como
    - Todo elemento de um conjunto satisfaz $\varphi$.
    - Algum elemento de um conjunto satisfaz $\varphi$.
    
## Introdução

- Para isso, vamos revisar a sintaxe, semântica e os formalismos de 
dedução natural e cálculo de sequentes.

# Sintaxe

## Sintaxe

- A sintaxe da lógica é definida em termos de uma _assinatura_.

## Sintaxe

- Uma assinatura $\Sigma$ é um conjunto de símbolos funcionais e uma função
$a : \Sigma\to\mathbb{N}$ que associa a aridade de cada símbolo.

- Constantes são símbolos $f \in \Sigma$ tais que $a(f) = 0$.

## Sintaxe

- A sintaxe da lógica de predicados descreve dois tipos diferentes de entidades.
    - Termos: que representam elementos de uma assinatura.
    - Fórmulas: componentes lógicos.
    
## Sintaxe

- A sintaxe de termos utiliza ...
    - um conjunto contável $\mathcal{V}$ de variáveis.
    - uma assinatura $\Sigma$.

## Sintaxe

- O conjunto de termos sobre uma assinatura $\Sigma$:
    - $\mathcal{V}\subseteq \mathcal{T}_{\Sigma}$.
    - Se $f \in \mathcal{T}_{\Sigma}$, $a(f) = n$ e $t_1 ... t_n \in \mathcal{T}_{\Sigma}$
    então $f(t_1,...,t_n) \in \mathcal{T}_{\Sigma}$.
    
## Sintaxe

- Exemplo: Vamos considerar $\Sigma = \{f : 2, a : 0\}$. 

- São termos sobre $\Sigma$:
    - $a$
    - $f(a,a)$
    - $f(x,(f(x,a)))$

## Sintaxe 

- Para definirmos a sintaxe de fórmulas, vamos considerar um conjunto $\mathcal{P}$
de predicados (ou símbolos relacionais).

## Sintaxe

- Associamos a aridade de predicados usando uma função $a : \mathcal{P} \to \mathbb{N}$.
    - Se $p \in \mathcal{P}$ e $a(p) = 0$ então $p$ é uma variável proposicional.

## Sintaxe 

- Fórmulas da lógica de predicados são geradas pela seguinte gramática.
    - $P \in \mathcal{P}$, $a(P) = n$ e $t_1, ..., t_n \in \mathcal{T}_{\Sigma}$. 
    - $\circ \in \{\supset, \leftrightarrow,\land,\lor\}$
$$
\begin{array}{lcl}
  \varphi & ::= & P(t_1,...,t_n)\,|\,\varphi \circ \varphi\,|\,\neg\varphi\,|\,\bot\,|\,\top\,|\\
          &     & \exists x. \varphi \,|\, \forall x. \varphi 
\end{array}
$$

## Sintaxe

- Em uma fórmula $\forall x. \varphi$, dizemos que $x$ é ligada em $\varphi$. 
- O mesmo pode se dizer para $\exists x. \varphi$.

## Sintaxe

- Uma variável é dita ser livre em uma fórmula $\varphi$ se esta não possui 
um quantificador que a define.

- Uma fórmula é dita ser fechada se $fv(\varphi) = \emptyset$.

## Sintaxe

- Denotamos por $[x \mapsto t]\varphi$ a operação de substituição de uma 
variável $x$ por um termo $t$.

- Para evitar a captura de variáveis, supomos um renomeamento de variáveis ligadas.

## Sintaxe

- Exemplo: Considere a fórmula

$$
\varphi = (\exists y. x + x = y) \lor (\exists x. x = y)
$$

- e a substituição $[x \mapsto z + z]$.

## Sintaxe

- O resultado de $[x \mapsto z + z]\varphi$ é:

$$
[x \mapsto z + z]\varphi = (\exists y. (z + z) + (z + z) = y) \lor (\exists x. x = y)
$$

## Sintaxe

- A operação de substituição será utilizada tanto para a definição
da semântica quanto da dedução natural para lógica de predicados.

# Semântica

## Semântica

- A partir de uma assinatura $\Sigma$ e um conjunto de predicados
$\mathcal{P}$, o significado de uma fórmula $\varphi$ é definido
em termos de uma _estrutura_.

## Semântica

- Uma estrutura é uma tripla $(M,F,R)$ em que:
    - $M$ é um conjunto não vazio.
    - $F$ um conjunto de funções $[\![f]\!] : M^n \to M$ para cada $f \in\Sigma$.
    - $R$ um conjunto de relações $[\![P]\!]\subseteq M^n$ para cada predicado $P$.

## Semântica

- A partir de uma estrutura, podemos definir uma função de interpretação para 
o significado de termos e fórmulas.

## Semântica

- Primeiro, vamos definir a função $[\![t]\!]^k : M^k\to M$ semântica de termos, em
que:
    - $k \in \mathbb{N}$
    - $t$ é um termo contendo $\{x_1,...,x_k\}$ variáveis livres.

## Semântica

- A semântica de uma variável $x_i$ é dado por uma projeção da $i$-ésima posição
de $k$-uplas de $M^k$.

## Semântica

- Função de interpretação é dada por:

$$
\begin{array}{l}
[\![f(t_1,...,t_n)]\!]^k(m_1,...,m_k) = \\
[\![f]\!]([\![t_1]\!]^k(m_1,...,m_k),...,[\![t_n]\!]^k(m_1,...,m_k))
\end{array}
$$

## Semântica

- Usando a semântica de termos, podemos definir a semântica de fórmulas 
da lógica de predicados como um subconjunto de $M^k$

## Semântica

- Função de interpretação de fórmulas

$$
\begin{array}{lcl}
   [\![\bot]\!]^k & = & \emptyset \\
   [\![\top]\!]^k & = & M^k \\
   [\![\neg \varphi]\!]^k & = & M^k - [\![\varphi]\!]^k\\
\end{array}
$$

## Semântica

- Função de interpretação de fórmulas

$$
\begin{array}{lcl}
   [\![\varphi_1 \land \varphi_2]\!]^k & = & [\![\varphi_1]\!]^k \cap [\![\varphi_2]\!]^k\\
   [\![\varphi_1 \lor \varphi_2]\!]^k & = & [\![\varphi_1]\!]^k\cup [\![\varphi_2]\!]^k\\
   [\![\varphi_1 \supset \varphi_2]\!]^k & = & [\![\neg \varphi_1 \lor \varphi_2]\!]^k\\
\end{array}
$$

## Semântica

- Função de interpretação de fórmulas

$$
\scriptsize{[\![\forall x_{k + 1}.\varphi]\!]^k = \bigcap_{m\in M}\{(m_1,...,m_k)\,|\,(m_1,...,m_k,m)\in[\![\varphi]\!]^{k+1}\}}
$$

## Semântica

- Função de interpretação de fórmulas

$$
\scriptsize{[\![\exists x_{k + 1}.\varphi]\!]^k = \bigcup_{m\in M}\{(m_1,...,m_k)\,|\,(m_1,...,m_k,m)\in[\![\varphi]\!]^{k+1}\}}
$$

## Semântica

- Em especial, para fórmulas fechadas, temos que $[\![\varphi]\!]^0 \subseteq \{()\}$.

- Logo, temos dois possíveis valores para a interpretação:
    - $[\![\varphi]\!]^0 = \emptyset$
    - $[\![\varphi]\!]^0 = \{()\}$

## Semântica

- De posse da semântica da lógica de predicados, podemos estudar os 
formalismos de dedução natural e cálculo de sequentes.

# Dedução Natural

## Dedução Natural

- A dedução natural para lógica de predicados inclui regras 
para manipulação de quantificadores.

## Dedução Natural

- Regras para o quantificador universal.

$$
\begin{array}{cc}
   \dfrac{\Gamma \vdash \varphi\:\:\:\:x \not\in\textrm{fv}(\Gamma)}
         {\Gamma\vdash \forall x. \varphi} &
   \dfrac{\Gamma \vdash \forall x. \varphi}
         {\Gamma \vdash [x\mapsto t]\varphi}
\end{array}
$$

## Dedução Natural

- Regras para o quantificador existencial.

$$
\begin{array}{c}
   \dfrac{\Gamma \vdash [x\mapsto t]\varphi}
         {\Gamma \vdash \exists x.\varphi} \\
   \dfrac{\Gamma\vdash \exists x.\varphi_1\:\:\:
          \Gamma, [x\mapsto t]\varphi_1\vdash\varphi\:\:\:
          t\not\in\textrm{fv}(\Gamma)\cup\textrm{fv}(\varphi)}
         {\Gamma\vdash \varphi}
\end{array}
$$

## Dedução Natural

- Exemplo: $\vdash \forall x. \neg A \supset \neg \exists x. A$

$$
\dfrac{}
      {\forall x. \neg A \supset \neg \exists x. A}
$$

## Dedução Natural

- Exemplo: $\vdash \forall x. \neg A \supset \neg \exists x. A$

$$
\dfrac{
    \dfrac{
    }{\neg \exists x. A}}
{\forall x. \neg A \supset \neg \exists x. A}
$$

## Dedução Natural

- Exemplo: $\vdash \forall x. \neg A \supset \neg \exists x. A$

$$
\dfrac{
    \dfrac{
      \dfrac{}
            {\bot}
    }{\neg \exists x. A}}
{\forall x. \neg A \supset \neg \exists x. A}
$$

## Dedução Natural

- Exemplo: $\vdash \forall x. \neg A \supset \neg \exists x. A$

$$
\dfrac{
    \dfrac{
      \dfrac{\dfrac{}{\exists x. A}\:\:\:\:
             \dfrac{}{\bot}}
            {\bot}
    }{\neg \exists x. A}}
{\forall x. \neg A \supset \neg \exists x. A}
$$

## Dedução Natural

- Exemplo: $\vdash \forall x. \neg A \supset \neg \exists x. A$

$$
\dfrac{
    \dfrac{
      \dfrac{\dfrac{}{\exists x. A}\:\:\:\:
             \dfrac{
                \dfrac{}{\neg A}
                \:\:\:
                \dfrac{}{A}
             }{\bot}}
            {\bot}
    }{\neg \exists x. A}}
{\forall x. \neg A \supset \neg \exists x. A}
$$

## Dedução Natural

- Exemplo: $\vdash \forall x. \neg A \supset \neg \exists x. A$

$$
\dfrac{
    \dfrac{
      \dfrac{\dfrac{}{\exists x. A}\:\:\:\:
             \dfrac{
                \dfrac{
                  \dfrac{}{\forall x. \neg A}
                }{\neg A}
                \:\:\:
                \dfrac{}{A}
             }{\bot}}
            {\bot}
    }{\neg \exists x. A}}
{\forall x. \neg A \supset \neg \exists x. A}
$$

## Dedução Natural

- Com essas 4 regras, conseguimos deduzir quaisquer fatos
demonstráveis usando a lógica de predicados.

# Sequent Calculus

## Sequent Calculus

- Assim como a dedução natural, o cálculo de sequentes para 
a lógica de predicados apenas inclui regras para lidar com 
os quantificadores.

## Sequent Calculus

- Regras para o quantificador universal

$$
\begin{array}{cc}
  \dfrac{\Gamma \Rightarrow \varphi\:\:\:x \not\in \textrm{fv}(\Gamma)}
        {\Gamma\Rightarrow \forall x. \varphi} &
  \dfrac{\Gamma, \forall x.\varphi_1, [x\mapsto t]\varphi_1\Rightarrow \varphi}
        {\Gamma,\forall x.\varphi_1 \Rightarrow \varphi}
\end{array}
$$

## Sequent Calculus

- Regras para o quantificador existencial

$$
\begin{array}{c}
   \dfrac{\Gamma \Rightarrow [x\mapsto t]\varphi}
         {\Gamma\Rightarrow \exists x.\varphi} \\ \\
   \dfrac{\Gamma, [x\mapsto t]\varphi\Rightarrow \varphi_1\:\:\:x\not\in\textrm{fv}(\Gamma)}
         {\Gamma,\exists x.\varphi \Rightarrow \varphi_1}
\end{array}
$$

## Sequent Calculus

- Isso conclui a nossa revisão da lógica de predicados.

# Referências

## Referências

- Girard, Jean Yves. Proofs and Types.

- Mimram, Samuel. Program = Proof.
