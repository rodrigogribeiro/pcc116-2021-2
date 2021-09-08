---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Sistema F
---

# Objetivos

## Objetivos

- Apresentar o sistema F, sua sintaxe, semântica e sistema de tipos.

- Apresentar a relação do sistema F e a correspondência de Curry-Howard.

## Objetivos

- Apresentar como codificar tipos de dados utilizando o sistema F.

# Introdução

## Introdução

- O $\lambda$-cálculo polimórfico, sistema F, foi 
desenvolvido paralelamente pelo lógico Jean Yves Girard 
e pelo cientista da computação John Reynolds.

## Introdução

- Girard identificou o sistema F como sendo o equivalente à
lógica proposicional de segunda ordem, que permite a quantificação
sobre proposições.

## Introdução

- De maneira simples, o sistema F inclui o quantificador universal 
ao $\lambda$-cálculo tipado simples.

## Introdução

- A motivação de Reynolds para o sistema F foi o estudo de 
polimorfismo em linguagens de programação.

## Introdução

- Considere as seguintes funções "identidade":

$$
\begin{array}{l}
   \lambda x : \textrm{bool} . x \\
   \lambda x : \textrm{int} . x \\
\end{array}
$$

## Introdução

- Evidentemente, temos "repetição" de código nessas expressões.

- Como evitar essa repetição?

## Introdução

- Idealmente, podemos evitar esse problema parametrizando essas definições 
pelo tipo da variável presente na abstração.

## Introdução 

- Identidade polimórfica.

$$
\Lambda \alpha. \lambda x : \alpha. x
$$

## Introdução

## Introdução 

- Identidade polimórfica.

- Abstração sobre variáveis de tipo usando $\Lambda$.

$$
\Lambda \alpha. \lambda x : \alpha. x
$$

## Introdução

- Com isso, temos que o tipo da identidade passa a ser 

$$
\Lambda \alpha. \lambda x : \alpha. x\: : \forall \alpha. \alpha \to \alpha
$$

## Introdução

- Essa modificação introduz um novo tipo de função: que recebe um 
_tipo_ como argumento.

## Introdução 

- Podemos obter a identidade para o tipo $\textrm{bool}$ da seguinte forma:

$$
\begin{array}{lc}
   (\Lambda \alpha. \lambda x : \alpha. x)\:\textrm{bool} & \longrigharrow \\
\end{array}
$$

## Introdução 

- Podemos obter a identidade para o tipo $\textrm{bool}$ da seguinte forma:

$$
\begin{array}{lc}
   (\Lambda \alpha. \lambda x : \alpha. x)\:\textrm{bool}  & \longrigharrow \\
   [\alpha \mapsto \textrm{bool}]\:(\lambda x : \alpha. x) & \longrightarrow \\
\end{array}
$$

## Introdução 

- Podemos obter a identidade para o tipo $\textrm{bool}$ da seguinte forma:

$$
\begin{array}{lc}
   (\Lambda \alpha. \lambda x : \alpha. x)\:\textrm{bool}  & \longrigharrow \\
   [\alpha \mapsto \textrm{bool}]\:(\lambda x : \alpha. x) & \longrightarrow \\
   \lambda x : \textrm{bool}. x\\
\end{array}
$$

## Introdução

- Para diferenciar a aplicação de funções a termos e a tipos, vamos usar uma 
sintaxe especial para esta última.

$$
(\Lambda \alpha. \lambda x : \alpha. x)[\textrm{bool}]
$$

## Introdução

- Na próxima seção, vamos considerar a sintaxe, semântica e sistema de tipos para 
o sistema F.

# Sistema F

## Sistema F

- Sintaxe de tipos

$$
\begin{array}{lcl}
   \sigma & ::= & \alpha \:\mid\:\sigma\to\sigma\:\mid\:\forall \alpha.\sigma.
\end{array}
$$

## Sistema F

- Sintaxe de termos 

$$
\begin{array}{lcl}
   e & ::= & x\:\mid\:e\,e'\:\mid\:\lambda x : \sigma. e\:\mid\: e\,[\sigma]\:\mid\: \Lambda \alpha. e
\end{array}
$$

## Sistema F

- Antes de apresentar o sistema de tipos, vamos considerar uma 
função para cálculo de variáveis livres em tipos.

## Sistema F

- Variáveis livres 

$$
\begin{array}{lcl}
   fv(\alpha)                & = & \{\alpha\}\\
   fv(\sigma_1 \to \sigma_2) & = & fv(\sigma_1) \cup fv(\sigma_2)\\
   fv(\forall \alpha.\sigma) & = & fv(\sigma) - \{\alpha\}\\
\end{array}
$$

## Sistema F

- Avaliação possui duas formas básicas de redução.
    - Redução de termos.
$$
\begin{array}{lcl}
   (\lambda x : \sigma . e_1)\,e_2 & \longrightarrow & [x\mapsto e_2]\:e_1\\
\end{array}
$$

## Sistema F

- Avaliação possui duas formas básicas de redução.
    - Redução de abstração de tipos.
$$
\begin{array}{lcl}
   (\lambda x : \sigma . e_1)\,e_2 & \longrightarrow & [x\mapsto e_2]\:e_1\\
   (\Lambda \alpha.e_1)\,\sigma    & \longrightarrow & [\alpha\mapsto \sigma]\,e_1\\
\end{array}
$$

## Sistema F

