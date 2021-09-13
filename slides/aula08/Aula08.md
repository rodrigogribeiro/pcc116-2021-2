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
   (\Lambda \alpha. \lambda x : \alpha. x)\:\textrm{bool} & \longrightarrow \\
\end{array}
$$

## Introdução 

- Podemos obter a identidade para o tipo $\textrm{bool}$ da seguinte forma:

$$
\begin{array}{lc}
   (\Lambda \alpha. \lambda x : \alpha. x)\:\textrm{bool}  & \longrightarrow \\
   [\alpha \mapsto \textrm{bool}]\:(\lambda x : \alpha. x) & \longrightarrow \\
\end{array}
$$

## Introdução 

- Podemos obter a identidade para o tipo $\textrm{bool}$ da seguinte forma:

$$
\begin{array}{lc}
   (\Lambda \alpha. \lambda x : \alpha. x)\:\textrm{bool}  & \longrightarrow \\
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

- No repositório da disciplina, está disponível uma implementação Haskell do 
Sistema F.

<https://github.com/rodrigogribeiro/pcc116-2021-2/tree/master/code/system-f>

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

- Variáveis livres

$$
\begin{array}{lcl}
   fv(\emptyset) & = & \emptyset \\
   fv(\Gamma, \alpha) & = & fv (\Gamma) \cup \{\alpha\}\\
   fv(\Gamma, x : \sigma) & = & fv(\Gamma) \cup fv(\sigma)\\
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
   (\Lambda \alpha.e_1)\,[\sigma]    & \longrightarrow & [\alpha\mapsto \sigma]\,e_1\\
\end{array}
$$

## Sistema F

- Ao contrário do $\lambda$-cálculo tipado simples, contextos no sistema F
armazenam
    - tipos para termos da forma $x : \sigma$.
    - variáveis de tipos: $\alpha$.
    
## Sistema F

- Regras para variáveis (termos).

$$
\dfrac{x : \sigma \in \Gamma}
      {\Gamma \vdash x : \sigma}
$$

## Sistema F

- Regra para abstrações (termos).

$$
\dfrac{\Gamma, x : \sigma' \vdash e : \sigma}
      {\Gamma \vdash \lambda x : \sigma'.e : \sigma' \to \sigma}
$$

## Sistema F

- Regra para aplicações (termos).

$$
\dfrac{\Gamma\vdash e_1 : \sigma' \to \sigma\:\:\:\:
       \Gamma\vdash e_2 : \sigma'}
      {\Gamma\vdash e_1\:e_2 : \sigma}
$$

## Sistema F

- Regra para abstração (tipos).

$$
\dfrac{\Gamma,\alpha\vdash e : \sigma\:\:\:\:\alpha\not\in fv(\Gamma)}
      {\Gamma\vdash \Lambda \alpha. e : \forall \alpha.\sigma}
$$

## Sistema F

- Regra para aplicação (tipos).

$$
\dfrac{\Gamma\vdash e : \forall \alpha.\sigma}
      {\Gamma\vdash e\,[\sigma'] : [\alpha\mapsto \sigma']\,\sigma}
$$

## Sistema F 

- Exemplo de derivação.

$$
\dfrac{}{
\vdash (\Lambda \alpha. \lambda x : \alpha. x)[\textrm{bool}] : \textrm{bool}\to\textrm{bool}}
$$

## Sistema F 

- Exemplo de derivação.

$$
\dfrac{
   \dfrac{}{\vdash \Lambda \alpha. \lambda x : \alpha. x : \forall \alpha . \alpha \to \alpha}
}{\vdash (\Lambda \alpha. \lambda x : \alpha. x)[\textrm{bool}] : \textrm{bool}\to\textrm{bool}}
$$

## Sistema F 

- Exemplo de derivação.

$$
\dfrac{
   \dfrac{\dfrac{}{\alpha \vdash \lambda x : \alpha . x : \alpha \to \alpha}}
         {\vdash \Lambda \alpha. \lambda x : \alpha. x : \forall \alpha . \alpha \to \alpha}
}{\vdash (\Lambda \alpha. \lambda x : \alpha. x)[\textrm{bool}] : \textrm{bool}\to\textrm{bool}}
$$

## Sistema F 

- Exemplo de derivação.

$$
\dfrac{
   \dfrac{\dfrac{
              \dfrac{}{\alpha, x : \alpha \vdash x : \alpha}
          }{\alpha \vdash \lambda x : \alpha . x : \alpha \to \alpha}}
         {\vdash \Lambda \alpha. \lambda x : \alpha. x : \forall \alpha . \alpha \to \alpha}
}{\vdash (\Lambda \alpha. \lambda x : \alpha. x)[\textrm{bool}] : \textrm{bool}\to\textrm{bool}}
$$

# Church Encodings

## Church Encodings

- O sistema F é uma linguagem bastante expressiva e permite codificar diversos tipos
de dados e de funções sobre estes.

## Church Encodings

- Basicamente, a representação consiste em adicionar anotações de tipos à versão 
destes termos do $\lambda$-cálculo não tipado.

## Church Encodings

- Booleanos

$$
\begin{array}{l}
   \textrm{bool}  = \forall \alpha. \alpha \to \alpha \to \alpha\\
   \textrm{true}  = \Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x\\
   \textrm{false} = \Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . y\\
\end{array}
$$

## Church Encodings

- Demonstrando que $\vdash true : bool$

$$
  \dfrac{}{\textrm{true} : \textrm{bool}}
$$

## Church Encodings

- Demonstrando que $\vdash true : bool$
   - $\textrm{true}  = \Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x$

$$
  \dfrac{}{\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x : \textrm{bool}}
$$

## Church Encodings

- Demonstrando que $\vdash true : bool$
   - $\textrm{true}  = \Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x$
   - $\textrm{bool}  = \forall \alpha. \alpha \to \alpha \to \alpha\\$

$$
  \dfrac{}{\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x : \forall \alpha. \alpha \to \alpha \to \alpha}
$$

## Church Encodings

- Demonstrando que $\vdash true : bool$
$$
  \dfrac{
    \dfrac{
    }{\alpha \vdash \lambda x : \alpha. \lambda y : \alpha . x :\alpha \to \alpha \to \alpha}}
{\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x : \forall \alpha. \alpha \to \alpha \to \alpha}
$$



## Church Encodings

- Demonstrando que $\vdash true : bool$
$$
  \dfrac{
    \dfrac{
       \dfrac{}{\alpha, x : \alpha \vdash \lambda y : \alpha . x : \alpha \to \alpha}
    }{\alpha \vdash \lambda x : \alpha. \lambda y : \alpha . x :\alpha \to \alpha \to \alpha}}
{\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x : \forall \alpha. \alpha \to \alpha \to \alpha}
$$

## Church Encodings

- Demonstrando que $\vdash true : bool$
$$
  \dfrac{
    \dfrac{
       \dfrac{
         \dfrac{}{\alpha, x : \alpha, y : \alpha \vdash x : \alpha}
       }{\alpha, x : \alpha \vdash \lambda y : \alpha . x : \alpha \to \alpha}
    }{\alpha \vdash \lambda x : \alpha. \lambda y : \alpha . x :\alpha \to \alpha \to \alpha}}
{\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x : \forall \alpha. \alpha \to \alpha \to \alpha}
$$

## Church Encodings

- Demonstrando que $\vdash true : bool$
$$
  \dfrac{
    \dfrac{
       \dfrac{
         \dfrac{x : \alpha \in \{\alpha, x : \alpha, y : \alpha\}}
               {\alpha, x : \alpha, y : \alpha \vdash x : \alpha}
       }{\alpha, x : \alpha \vdash \lambda y : \alpha . x : \alpha \to \alpha}
    }{\alpha \vdash \lambda x : \alpha. \lambda y : \alpha . x :\alpha \to \alpha \to \alpha}}
{\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x : \forall \alpha. \alpha \to \alpha \to \alpha}
$$

## Church Encodings

- Números naturais usando a notação de Peano.

$$
\begin{array}{l}
\textrm{nat} = \forall \alpha. (\alpha \to \alpha) \to \alpha \to \alpha \\
\textrm{zero} = \Lambda \alpha. \lambda s : \alpha \to \alpha. \lambda z : \alpha. z\\
\textrm{succ} = \Lambda \alpha. \lambda s : \alpha \to \alpha. \lambda z : \alpha. s\:z\\
\end{array}
$$ 

## Church Encodings

- Listas

$$
\begin{array}{lcl}
   \textrm{list}\:\alpha & = & \forall\,\beta.(\alpha\to\beta\to\beta)\to\beta\to\beta\\
   \textrm{nil} & = & \Lambda \alpha. \Lambda\,\beta.\lambda c : \alpha \to \beta\to \beta.\lambda n : \beta. n\\
   \textrm{cons} & = & \Lambda \alpha.\lambda h : \alpha. \lambda tl : \textrm{list }\alpha.\\
                 &   & \Lambda \beta.\lambda c : \alpha\to\beta\to\beta. \lambda n : \beta. c\,h\,(tl\,[\beta]\,c\,n)\\
\end{array}
$$

## Church Encodings

- Além de tipos de dados, podemos utilizar o sistema F para representar conectivos da lógica.

## Church Encodings

- Representando a conjunção $A \land B$.

$$
\forall \alpha. (A \to B \to \alpha) \to \alpha
$$

## Church Encodings 

- Representando a negação $\neg A$

$$
\forall \alpha.A \to \alpha
$$

## Church Encodings

- Representando a constante $\top$:

$$ 
\forall \alpha. \alpha\to \alpha
$$

## Church Encodings

- Antes de generalizarmos o processo de representação de termos quaisquer 
utilizando o sistema F, vamos considerar a estrutura de formas normais 
deste cálculo.

# Formas Normais

## Formas Normais 

- Intuitivamente, um termo do sistema F é uma forma normal se não
possui sub-expressões:
    - $(\Lambda \alpha.e)[\beta]$
    - $(\lambda x : \sigma.e)\,e'$

## Formas Normais

- Formas normais do sistema F
    - $\Lambda a_i$: abstrações de tipos ou termos.
    - $Q_j$: um termo em forma normal ou um tipo.
    
$$
\Lambda a_1. ... \Lambda a_n. z Q_1 ... Q_k
$$

## Formas Normais

- Sistema F não possui formas normais únicas.

- Exemplos

$$
\begin{array}{l}
\Lambda \alpha.\Lambda \beta. \lambda x : \alpha \to \beta . x\\
\Lambda \alpha.\Lambda \beta. \lambda x : \alpha \to \beta . \lambda y : \alpha. x\,y\\
\end{array}
$$

## Formas Normais

- Os termos anteriores são $\eta$-equivalentes.

$$
\begin{array}{l}
e \equiv_{\eta} \lambda x. e\\
x \not\in\textrm{fv}(e)
\end{array}
$$

## Formas Normais

- Para considerar formas normais únicas, temos que adaptar a definição
para levar em conta a $\eta$ equivalência.

## Formas Normais

- Um termo é uma forma normal longa, se:
    - Se é uma forma normal.
    - O termo $z Q_1 ... Q_n$ possui um tipo atômico.
    - Cada $Q_j$, se termo, está em forma normal longa.
    
## Formas Normais

- Propriedade: Todo termo do Sistema F possui uma única forma normal longa.

## Formas Normais

- Formas normais longas são importantes porque muito de sua estrutura 
deriva diretamente de seu tipo.

## Formas Normais

- Se o tipo da forma normal for atômico, então esta deve ser:

$$
z Q_1 ... Q_n
$$

## Formas Normais

- Se o tipo da forma normal for $\sigma\to\sigma'$, então esta deve ser:

$$
\lambda x : \sigma . e
$$

## Formas Normais

- Se o tipo da forma normal for $\forall \alpha.\sigma$, então esta deve ser:

$$
\Lambda \alpha. e
$$

## Formas Normais

- Exemplo: Considere o tipo: 

$$
\sigma_1 \to \sigma_2 \to \forall \alpha_3. \sigma_4 \to \forall \alpha_5. \beta
$$

## Formas Normais

- Esse tipo possui 5 "prefixos".

$$
\sigma_1 \to \sigma_2 \to \forall \alpha_3. \sigma_4 \to \forall \alpha_5. \beta
$$


## Formas Normais 

- Uma forma normal para o tipo anterior deve ser:

$$
\lambda x : \sigma_1. \lambda y: \sigma_2. \Lambda \alpha_3. \lambda z:\sigma_4.\Lambda \alpha_5 ...
$$

## Formas Normais

- Este termo também possui 5 prefixos, correspondentes aos prefixos em seu tipo.

$$
\lambda x : \sigma_1. \lambda y: \sigma_2. \Lambda \alpha_3. \lambda z:\sigma_4.\Lambda \alpha_5 ...
$$

## Formas Normais

- Logo, o problema de construir uma forma normal longa pra um termo consiste em determinar
a primeira variável em

$$
z Q_1 ... Q_k
$$

- E, em seguida, preencher cada um dos $Q_j$ recursivamente.

## Formas Normais

- Exemplo: toda forma normal longa do tipo $\textrm{bool}$ é equivalente
aos termos $\textrm{true}$ e $\textrm{false}$.

$$
\begin{array}{l}
   \textrm{bool}  = \forall \alpha. \alpha \to \alpha \to \alpha\\
   \textrm{true}  = \Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . x\\
   \textrm{false} = \Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha . y\\
\end{array}
$$


## Formas Normais

- Como $\textrm{bool}  = \forall \alpha. \alpha \to \alpha \to \alpha$, temos que suas 
formas normais longa devem possuir a forma:

$$
\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha. ...
$$


## Formas Normais

- Visto que o contexto atual é $\Gamma = \{\alpha, x : \alpha, y : \alpha\}$, temos dois 
possíveis termos:
    - que são exatamente as formas normais do tipo $\textrm{bool}$.

$$
\begin{array}{l}
\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha. x\\
\Lambda \alpha. \lambda x : \alpha. \lambda y : \alpha. y\\
\end{array}
$$

## Formas Normais

- Vamos considerar a tarefa de codificar um tipo de dados para árvores binárias como 
termos do sistema F.

```haskell
data Tree = Leaf Nat | Node Tree Tree
```

## Formas Normais

- Para traduzir o tipo anterior em um termo do sistema F, precisamos de uma variável.

## Formas Normais

- Além da variável, precisamos de tipos para representar os construtores do tipo `Tree`{.haskell}

## Formas Normais

- O construtor `Leaf Nat`{.haskell} pode ser representado pelo seguinte tipo:

$$
\textrm{nat} \to \alpha
$$


## Formas Normais

- O construtor `Node Tree Tree`{.haskell} pode ser representado por: 

$$
\alpha \to \alpha \to \alpha
$$

## Formas Normais

- Dessa forma, o tipo `Tree`{.haskell} pode ser representado por:

$$
\forall \alpha. (\textrm{nat}\to\alpha)\to (\alpha \to \alpha \to \alpha) \to \alpha
$$

## Formas Normais

- Usando o tipo para representar `Tree`{.haskell}, temos que as formas normais deste
devem iniciar com o seguinte prefixo.

$$
\Lambda \alpha. \lambda l : \textrm{nat}\to\alpha. \lambda n : \alpha\to\alpha\to\alpha. ...
$$

## Formas Normais

- Podemos inclusive representar a sintaxe do sistema F usando essa estratégia de codificação
de termos.

## Formas Normais

- Com isso, podemos codificar um interpretador de sistema F usando o sistema F.

- Consideração importante: todo termo bem tipado do sistema F termina a execução em tempo finito.

## Formas Normais

- Detalhes podem ser encontrados no artigo:

<http://web.cs.ucla.edu/~palsberg/paper/popl16-full.pdf>

# Referências

## Referências

- Selinger, Peter. Lecture Notes on the $\lambda$-calculus.

- Pierce, Benjamin. Types and Programming Languages. MIT Press. 2002.
