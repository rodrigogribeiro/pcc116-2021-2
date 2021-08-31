---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: $\lambda$-cálculo tipado simples
---

# Objetivos

## Objetivos

- Apresentar o sistema de tipos para o $\lambda$-cálculo tipado simples.

## Objetivos

- Discutir a implementação de um algoritmo para verificação / inferência 
de tipos.

## Objetivos

- Apresentar a correspondência de Curry-Howard entre o $\lambda$-cálculo tipado 
simples e a lógica proposicional.

## Objetivos 

- Apresentar o conceito de normalização forte.

# Motivação

## Motivação

- O $\lambda$-cálculo foi criado por Alonzo Church na década de 30
como um sistema formal para os fundamentos da matemática.

## Motivação

- A intuição de Church para o $\lambda$-cálculo foi usar termos
para representar fatos da teoria de conjuntos.

## Motivação

- Exemplo

$$
\begin{array}{c|c}
  \textrm{teoria de conjuntos} & \lambda-\textrm{cálculo}\\ \hline
  e\in s                       & e\:s\\
  \{x\,\mid\,e\}               & \lambda x. e\\
\end{array}
$$

## Motivação

- Logo, o conhecido paradoxo de Russell 

$$
R = \{x \,|\, x \not \in x\}
$$

é representado pelo seguinte termo:

$$
R = \lambda x. \neg (x\,x)
$$

## Motivação

- O conjunto proposto por Russell possui a propriedade de que 
$R \in R$ se, e somente se $R \not\in R$, isto é:

$$
R \:R = \neg (R\,R)
$$

## Motivação

- Ponto fixo: $x$ é ponto fixo de $f$ se $f(x) = x$.

## Motivação

- Isso denota que $R\:R$ é um ponto fixo para $\neg$:

$$
R \:R = \neg (R\,R)
$$


## Motivação

- Generalizando $\neg$ para um $f$ qualquer, temos:

$$
\lambda f. R\,R
$$

## Motivação 

- Substituindo $R = \lambda x. f (x\,x)$, temos: 

$$
\lambda f. (\lambda x. f (x\,x))\:(\lambda x. f (x\,x))
$$

## Motivação 

- Com isso, temos que o paradoxo de Russell é representado 
pelo termo:

$$
\lambda f. (\lambda x. f (x\,x))\:(\lambda x. f (x\,x))
$$

- que consiste de um operador de ponto fixo para um 
$\lambda$-termo qualquer.

## Motivação

- A partir deste termo paradoxal, a solução de Church foi 
adicionar um sistema de classificação de termos similar ao 
proposto por Russell para a teoria de conjuntos.

## Motivação

- A adoção de tipos em linguagens de programação tem motivações
similares: evitar comportamentos anômalos classificando trechos
de programas de acordo com os valores que estes computam.


# Sistema de tipos

## Sistema de tipos

- Vamos considerar a variante do $\lambda$-cálculo conhecida
como tipado simples.

## Sistema de tipos

- Sintaxe de tipos.

$$
\begin{array}{lcll}
   \tau & \to  & X             & \textrm{variáveis}\\
        & \mid & \tau \to \tau & \textrm{tipos funcionais}\\
\end{array}
$$

## Sistema de tipos

- Modificando a sintaxe de termos.
    - Inicialmente, vamos considerar a definição seguindo Church.
    
$$
\begin{array}{lcl}
e & \to  & x \\
  & \mid & \lambda x : \tau . e \\
  & \mid & e\:e\\
\end{array}
$$


## Sistema de tipos

- Contextos: usados para armazenar informações sobre os tipos de variáveis.

- Consideraremos contextos como listas e não conjuntos.

$$
\Gamma = \{x_1 : \tau_1, ... , x_n : \tau_n\}
$$

## Sistema de tipos

- Representando $x : \tau \in \Gamma$

$$
\begin{array}{cc}
  \dfrac{}{x : \tau \in \Gamma, x : \tau} & 
  \dfrac{x : \tau \in \Gamma\:\:\:\: x\neq y}{x : \tau \in \Gamma, y : \tau'}
\end{array}
$$

## Sistema de tipos

- Exemplo $x : A \in \{y : B, x : A\}$.

$$
\dfrac{}
      {x : A \in \{y : B, x : A\}}
$$

## Sistema de tipos

- Exemplo $x : A \in \{y : B, x : A\}$.

$$
\dfrac{
   \dfrac{}{x : A \in \{x : A\}}\:\:\:\:
   x\neq y
}{x : A \in \{y : B, x : A\}}
$$


## Sistema de tipos

- O sistema de tipos é uma relação entre contextos, $\lambda$-termos e 
tipos.

- Representamos as triplas $(\Gamma, e, \tau)$ como $\Gamma\vdash e : \tau$.


## Sistema de tipos 

- Regra para variáveis.

$$
\dfrac{x : \tau \in \Gamma}
      {\Gamma \vdash x : \tau}
$$

## Sistema de tipos 

- Regra para abstrações.

$$
\dfrac{\Gamma, x : \tau \vdash e : \tau'}
      {\Gamma \vdash \lambda x : \tau . e : \tau \to \tau'}
$$

## Sistema de tipos 

- Regra para aplicações.

$$
\dfrac{\Gamma\vdash e : \tau' \to \tau \:\:\:\:
       \Gamma\vdash e' : \tau'}
      {\Gamma\vdash e\:e' : \tau}
$$

## Sistema de tipos

- Exemplo: $\tau = A \to A$ e $\tau' = A$.

## Sistema de tipos

- Ex.: $\vdash \lambda f : \tau. \lambda x : \tau'. f (f\:x) : \tau \to \tau' \to \tau'$

$$
\dfrac{}
      {\vdash \lambda f : \tau. \lambda x : \tau'. f (f\:x) : \tau \to \tau' \to \tau'}
$$


## Sistema de tipos

- $\Gamma_1 =\{f : \tau\}$.

$$
\dfrac{\Gamma_1 \vdash \lambda x : \tau. f (f\:x) : \tau' \to \tau'}
      {\vdash \lambda f : \tau. \lambda x : \tau'. f (f\:x) : \tau \to \tau' \to \tau'}
$$

## Sistema de tipos

- $\Gamma_2 =\{f : \tau, x : \tau'\}$.

$$
\dfrac{
    \dfrac{\Gamma_2 \vdash f(f\:x) : \tau'}
          {\Gamma_1 \vdash \lambda x : \tau. f (f\:x) : \tau' \to \tau'}
}{\vdash \lambda f : \tau. \lambda x : \tau'. f (f\:x) : \tau \to \tau' \to \tau'}
$$

## Sistema de tipos

- $\Gamma_2 =\{f : \tau, x : \tau'\}$.

$$
\dfrac{
    \dfrac{
      \dfrac{
         \dfrac{}{\Gamma_2 \vdash f : \tau  \to \tau'}\:\:\:\:
         \dfrac{}{\Gamma_2 \vdash f\:x : A}
      }{\Gamma_2 \vdash f(f\:x) : \tau'}
    }{\Gamma_1 \vdash \lambda x : \tau. f (f\:x) : \tau' \to \tau'}
}{\vdash \lambda f : \tau. \lambda x : \tau'. f (f\:x) : \tau \to \tau' \to \tau'}
$$


## Sistema de tipos

- $\Gamma_2 =\{f : A \to A, x : A\}$.

$$
\dfrac{
    \dfrac{
      \dfrac{
         \dfrac{f : A \to A \in \Gamma_2}{\Gamma_2 \vdash f : A \to A}\:\:\:\:
         \dfrac{
            \dfrac{f : \tau \in \Gamma_2}{\Gamma_2 \vdash f : A  \to A} \:\:\:\:
            \dfrac{x : A \in \Gamma_2}{\Gamma_2 \vdash x : A}
         }{\Gamma_2 \vdash f\:x : A}
      }{\Gamma_2 \vdash f(f\:x) : A}
    }{\Gamma_1 \vdash \lambda x : \tau. f (f\:x) : A \to A}
}{\vdash \lambda f : \tau. \lambda x : \tau'. f (f\:x) : \tau \to A \to A}
$$

## Sistema de tipos

- Existem dois problemas básicos envolvendo sistemas de tipos: 

1. Verificação de tipos

2. Inferência de tipos 

## Sistema de tipos

- O problema de verificação consiste em: dados $\Gamma, e$ e $\tau$ determinar se
$\Gamma \vdash e : \tau$

## Sistema de tipos 

- O problema de inferência consiste em: dados $\Gamma$ e $e$ determinar um tipo 
$\tau$ de forma que $\Gamma \vdash e : \tau$.

## Sistema de tipos

- Vamos considerar uma implementação simples destes problemas
usando a linguagem Haskell.

# Inferência de tipos

## Inferência de tipos

- Vamos considerar uma implementação de um algoritmo para inferência 
de tipos para o $\lambda$-cálculo tipado simples.

## Inferência de tipos

- A verificação de tipos pode ser vista como um caso particular da 
inferência. 

- Logo, vamos implementar a inferência e usá-la para a verificação.

## Inferência de tipos

- Sintaxe de tipos

```haskell
type Name = String

data Ty
  = TVar Name
  | Ty :-> Ty
```

## Inferência de tipos

- Contextos são finite maps entre nomes e tipos.

```haskell
type Gamma = Map Name Ty
```

## Inferência de tipos

- Sintaxe de termos

```haskell
data Term
  = Var Name
  | Lam Name Ty Term
  | Term :@: Term
```

## Inferência de tipos

- Explicando erros durante a inferência.

```haskell
type Expected = Ty
type Found = Ty

data Error
  = UndefinedVar Name
  | CheckError Expected Found
  | ExpectedFunction Found
```

## Inferência de tipos

- Inferência de tipos: variáveis

```haskell
infer :: Gamma -> Term -> Either Error Ty
infer gamma (Var v)
  = case Map.lookup v gamma of
      Just ty -> Right ty
      Nothing -> Left (UndefinedVar v)
```

## Inferência de tipos

- Inferência de tipos: abstrações

```haskell
infer gamma (Lam n ty e)
  = case infer gamma' e of
      Left err  -> Left err
      Right ty' -> Right (ty :-> ty')
    where
      gamma' = Map.insert n ty gamma
```

## Inferência de tipos 

- Inferência de tipos: aplicação

```haskell
infer gamma (e :@: e')
  = case infer gamma e of
      Right (ty :-> ty') ->
        case infer gamma e' of
          Right ty1 ->
            if ty == ty1
            then Right ty'
            else Left (CheckError ty ty1)
      Right ty -> Left (ExpectedFunction ty)
      Left err -> Left err
```

## Inferência de tipos

- Representando a verificação usando inferência.

```haskell
check :: Gamma -> Term -> Ty -> Either Error ()
check gamma e ty
  = case infer gamma e of
      Right ty' ->
        if ty == ty' then Right ()
        else Left (CheckError ty ty')
      Left err -> Left err
```

## Inferência de tipos

- O algoritmo apresentado é **correto**, isto é,
se `infer gamma e = Right t`{.haskell} então existe um 
contexto $\Gamma$ equivalente a `gamma` tal que  
$\Gamma\vdash e : t$.

## Inferência de tipos

- Posteriormente veremos como demonstrar esta propriedade
de correção usando a linguagem Agda.

# Curry-Howard

## Curry-Howard

- Após estudarmos o sistema de tipos para o $\lambda$-cálculo,
vamos considerar sua relação com a lógica proposicional.

## Curry-Howard

- A relação entre estes dois formalismos foi descoberta de 
forma independente por Curry e Howard e, por isso, recebeu 
o nome de correspondência de Curry-Howard.

## Curry-Howard

- Em essência, a dedução natural para lógica proposicional
possui uma correspondência com o sistema de tipos para o 
$\lambda$-cálculo.

## Curry-Howard

- Nesta correspondência, temos que os tipos para o $\lambda$-cálculo
são equivalentes às proposições da lógica.
    - Substituindo tipos funcionais $\to$ pela implicação $\supset$.

## Curry-Howard

- Termos do $\lambda$-cálculo possuem a mesma estrutura de derivações
da dedução natural, isto é, eles correspondem a uma representação 
sintática de demonstrações da lógica.

## Curry-Howard

- Visualmente:

$$
\begin{array}{c|c}
   \textrm{Lógica} & \lambda\textrm{-cálculo}\\
   \\
   \dfrac{\tau \in \Gamma}
         {\Gamma \vdash \tau} & 
   \dfrac{x : \tau \in \Gamma}
         {\Gamma \vdash x : \tau} \\ 
\end{array}
$$


## Curry-Howard

- Visualmente:

$$
\begin{array}{c|c}
   \textrm{Lógica} & \lambda\textrm{-cálculo}\\
   \\
   \dfrac{\Gamma, \tau \vdash \tau'}
         {\Gamma \vdash \tau \supset \tau'} & 
   \dfrac{\Gamma, x : \tau \vdash e : \tau'}
         {\Gamma \vdash \lambda x : \tau. e : \tau \to \tau'} \\ 
\end{array}
$$

## Curry-Howard

- Visualmente:

$$
\begin{array}{c|c}
   \textrm{Lógica} & \lambda\textrm{-cálculo}\\
   \\
   \dfrac{\Gamma \vdash \tau' \supset \tau\:\:\:\:
          \Gamma \vdash \tau'}
         {\Gamma \vdash \tau} & 
   \dfrac{\Gamma \vdash e : \tau' \to \tau\:\:\:\:
          \Gamma \vdash e' : \tau'}
         {\Gamma \vdash e\:e' : \tau} \\ 
\end{array}
$$

## Curry-Howard 

- Seja $\Gamma \vdash \tau$ um sequente válido da lógica proposicional.
Então, existe um $\lambda$-termo $e$ tal que $\Gamma \vdash e : \tau$.

## Curry-Howard

- A correspondência apresentada envolveu apenas a implicação lógica.

- Porém, esta é válida pra os demais conectivos da lógica.

## Curry-Howard

- Conjunção: produto

$$
\begin{array}{cc}
   \dfrac{\Gamma \vdash \tau\:\:\:\:
          \Gamma \vdash \tau'}
         {\Gamma \vdash \tau \land \tau'} &
   \dfrac{\Gamma \vdash e : \tau\:\:\:\:
          \Gamma \vdash e' : \tau'}
         {\Gamma \vdash (e,e') : \tau \times \tau'}
\end{array}
$$

## Curry-Howard

- Conjunção: produto

$$
\begin{array}{cc}
   \dfrac{\Gamma \vdash \tau\land\tau'}
         {\Gamma \vdash \tau} &
   \dfrac{\Gamma \vdash e : \tau \times \tau'}
         {\Gamma \vdash \textrm{fst }e : \tau}
\end{array}
$$

## Curry-Howard

- Conjunção: produto

$$
\begin{array}{cc}
   \dfrac{\Gamma \vdash \tau\land\tau'}
         {\Gamma \vdash \tau'} &
   \dfrac{\Gamma \vdash e : \tau \times \tau'}
         {\Gamma \vdash \textrm{snd }e : \tau'}
\end{array}
$$

## Curry-Howard

- Disjunção: co-produto

$$
\begin{array}{cc}
   \dfrac{\Gamma\vdash \tau}
         {\Gamma\vdash \tau \lor \tau'} & 
   \dfrac{\Gamma\vdash e : \tau}
         {\Gamma\vdash \textrm{inl }e : \tau + \tau'} 
\end{array}
$$

## Curry-Howard

- Disjunção: co-produto

$$
\begin{array}{cc}
   \dfrac{\Gamma\vdash \tau'}
         {\Gamma\vdash \tau \lor \tau'} & 
   \dfrac{\Gamma\vdash e' : \tau'}
         {\Gamma\vdash \textrm{inr }e' : \tau + \tau'} 
\end{array}
$$

## Curry-Howard

- Disjunção: co-produto

$$
\begin{array}{c}
  \dfrac{\Gamma \vdash \tau_1 \lor \tau_2\:\:\:
         \Gamma, \tau_1 \vdash \tau \:\:\:
         \Gamma,\tau_2 \vdash \tau}{\Gamma \vdash \tau} \\ \\
  \dfrac{\Gamma \vdash e : \tau_1 \lor \tau_2\:\:\:
         \Gamma, x : \tau_1 \vdash e_1 : \tau \:\:\:
         \Gamma, y : \tau_2 \vdash e_2 : \tau}
       {\Gamma \vdash \textrm{case}(e,\lambda x : \tau_1. e_1, \lambda y : \tau_2. \mapsto e_2) : \tau}
\end{array}
$$

## Curry-Howard

- Verdadeiro: unit type

$$
\begin{array}{cc}
   \dfrac{}{\Gamma\vdash \top} & 
   \dfrac{}{\Gamma\vdash () : \top}\\
\end{array}
$$

## Curry-Howard

- Falso: bottom type

$$
\begin{array}{cc}
   \dfrac{\Gamma \vdash \bot}{\Gamma\vdash \tau} & 
   \dfrac{\Gamma \vdash e : \bot}{\Gamma\vdash\textrm{absurd}^{\tau}(e) : \tau}
\end{array}
$$

## Curry-Howard 

- Contextos devem ser considerados listas e não conjuntos.

- Para entender o motivo, considere o tipo:

$$
A \to A \to A
$$

## Curry-Howard

- Dois possíveis termos para esse tipo são:

$$
\begin{array}{c}
  \lambda x : A. \lambda y : A. x \\
  \lambda x : A. \lambda y : A. y \\
\end{array}
$$

## Curry-Howard 

- Derivação de $\lambda x : A. \lambda y : A. x$: 

$$
  \dfrac{}
        {\vdash \lambda x : A. \lambda y : A. x : A \to A \to A}
$$

## Curry-Howard 

- Derivação de $\lambda x : A. \lambda y : A. x$: 

$$
  \dfrac{
     \dfrac{}{\{x : A\} \vdash \lambda y : A. x : A \to A}
  }{\vdash \lambda x : A. \lambda y : A. x : A \to A \to A}
$$

## Curry-Howard 

- Derivação de $\lambda x : A. \lambda y : A. y$: 

$$
  \dfrac{
     \dfrac{
        \dfrac{}{\{x : A, y : A\} \vdash y : A}
     }{\{x : A\} \vdash \lambda y : A. x : A \to A}
  }{\vdash \lambda x : A. \lambda y : A. x : A \to A \to A}
$$

## Curry-Howard

- Do ponto de vista da dedução natural, os termos anteriores
corresponderiam à dedução:

$$
  \dfrac{
     \dfrac{
        \dfrac{}{\{A,A\} \vdash A}
     }{\{A\} \vdash A \to A}
  }{\vdash A \to A \to A}
$$

## Curry-Howard

- Se consideramos contextos como conjuntos, não há diferença entre
$\{A,A\}$ e $\{A\}$.
   - E os termos anteriores seriam considerados "iguais".

- Dessa forma, do ponto de vista computacional, só faz sentido pensar 
contextos como listas e não como contextos.


## Curry-Howard

- Até agora vimos uma relação entre deduções da lógica e derivações
de sistemas de tipos.

- Há uma relação entre deduções da lógica e execução de $\lambda$-termos?

## Curry-Howard

- Sim! Vermos que o processo de eliminação de corte corresponde exatamente 
à execução no $\lambda$-cálculo.

## Curry-Howard

- Para entender essa relação, vamos considerar uma propriedade do 
sistema de tipos do $\lambda$-cálculo.

- Essa propriedade é conhecida como Lema da Substituição.

## Curry-Howard

- **Lema da Substituição:** 

$$
\dfrac{\Gamma,x : \tau' \vdash e : \tau\:\:\:\:
       \Gamma \vdash e' : \tau'}
      {\Gamma \vdash [x \mapsto e']\,e : \tau}
$$

## Curry-Howard

- Eliminando os termos da lema da substituição...

$$
\dfrac{\Gamma,x : \tau' \vdash e : \tau\:\:\:\:
       \Gamma \vdash e' : \tau'}
      {\Gamma \vdash [x \mapsto e']\,e : \tau}
$$


## Curry-Howard

- ... obtemos a regra de corte!

$$
\dfrac{\Gamma,\tau' \vdash \tau\:\:\:\:
       \Gamma \vdash \tau'}
      {\Gamma \vdash \tau}
$$

## Curry-Howard 

- Se o corte corresponde à substituição 
no $\lambda$-cálculo...

- a eliminação de corte é equivalente à computação no 
$\lambda$-cálculo.

## Curry-Howard

- ... valores do $\lambda$-cálculo correspondem a 
deduções sem corte na dedução natural.

- Dessa forma, podemos pensar que a tarefa de 
verificar provas da lógica proposicional resume-se
à verificação/inferência de tipos.

## Curry-Howard

- Em aulas anteriores, vimos que toda demonstração
em dedução natural possui uma forma normal.
    - Isso é, uma dedução sem ocorrência de cortes.
    
## Curry-Howard

- Adicionalmente, temos que o processo de remoção
de corte termina em um número finito de passos.

## Curry-Howard

- Dada a corrêspondência de Curry-Howard, temos que 
existir um processo equivalente para redução de 
$\lambda$-termos em um número finito de passos.

## Curry-Howard

- Esse processo de normalização do $\lambda$-cálculo
é baseado em uma propriedade conhecida como 
**normalização forte.**

# Normalização

## Normalização

- Vamos apresentar, em alto nível, a demonstração do 
resultado de normalização forte.

- Essa demonstração foi originalmente realizada por Tait 
e posteriormente refinada por Girard.

## Normalização 

- **Normalização forte**: Toda sequência de computação é finita.

## Normalização 

- A demonstração é baseada no conceito de _reducibility candidates_.

- Reducibility candidates
    - Se $\Gamma \vdash e : \tau$ temos que $e \in R_{\tau}$.
    - Todo $e \in R_{\tau}$ possui normalização forte.
    
## Normalização

- Definimos o conjunto $R_{\tau}$ por indução sobre $\tau$:

## Normalização

- Se $\tau = A$ então $R_{A}$ é o conjunto de todos os termos
$e$ que possuem normalização forte.

## Normalização 

- Se $\tau = \tau_1\to\tau_2$ então $R_{\tau_1\to\tau_2}$ é o conjunto de 
termos $e$ tais que para todo $e' \in R_{\tau_1}$, temos que $e\:e' \in R_{\tau_2}$.

## Normalização

- Algumas propriedades de $R_{\tau}$:

- (P1). Se $e \in R_{\tau}$ então $e$ possui normalização forte.

- (P2). Se $e \in R_{\tau}$ e $e \to_{\beta} e'$ então $e' \in R_{\tau}$.

- (P3). Se $e$ é neutro, $e \to_{\beta} e'$ implica que $e' \in R_{\tau}$ então
$e\in R_{\tau}$.

## Normalização

- A propriedade P1 é uma consequência direta da definição de $R_{\tau}$.

## Normalização

- Propriedade P2: Suponha $e \in R_{\tau}$ e $e \to_{\beta} e'$. 
    - Como $e \in R_{\tau}$, existe uma sequência finita de reduções de $e$.

## Normalização

- Propriedade P2: Suponha $e \in R_{\tau}$ e $e \to_{\beta} e'$. 
    - Como $e \in R_{\tau}$, existe uma sequência finita de reduções de $e$.
    - Se $e$ possui uma sequência finita de reduções e $e \to_{\beta} e'$, 
      temos que $e'$ também o possui. 
      
## Normalização

- Propriedade P2: Suponha $e \in R_{\tau}$ e $e \to_{\beta} e'$. 
    - Como $e \in R_{\tau}$, existe uma sequência finita de reduções de $e$.
    - Se $e$ possui uma sequência finita de reduções e $e \to_{\beta} e'$, 
      temos que $e'$ também o possui. 
    - Se $e'$ possui uma sequência finita de reduções, temos que $e' \in R_{\tau}$.
    
## Normalização

- Propriedade P3: Demonstração similar à propriedade P2.

## Normalização 

- Lema: Seja $e$ um termo tal que para todo $e'\in R_{\tau_1}$, temos que 
$[x \mapsto e']\,e \in R_{\tau_2}$. Então $\lambda x : \tau_1. e \in R_{\tau_1\to\tau_2}$.

## Normalização

- Por P1 e a definição de $R_{\tau_1\to\tau_2}$,
temos que $e$ e $e'$ tem normalização forte.

## Normalização

- Para mostrar que $(\lambda x : \tau_1.e)\,e'$ tem normalização forte, temos
que considerar 3 casos.

## Normalização

1. $(\lambda x : \tau_1.e)\,e' \to_{\beta}[x \mapsto e']\,e$:

- Ok, visto que é uma hipótese.

## Normalização

2. $(\lambda x : \tau_1.e)\,e' \to_{\beta}(\lambda x : \tau_1.e_1)\,e'$, com $e\to_\beta e_1$.

- Pela H.I. temos que $(\lambda x : \tau_1 . e_1)\,e' \in R_{\tau_2}$.

- Como $e\to_\beta e_1$ e $(\lambda x : \tau_1 . e_1)\,e' \in R_{\tau_2}$, temos que 
$(\lambda x : \tau_1 . e)\,e' \in R_{\tau_2}$.

## Normalização 

3. $(\lambda x : \tau_1.e)\,e' \to_{\beta}(\lambda x : \tau_1.e)\,e_2$, com $e'\to_\beta e_2$.

- Pela H.I. temos que $(\lambda x : \tau_1 . e)\,e_2 \in R_{\tau_2}$.

- Como $e'\to_\beta e_2$ e $(\lambda x : \tau_1 . e)\,e_2 \in R_{\tau_2}$, temos que 
$(\lambda x : \tau_1 . e)\,e' \in R_{\tau_2}$.

## Normalização

- Lema: Seja $\Gamma = \{x_1 : \tau_1, ... , x_n : \tau_n\}$ e $t_i \in R_{\tau_i}$ para
$1 \leq i \leq n$. Se $\Gamma\vdash e : \tau$ então $[x_i\mapsto \tau_i]\,e \in R_{\tau}$.

- Demonstração: Indução sobre $\Gamma\vdash e : \tau$ usando o lema anterior.

## Normalização

- Corolário 1: Se $\Gamma \vdash e : \tau$ então $e \in R_{\tau}$.

- Corolário 2: Se $\Gamma \vdash e : \tau$ então $e$ possui normalização forte.

## Normalização

- Consequências: Termos que não reduzem em um número finito de passos não 
possuem tipos válidos.

- Ex. $(\lambda x. x x)\,(\lambda x. x x)$

## Normalização

- Existe um algoritmo para determinar se dois termos denotam a mesma função.

## Normalização

1. Sejam $\Gamma \vdash e_1 : \tau$ e $\Gamma \vdash e_2 : \tau$.

2. Logo, tanto $e_1$ e $e_2$ são tais que:
    - $e_1 \rightarrow^*_{\beta} v_1$
    - $e_2 \rightarrow^*_{\beta} v_2$
3. Retorne $v_1 \equiv_\alpha v_2$.

## Referências

- Pierce, Benjamin. Types and programming languages, MIT Press, 2002.

- Mimram, Samuel. Program = Proof.
