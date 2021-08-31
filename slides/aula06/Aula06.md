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

- Apresentar o isomorfismo de Curry-Howard entre o $\lambda$-cálculo tipado 
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
       {\Gamma \vdash \textrm{case}(e,x \mapsto e_1, y \mapsto e_2) : \tau}
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
$$
