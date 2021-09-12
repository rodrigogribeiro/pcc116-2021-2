---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Sistema de Hindley-Milner.
---

# Objetivos

## Objetivos

- Apresentar o sistema de tipos de Hindley-Milner e seu algoritmo 
de inferência de tipos.

## Objetivos

- Discutir uma implementação deste algoritmo em Haskell.

# Motivação

## Motivação 

- Vimos em aulas anteriores... 
    - O $\lambda$-cálculo tipado simples possui uma correspondência com 
      a lógica proposicional.
      
## Motivação

- Mas e a lógica de primeira ordem?

- Como lidar com quantificadores?

## Motivação

- Antes de responder essas perguntas em um contexto geral, vamos
considerar o problema restrito de adicionar o quantificador universal 
ao $\lambda$-cálculo tipado simples.

## Motivação

- Se restringirmos a presença de quantificadores a "prefixos" dos tipos
do $\lambda$-cálculo, obtemos o núcleo de linguagens funcionais como ML 
e Haskell

## Motivação

- Nesta aula, focaremos no problema de inferência de tipos para o $\lambda$-cálculo
estendido com a construção $\texttrm{let}$.

# Sistema HM
    
## Sistema HM

- Linguagens modernas possuem polimorfismo paramétrico
para evitar repetição de código.

- Em essência, essas linguagens utilizam uma variação do sistema 
de tipos proposto por Hindley-Milner.

## Sistema HM

- Para o sistema HM, vamos considerar a seguinte sintaxe de tipos:

$$
\begin{array}{lcl}
   \overline{\alpha} & ::= & \alpha_1\,...\,\alpha_n\\
   \sigma & ::= & \tau \,|\,\forall\,\overline{\alpha}.\tau\\
   \tau   & ::= & \alpha \,|\, C\,|\, \tau \to \tau\\
\end{array}
$$

## Sistema HM

- Tipos denotados pela meta-variável $\sigma$ são conhecidos por 
_type schemes_.

- Type schemes correspondem a tipos possivelmente polimórficos.

## Sistema HM

- O que uma variável universalmente quantificada representa em 
$\sigma$?

## Sistema HM

- De maneira intuitiva, uma variável quantificada denota um tipo 
_qualquer_.

## Sistema HM

- De maneira intuitiva, uma variável quantificada denota um tipo 
_qualquer_.

- Logo, tipos polimórficos denotam um _conjunto_ de tipos.


## Sistema HM

- Formalmente

$$
[\![\sigma]\!] = \{[\overline{\alpha_i \mapsto \tau_i}]\,\tau\,|\,\sigma = \forall \overline{\alpha}.\tau\}
$$

## Sistema HM

- Exemplo: Considere o tipo polimórfico

$$
\sigma_1 = \forall \alpha_1\,\alpha_2. \alpha_1 \to \alpha_2 \to \alpha_1
$$

## Sistema HM

- Instâncias do tipo $\forall \alpha_1\,\alpha_2. \alpha_1 \to \alpha_2 \to \alpha_1$:

$$
\begin{array}{l|l}
   \forall \alpha_2. \textrm{int} \to \alpha_2 \to \textrm{int} & S=\{\alpha_1 \mapsto\textrm{int}\}\\
   \textrm{int} \to \textrm{bool} \to \textrm{int} & S=\{\alpha_1 \mapsto\textrm{int},\alpha_2\mapsto\textrm{bool}\}\\
\end{array}
$$

## Sistema HM

- Evidentemente, temos que o tipo

$$
\sigma_1 = \forall \alpha_1\,\alpha_2. \alpha_1 \to \alpha_2 \to \alpha_1
$$

- é mais "polimórfico" que 

$$
\forall \alpha_2. \textrm{int} \to \alpha_2 \to \textrm{int}
$$

## Sistema HM

- O tipo

$$
\forall \alpha_2. \textrm{int} \to \alpha_2 \to \textrm{int}
$$

- é obtido a partir de 

$$
\sigma_1 = \forall \alpha_1\,\alpha_2. \alpha_1 \to \alpha_2 \to \alpha_1
$$

- usando $[\alpha_1 \mapsto \textrm{int}]$.

## Sistema HM

- Formalmente, dizemos que $\sigma_1$ é mais geral que $\sigma_2$, $\sigma_1 \sqsubseteq \sigma_2$ 
se:

$$
[\![\sigma_1]\!] \subseteq [\![\sigma_2]\!]
$$

## Sistema HM

- A partir da definição de tipos, podemos especificar a sintaxe de termos.

## Sistema HM

- Sintaxe de termos

$$
\begin{array}{lcl}
   e & ::=  & x \,|\, \lambda x. e\,|\,e\,e\\
     & \mid & \textrm{let } x = e\textrm{ in } e\\
\end{array}
$$

## Sistema HM

- A sintaxe de termos possui um novo componente: 
termos $\textrm{let}$.

## Sistema HM

- Intuitivamente, a expressão 

$$
\textrm{let } x = e_1\textrm{ in } e_2
$$

- Define a variável $x$ como sendo a expressão $e_1$ e a 
torna visível no escopo de $e_2$.

## Sistema HM

- De um ponto de vista semântico, temos: 

$$
\textrm{let } x = e_1\textrm{ in } e_2 \equiv (\lambda x. e_2)\:e_1
$$

## Sistema HM

- Porém, no sistema de tipos, temos que expressões \textrm{let}
permitem a definição de termos polimórficos.

## Sistema HM

- O sistema será especificado utilizando sequentes da forma
$$
\Gamma \vdash e : \tau
$$

## Sistema HM

- Sistema HM: variáveis

$$
\dfrac{x : \sigma \in \Gamma\:\:\:\:\sigma \sqsubseteq \tau}
      {\Gamma \vdash x : \tau}
$$

## Sistema HM

- Sistema HM: aplicação

$$
\dfrac{\Gamma \vdash e : \tau' \to \tau\:\:\:\:
       \Gamma\vdash e' : \tau'}
      {\Gamma\vdash e\:e' : \tau}
$$

## Sistema HM

- Sistema HM: abstração

$$
\dfrac{\Gamma,x : \tau' \vdash e : \tau}
      {\Gamma \vdash \lambda x. e : \tau' \to \tau}
$$

## Sistema HM

- Sistema HM : let

$$
\dfrac{\Gamma \vdash e_1 : \tau_1\:\:\:\:
       \Gamma , x : \sigma_1 \vdash e_2 : \tau_2\:\:\:\:
       \sigma_1 = \textrm{gen}(\tau_1,\Gamma)}
      {\Gamma \vdash \textrm{let } x = e_1 \textrm{ in } e_2 : \tau_2}
$$

## Sistema HM

- Generalização

$$
\begin{array}{lcl}
gen(\tau,\Gamma) & = & \forall \overline{\alpha}.\tau\\
\overline{\alpha} & = & \textrm{fv}(\tau) - \textrm{fv}(\Gamma)\\
\end{array}
$$

## Sistema HM

- Exemplo:

$$
\dfrac{}{\vdash  \lambda x.\textrm{let }y = x\textrm{ in } y : ?}
$$


## Sistema HM

- Exemplo:

$$
\dfrac{x : X \vdash \textrm{let }y = x\textrm{ in } y : ?}
      {\vdash \lambda x.\textrm{let }y = x\textrm{ in } y : ?}
$$

## Sistema HM

- Exemplo:

$$
\dfrac{
    \dfrac{
       \dfrac{}{x : X \vdash x : X}\:\:\:\:
       \dfrac{\forall \alpha. \alpha \sqsubseteq Y}{x : X, y : \forall \alpha. \alpha \vdash y : Y}
    }{x : X \vdash \textrm{let }y = x\textrm{ in } y : Y}}
{\vdash \lambda x.\textrm{let }y = x\textrm{ in } y : X \to Y}
$$

## Sistema HM

- Agora que apresentamos o sistema HM, vamos considerar seu algoritmo de inferência.

# Inferência

## Inferência

- O sistema de tipos de Hindley-Milner consiste de uma extensão simples do 
$\lambda$-cálculo tipado simples.

## Inferência

- Porém, as regras apresentadas não consistituem diretamente um algoritmo.

- Existe não determinismo nas regras apresentadas.

## Inferência

- Não determinismo presente em determinar uma instância $\tau$ 
para um tipo $\sigma$.

$$
\dfrac{x : \sigma\in\Gamma\:\:\:\:\sigma\sqsubseteq\tau}
      {\Gamma \vdash x : \tau}
$$

## Inferência

- A solução proposta por Damas consiste em produzir uma instância
utilizando variáveis que não ocorrem no contexto $\Gamma$.

- Adicionalmente, o algoritmo calcula uma substituição que 
"preenche" as novas variáveis.

## Inferência

- Especificaremos o algoritmo de inferência utilizando um sequente da forma:

$$
\Gamma \vdash e : \tau \Rightarrow S
$$

## Inferência

- No repositório da disciplina, encontra-se uma implementação Haskell do 
algoritmo de inferência.

## Inferência

- O algoritmo desenvolvido possui o seguinte tipo: 

```haskell
infer :: Gamma -> Term -> Tc (Subst, Tau)
```

- que a partir de um contexto e uma expressão, produz um 
tipo e uma substituição.

## Inferência

- Regra para variáveis

$$
\dfrac{x : \forall\overline{\alpha}.\tau \in \Gamma\:\:\:\:
       \overline{\beta}\textrm{ são novas variáveis }}
      {\Gamma \vdash x : [\overline{\alpha_i\mapsto \beta_i}]\,\tau \Rightarrow id}
$$

## Inferência

- Instanciação 

```haskell
instantiate :: Sigma -> Tc Tau
instantiate (ForAll vs rho)
  = do
      let
        step acc v
          = do
              v' <- fresh
              return (Map.insert v v' acc)
      s <- foldM step idSubst vs
      return (apply s rho)
```

## Inferência

- Localizando uma variável no contexto

```haskell
lookupVar :: Gamma -> Name -> Tc (Subst, Tau)
lookupVar gamma v
  = case Map.lookup v gamma of
        Just sig ->
          do
            tau <- instantiate sig
            return (idSubst, tau)
        Nothing -> throwError "..."
```

## Inferência

- Inferência para variáveis

```haskell
infer gamma (Var v)
  = lookupVar gamma v
```

## Inferência 

- Regra para abstração

$$
\dfrac{
    \Gamma, x : \alpha \vdash e : \tau \Rightarrow S\:\:\:\:
    \alpha \textrm{ fresh }
}{\Gamma \vdash \lambda x. e : S(\alpha) \to \tau \Rightarrow S}
$$

## Inferência

- Inferência para abstração

```haskell
infer gamma (Lam n e)
  = do
      t <- fresh
      let
          sig = ForAll [] t
          gamma' = Map.insert n sig gamma
      (s', t') <- infer gamma' e
      return (s', (apply s' t) --> t')
```
    
## Inferência

- Regra para aplicação

$$
\begin{array}{c}
\dfrac{\Gamma\vdash e_1 : \tau_1\Rightarrow S_1\:\:\:
\Gamma\vdash e_2 : \tau_2\Rightarrow S_2\:\:\:
         \alpha\textrm{ fresh }}
        {\Gamma\vdash e_1\:e_2 : S_3 (\alpha)\Rightarrow S_3 \circ S_2 \circ S_1}\\
S_3 = \textrm{unify}(\tau_2\to\alpha,\tau_1)
\end{array}
$$

## Inferência

- Processo central para inferência de tipos: unificação.

- Intuitivamente, a unificação consiste em calcular uma substituição 
$S$ tal que $S(\tau_1) = S(\tau_2)$.

## Inferência

- A unificação de um tipo $\tau$ e uma variável resulta na substituição:

$$
[\alpha\mapsto \tau]
$$

- se $\alpha\not\in\textrm{fv}(\tau)$

## Inferência 

- A unificação de tipos $\tau_1\to\tau_2$ e $\tau'_1\to\tau'_2$ é dada por
$S_3 = S_2 \circ S_1$, em que:

$$
\begin{array}{lcl}
  S_1 & = & \textrm{unify}(\tau_1,\tau_1')\\
  S_2 & = & \textrm{unify}(S_1(\tau_2),S_1(\tau'_2))\\
\end{array}
$$

## Inferência

- Inferência para aplicações

```haskell
infer gamma (App fun arg)
  = do
      v <- fresh
      (s1, t1) <- infer gamma fun
      (s2, t2) <- infer (apply s1 gamma) arg
      s3 <- unify (apply s2 t1) (t2 --> v)
      return (s3 @@ s2 @@ s1, apply s3 v)
```

## Inferência

- Regra para let:

$$
\begin{array}{c}
\dfrac{
\Gamma \vdash e_1 : \tau_1 \Rightarrow S_1\:\:\:
S_1(\Gamma),x : \sigma \vdash e_2 : \tau_2\Rightarrow S_2
}{\Gamma \vdash \textrm{let }x = e_1 \textrm{ in }e_2 : \tau_2 \Rightarrow S_2} \\
\sigma = gen(\tau_1,\Gamma)\:\:\:
\end{array}
$$

## Inferência

- Implementando a inferência para let.

```haskell
infer gamma (Let n e e')
  = do
       (s1, t1) <- infer gamma e
       let gamma' = apply s1 gamma
           sig = generalization gamma' t1
       (s2, t2) <- infer (Map.insert n sig gamma') e'
       return (s2 @@ s1, t2)
```

## Inferência

- Isso conclui a apresentação do algoritmo de 
inferência de tipos para o $\lambda$-cálculo.

## Inferência

- Propriedades: O algoritmo é correto.

- Se $\Gamma \vdash e : \tau \Rightarrow S$ então $S(\Gamma)\vdash e : S(\tau)$.

## Inferência

- Propriedades: O algoritmo é completo.

- Se $\Gamma\vdash e : \tau$ então existe $S'$, $S''$, $\Gamma'$ e $\tau'$ tais que 
$\Gamma = S'(\Gamma')$,  $\tau = S'(\tau')$, $\Gamma'\vdash e : \tau' \Rightarrow S$ e 
$S' = S'' \circ S$.

## Inferência

- Uma implementação deste algoritmo está disponível no repositório da disciplina.

<https://github.com/rodrigogribeiro/pcc116-2021-2/tree/master/code/hindley-milner>

# Referências

## Referências

- Pierce, Benjamin. Types and Programming Languages, MIT Press. 2002.

- Damas, Luis; Milner, Robin. Principal types schemes for functional programs.
POPL 82.


