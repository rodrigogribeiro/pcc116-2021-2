---
title: Recursão não estrutural em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

<!--
```agda
module aula19 where

open import Data.Empty.Empty
open import Data.List.List     hiding (map)
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Unit.Unit

open import Prelude.Classes

open import Relation.Properties
open import Relation.Equality.Propositional
```
-->


# Objetivos

- Discutir os motivos para assistentes de prova para
limitar definições recursivas.

- Apresentar técnicas para definir funções recursivas em
assistentes de provas.


# Consistência lógica em assistentes de provas


- Um problema central em assistentes de provas é o de garantir
que a lógica associada seja consistente.

- Para garantir a consistência, todas as funções definíveis no
assistente de provas devem ser totais.

- Função total: resultado definido para toda entrada.
    - Toda função total termina em tempo finito.
    - Toda função total deve realizar casamento de padrão
      exaustivo.

- Para nosso estudo de recursão geral em Agda, vamos considerar
dois exemplos:
    - Divisão sobre números naturais
    - Intercalação de listas.


Divisão sobre números naturais
==============================

- Uma maneira de definir a divisão sobre números naturais
é como uma repetição da subtração.

6 / 2 = 1 + (4 / 2) = 1 + (1 + (2 / 2)) = 1 + (1 + (1 + 0 / 2)) = 3

```haskell
div : ℕ → ℕ → ℕ
div zero m = 0
div n    m = suc (div (n - m) m)
```

- Porém, a definição acima possui um problema:
    - Não considera a possibilidade de divisão por zero.

- Podemos definir um tipo para exigir que o dividendo
seja diferente de zero.

```agda
NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤
```

- Adicionalmente, podemos usar instance arguments para
que Agda preencha a dedução de NonZero automaticamente.

```agda
div1 : (n m : ℕ){{_ : NonZero m}} → ℕ
div1 0 m = m
div1 n m = 0
```

- Porém, ao tentarmos fazer o type checking do código
encontramos mais um problema: Agda não identifica a
função div como total.
    - O type checker não identifica que o primeiro
      argumento de div sempre diminui em cada
      chamada recursiva.

- Então como definir essa função? Existem algumas possibilidades:
    - Uso de fuel
    - Well-founded recursion
    - Bove-Capretta predicates


# Divisão usando fuel

- A maneira mais simples para garantir a terminação de funções
é o uso de um número natural para limitar a quantidade de
chamadas recursivas permitidas.

```agda
Fuel : Set
Fuel = ℕ

module DivFuel where
```

- Primeiramente, definimos Fuel como um sinônimo para o
tipo ℕ

- Em sequência definimos a função para divisão, retornando
`nothing` quando o Fuel chega a zero.

```agda
  div-fuel : Fuel → (n m : ℕ).{{_ : NonZero m}} → Maybe ℕ
  div-fuel zero n m = nothing
  div-fuel (suc gas) 0 m = just 0
  div-fuel (suc gas) n m
    = map suc (div-fuel gas (n - m) m)

  _ : div-fuel 6 6 2 {{tt}} ≡ just 3
  _ = refl
```

- Usando a função `div-fuel`, podemos definir a função de
divisão de maneira simples.

```agda
  div : (n m : ℕ).{{_ : NonZero m}} → Maybe ℕ
  div n m = div-fuel n n m
```

- O uso de fuel permite a definição de funções de maneira
simples, porém:
    - Inclui um parâmetro adicional à definição.
    - Nem sempre é fácil determinar o quanto de "fuel" é
      necessário para execução de uma chamada.


# Divisão por well-founded recursion

- O problema central em garantir a terminação de uma função
é mostrar que cada chamada recursiva é feita sobre argumentos
menores.

- Como garantir que chamadas feitas sobre argumentos menores
realmente terminam?
    - Observe que apenas isso não garante terminação.
    - Ex: subtração sobre números inteiros.

- Para garantir a terminação devemos impor que não existam
  cadeias decrescentes infinitas.

x_1 > x_2 > x_3 ... x_n > x_{n + 1} ...

- Toda relação que não possui cadeias decrescentes infinitas é
dita ser uma relação bem formada.

- Vamos modelar esse conceito de forma construtiva usando a noção
de acessibilidade, com respeito a uma relação de ordem:
    - Elementos minimais são acessíveis =>  ¬ ∃ y . y < x
    - Um elemento x é acessível se todos os elementos menores que x
      são acessíveis.

```agda
module WellFounded where

  data Acc {A : Set}(_<_ : Relation A)(x : A) : Set where
    acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x
```

- Usando a acessibilidade, podemos definir o conceito de
relação bem formada.

```agda
  WellFounded : {A : Set}(_<_ : Relation A) → Set
  WellFounded _<_ = ∀ x → Acc _<_ x
```

- A partir do tipo de acessibilidade, podemos definir
um operador `fold` --- recursor:

```agda
  acc-fold : {A : Set}                             →
             {_<_ : Relation A}                    →
             {P : A → Set}                        →
             (∀ x → (∀ y → y < x → P y) → P x) →
             ∀ z → Acc _<_ z → P z
  acc-fold IH z (acc H) = IH z (λ y y<z → acc-fold IH y (H y y<z))
```

- A partir do recursor de acessibilidade, podemos definir
o princípio de indução por well-founded induction.

```agda
  wfRec : {A : Set}                             →
          (_<_ : Relation A)                    →
          WellFounded _<_                       →
          ∀ (P : A → Set)                      →
          (∀ x → (∀ y → y < x → P y) → P x) →
          ∀ a → P a
  wfRec R wf P IH a = acc-fold IH a (wf a)
```

- Logo, temos a definição de um princípio de indução
para uma relação bem formada.

- Temos então que definir uma relação bem formada sobre o
  conjunto ℕ.

- Uma possível relação bem formada sobre ℕ é <.

```agda
module ℕ-Lt where
  open WellFounded

  data _<_ (n : ℕ) : ℕ → Set where
    <-base : n < suc n
    <-step : ∀ {m} → n < m → n < suc m

  <-ℕ-wf : WellFounded _<_
  <-ℕ-wf x = acc (IH x)
    where
      IH : ∀ x y → y < x → Acc _<_ y
      IH (suc x) .x <-base = <-ℕ-wf x
      IH (suc x) y (<-step y<x) = IH x y y<x
```

- Usando essa definição da relação <, vamos demonstrar
que n - m < n.

- Esse resultado será utilizado para demonstrar que
a chamada recursiva de `div` sempre diminui o primeiro
argumento.

```agda
  n-m<n+1 : ∀ (n m : ℕ){{_ : NonZero m}} → (n - m) < suc n
  n-m<n+1 zero    (suc m)       = <-base
  n-m<n+1 (suc n) (suc zero)    = <-step <-base
  n-m<n+1 (suc n) (suc (suc m)) = <-step (n-m<n+1 n (suc m))
```

- De posse da infra-estrutura anterior, podemos construir
o algoritmo para divisão de números naturais.

```agda
module DivWellFounded where
  open WellFounded
  open ℕ-Lt

  div : (n m : ℕ){{_ : NonZero m}} → ℕ
  div n m = wfRec _<_         -- relação de ordem
                  <-ℕ-wf      -- prova de well-foundness
                  (λ _ → ℕ)  -- tipo de retorno
                  step        -- corpo da função
                  n           -- entrada
    where
      step : ∀ (x : ℕ) → ((y : ℕ) → y < x → ℕ) → ℕ
      step zero    IH = 0
      step (suc x) IH = suc (IH (x - m) (n-m<n+1 x m))
```

- Uma vantagem do uso de well-founded relations é que
não incluímos um parâmetro artificial para satisfazer
o type checker de Agda.

- Outra vantagem, é que o podemos construir well-founded
relations usando diversas propriedades de fechamento:
união, imagem inversa, produto cartesiano, entre outras.

- Desvantagem: A definição é feita usando um princípio de
indução, o que não corresponde diretamente a como essa
função seria implementada por casamento de padrão.


# Divisão usando Bove-Capretta predicates.


- O uso de well-founded relations é baseado em um predicado
de acessibilidade genérico que é aplicável a qualquer
relação bem formada.


- A técnica desenvolvida por Ana Bove e Venanzio Capretta
consiste em definir um predicado que representa a estrutura
de chamadas recursivas da função.

- Abaixo, apresentamos o predicado que representa a estrutura
recursiva da divisão.

```agda
module DivBoveCapretta where

  data _≺_ : ℕ → ℕ → Set where
    ≺-base : ∀ {m} → 0 ≺ suc m
    ≺-one  : ∀ {n} → (suc n) ≺ 1
    ≺-step : ∀ {n m} → (n - m) ≺ m →
                       n ≺ (suc m)
```

- Na sequência, devemos provar que esse predicado
é válido para todo o domínio da função.

```agda
  ≺-all : ∀ (n m : ℕ).{{_ : NonZero m}} → n ≺ m
  ≺-all zero (suc m)          = ≺-base
  ≺-all (suc n) (suc zero)    = ≺-one
  ≺-all (suc n) (suc (suc m)) = ≺-step (≺-all (n - m) (suc m))
```

- A definição da divisão é feita por recursão
sobre a estrutura do predicado.

```agda
  div-≺ : ∀ {n m : ℕ} → n ≺ m → ℕ
  div-≺ ≺-base       = 0
  div-≺ {n} ≺-one    = n
  div-≺ (≺-step n≺m) = suc (div-≺ n≺m)
```

- Para definir a função div, basta combinarmos a prova de
que o predicado é válido para todo o domínio e a função
div-≺.

```agda
  div : ∀ (n m : ℕ).{{_ : NonZero m}} → ℕ
  div n m = div-≺ (≺-all n m)
```

Intercalação de listas
======================

- Vamos considerar um exemplo um pouco maior: a rotina
de intercalação de listas utilizada pelo algoritmo
mergesort.

```haskell
merge : List A → List A → List A
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) = if x <= y then x ∷ merge xs (y ∷ ys)
                                    else y ∷ merge (x ∷ xs) ys
```

# Intercalação usando fuel

- A implementação da intercalação de listas usando fuel é
bastante imediata.

```agda
module MergeFuel {{_ : Compare A }} where

  merge-fuel : Fuel → List A → List A → Maybe (List A)
  merge-fuel zero      xs       ys       = nothing
  merge-fuel (suc gas) []       ys       = just ys
  merge-fuel (suc gas) (x ∷ xs) []       = just (x ∷ xs)
  merge-fuel (suc gas) (x ∷ xs) (y ∷ ys) with compare x y
  ...| less    = map (x ∷_) (merge-fuel gas xs (y ∷ ys))
  ...| equal   = map (y ∷_) (merge-fuel gas (x ∷ xs) ys)
  ...| greater = map (y ∷_) (merge-fuel gas (x ∷ xs) ys)
```

# Intercalação usando well-founded relations

- Primeiro, devemos definir uma relação bem formada sobre
pares de listas.

- A relação é dada por:

     (xs, xs') << (ys, ys') = length xs < length ys ||
                              (length xs == length ys &&
                               length xs' < length ys')
- Para construir essa relação bem formada, vamos utilizar
algumas propriedades de fechamento.

- Relações bem formadas são fechadas sobre imagem inversa.

- Primeiro, mostramos uma relação de ordem sobre a imagem
de uma função, usando uma relação sobre seu
contra-domínio: _<_.

```agda
module InverseImageWellFounded {A B}(f : A → B)(_<_ : Relation B) where

  open WellFounded

  _<<_ : Relation A
  x << y = f x < f y
```

- Em seguida, vamos mostrar que se temos uma prova
de que f x é acessível, então podemos construir uma
demonstração de que x é acessível usando a relação
_<<_ sobre o tipo A.

```agda
  inv-img-acc : ∀ {x} → Acc _<_ (f x) → Acc _<<_ x
  inv-img-acc (acc g) = acc (λ y fy<fx → inv-img-acc (g (f y) fy<fx))
```

- A partir da função anterior, podemos construir uma prova
de que _<<_ é uma relação bem formada a partir do fato de
que _<_ é uma relação bem formada.

```
  inv-img-WF : WellFounded _<_ → WellFounded _<<_
  inv-img-WF wf x = inv-img-acc (wf (f x))
```

- Nosso próximo passo será construir uma relação de
ordem lexicográfica, a partir de relações bem formadas
para conjuntos A e B.

- Inicialmente, vamos definir um módulo parametrizado
por relações sobre tipos A e B.

```agda
module Lexicographic {A B : Set}(_<A_ : Relation A)
                                (_<B_ : Relation B) where
  open WellFounded
```

- A seguir, precisamos definir alguma infra-estrutura
para a construção de uma relação bem formada sobre
os tipos A e B.

- Primeiro, vamos definir um tipo para representar um predicado.

```agda
  Pred : Set → Set₁
  Pred A = A → Set
```

- Usando a definição de predicados, podemos criar um tipo
para representar uma hipótese de indução.

```agda
  RecStruct : Set → Set₁
  RecStruct A = Pred A → Pred A

  WfRec : ∀ {A} → Relation A → RecStruct A
  WfRec _<_ P x = ∀ y → y < x → P y
```

- Podemos codificar a ordem entre pares de valores.

```agda
  data _⊏_ : Relation (A × B) where
    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : x₁ <A x₂) → (x₁ , y₁) ⊏ (x₂ , y₂)
    right : ∀ {x y₁ y₂}     (y₁<y₂ : y₁ <B y₂) → (x  , y₁) ⊏ (x  , y₂)
```

- Usando o tipo _⊏_ sobre pares, podemos construir a prova de
acessibilidade entre pares, como funções mutuamente recursivas.

```agda
  accessibleA : ∀ {x y} → Acc _<A_ x       →
                           WellFounded _<B_ →
                           Acc _⊏_ (x , y)

  accessibleB : ∀ {x y} → Acc _<A_ x →
                           Acc _<B_ y →
                           WellFounded _<B_ →
                           WfRec _⊏_ (Acc _⊏_) (x , y)


  accessibleA accA wfB
    = acc (accessibleB accA (wfB _) wfB)

  accessibleB (acc IHA) accB wfB _ (left x₁<x₂)
    = accessibleA (IHA _ x₁<x₂) wfB
  accessibleB accA (acc IHB) wfB _ (right y₁<y₂)
    = acc (accessibleB accA (IHB _ y₁<y₂) wfB)
```

- A seguir, podemos codificar uma função para criar
uma relação bem formada sobre pares a partir de
relações sobre tipos A e B.

```agda
  wellFounded : WellFounded _<A_ → WellFounded _<B_ → WellFounded _⊏_
  wellFounded wfA wfB p = accessibleA (wfA (proj₁ p)) wfB
```

- Usando essa infra-estrutura, podemos definir uma relação
bem formada considerando a função length de listas.

```agda
module LengthWF (A : Set) where
  open import Data.List.List
  open ℕ-Lt
  open InverseImageWellFounded (length {A = A}) _<_ public
  open WellFounded

  length-wf : WellFounded _<<_
  length-wf = inv-img-WF <-ℕ-wf
```

- Finalmente, podemos construir uma relação bem formada
para pares de listas.

```agda
module MergeWF (A : Set) where
  open LengthWF A
  open Lexicographic _<<_ _<<_
  open WellFounded

  merge-wf : WellFounded _⊏_
  merge-wf = wellFounded length-wf length-wf

  _<*_ : Relation (List A × List A)
  x <* y = x ⊏ y
```

- Finalmente, usando a relação sobre pares de listas,
podemos definir a função de intercalação por
well-founded recursion.

```agda
module Merge where
  open MergeWF ℕ
  open WellFounded
  open Lexicographic
  open import Prelude.Nat
  open ℕ-Lt
```

- Para definir a intercalação de listas, precisamos mostrar que
as chamadas recursivas diminuem o tamanho da entrada, de acordo
com a ordem definida sobre pares de listas.

```agda
  termination-1 : ∀ (xs ys : List ℕ) x y → (xs , y ∷ ys) <* (x ∷ xs , y ∷ ys)
  termination-1 xs ys x y = left <-base
```

- O segundo lema mostra que a chamada para o caso x ≥ y também
satisfaz a ordem sobre pares.

```agda
  termination-2 : ∀ (xs ys : List ℕ) x y → (x ∷ xs , ys) <* (x ∷ xs , y ∷ ys)
  termination-2 xs ys x y = right <-base
```

- Usando os lemas para as chamadas recursivas, a definição da
função merge é feita de forma direta usando o combinador
wfRec.

```agda
  merge : List ℕ → List ℕ → List ℕ
  merge xs ys = wfRec _<*_ merge-wf (λ _ → List ℕ) step (xs , ys)
    where
      step : ∀ (x : List ℕ × List ℕ) →
               (∀ y → y <* x → List ℕ) → List ℕ
      step ([] , ys') IH      = ys'
      step (x ∷ xs' , []) IH  = x ∷ xs'
      step (x ∷ xs' , y ∷ ys') IH with compare x y
      ...| less  = x ∷ IH (xs' , y ∷ ys') (termination-1 xs' ys' x y)
      ...| equal = y ∷ IH (x ∷ xs' , ys') (termination-2 xs' ys' x y)
      ...| greater = y ∷ IH (x ∷ xs' , ys') (termination-2 xs' ys' x y)
```

# Intercalação de listas usando Bove-Capretta predicates.

- Primeiramente, vamos definir um predicado que representa
a estrutura recursiva da função merge.

```agda
module MergeBove where

  open import Prelude.Nat
  open ℕ-Lt
  open WellFounded
  open MergeWF ℕ
  open Lexicographic renaming (_⊏_ to _⊑_)

  data _⊏_ : List ℕ → List ℕ → Set where
    ⊏-1 : ∀ {xs} → xs ⊏ []
    ⊏-2 : ∀ {ys} → [] ⊏ ys
    ⊏-3 : ∀ {x y xs ys} → x ≤ y → xs ⊏ (y ∷ ys) → (x ∷ xs) ⊏ (y ∷ ys)
    ⊏-4 : ∀ {x y xs ys} → x ≥ y → (x ∷ xs) ⊏ ys → (x ∷ xs) ⊏ (y ∷ ys)
```

- De posse do predicado, podemos definir a função
de intercalação por indução sobre xs ⊏ ys.

```agda
  merge-bove : {xs ys : List ℕ} → xs ⊏ ys → List ℕ
  merge-bove {xs = xs} ⊏-1 = xs
  merge-bove {ys = ys} ⊏-2 = ys
  merge-bove {xs = x ∷ xs}(⊏-3 x≤y xs⊏ys) = x ∷ (merge-bove xs⊏ys)
  merge-bove {ys = y ∷ ys}(⊏-4 x≥y xs⊏ys) = y ∷ (merge-bove xs⊏ys)
```

- Em seguida, mostramos que o predicado é válido para
quaisquer listas. Para isso, usaremos well-founded
induction.

```agda
  ⊏-all : (xs ys : List ℕ) → xs ⊏ ys
  ⊏-all xs ys
    = wfRec _<*_
            merge-wf
            (λ p → proj₁ p ⊏ proj₂ p)
            step
            (xs , ys)
      where
        step : ∀ x → (∀ y → y <* x → proj₁ y ⊏ proj₂ y) → proj₁ x ⊏ proj₂ x
        step ([] , ys') IH = ⊏-2
        step (x ∷ xs' , []) IH = ⊏-1
        step (x ∷ xs' , y ∷ ys') IH with compare x y
        ...| less {{x≤y}}    = ⊏-3 x≤y (IH (xs' , y ∷ ys')
                                           (Merge.termination-1 xs' ys' x y))
        ...| equal {{refl}}  = ⊏-4 ≤-refl (IH (x ∷ xs' , ys')
                                              (Merge.termination-2 xs' ys' x y))
        ...| greater {{x≥y}} = ⊏-4 x≥y (IH (x ∷ xs' , ys')
                                           (Merge.termination-2 xs' ys' x y))

```

- De posse da prova de que o predicado é válido para todos pares de
listas e da função de intercalação definida sobre o predicado,
a definição de `merge` é imediata.

```agda
  merge : List ℕ → List ℕ → List ℕ
  merge xs ys = merge-bove (⊏-all xs ys)
```

# Conclusão

- Apresentamos 3 técnicas para definição de funções que usam
recursão não estrutural em Agda.

- Evidentemente, cada uma dessas técnicas tem suas vantagens
e desvantagens.
    - Fuel: simples, porém adiciona um parâmetro adicional.
    - Well-founded induction:
        - Complexa: depende de uma biblioteca contendo a infra
          para construção de relações bem formadas.
        - Definição de funções não é similar a uma implementação
          em linguagens funcionais.
        - Tipo final da definição é idêntico ao de uma implementação
          em linguagens funcionais.
    - Bove and Capretta predicates:
        - Depende da definição de um predicado que representa a
          estrutura recursiva da função.
        - Deve-se provar que todo o domínio da função satisfaz
          o predicado.
        - Função possui definição natural por indução sobre o
          predicado.
        - Tipo final idêntico ao de uma implementação em linguagens
          funcionais.
        - Processo automatizável na prática.

# Referências

- McBride, Connor. Turing Completeness Totally Free.

- Bove, Ana; Capretta, Venanzio. Modelling General Recursion in Type Theory.
