---
title: Co-indução em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

<!--
```agda
{-# OPTIONS --copatterns --sized-types #-}

module aula20 where

open import Coinduction.Size
open import Data.Bool.Bool
open import Data.Nat.Nat

open import Relation.Equality.Propositional
```
-->

# Objetivos

- Apresentar o conceito de co-indução e de seu uso para demonstrar
fatos sobre estruturas possivelmente infinitas.

- Apresentar como definir tipos co-indutivos na linguagem Agda.

# Introdução

- Indução é o princípio de prova mais utilizado em computação.

- A rigor a indução descreve como uma propriedade é válida para
objetos construídos de forma finita.

- Porém, nem sempre em computação estamos interessados em objetos
finitos.
    - Como lidar uma lista possivelmente infinita de processos
      em um servidor web?

- Para lidar com estruturas possivelmente infinitas, devemos usar
o princípio de co-indução.

# Streams

- O tipo co-indutivo mais comum é o de Streams, ou listas infinitas.

```agda
record Stream (i : Size)(A : Set) : Set where
  constructor _∷_
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream j A

open Stream
```

- Usando o tipo Stream podemos criar uma lista infinita
formada apenas por zeros.

```agda
zeros : ∀ {i} → Stream i ℕ
head zeros = 0
tail zeros = zeros
```

- A função zeros é definida por co-pattern matching.
    - Equações definem como observar cada campo do Stream.

- Podemos construir streams mutuamente recursivos.

```agda
trues  : ∀ {i} → Stream i Bool
falses : ∀ {i} → Stream i Bool

head trues = true
tail trues = trues

head falses = false
tail falses = falses
```

- Funções de ordem superior sobre Stream.

```agda
map : ∀ {A B i} → (A → B) → Stream i A → Stream i B
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

zipWith : ∀ {A B C i} → (A → B → C) →
                         Stream i A    →
                         Stream i B    →
                         Stream i C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)
```

- Sequencia de Fibonacci

```agda
fib : ∀ {i} → Stream i ℕ
head fib        = 0
head (tail fib) = 1
tail (tail fib) = zipWith _+_ fib (tail fib)
```

- Bissimulation: stream equality

```agda
infix 4 _≈_

record _≈_ {A : Set}{i} (xs ys : Stream i A) : Set where
  constructor _∷_
  coinductive
  field
    ≈-head : head xs ≡ head ys
    ≈-tail : tail xs ≈ tail ys
```
