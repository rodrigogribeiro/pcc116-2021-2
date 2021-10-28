---
title: Co-indução em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

<!--
```agda
{-# OPTIONS --copatterns --sized-types --guardedness #-}

module aula20 where

open import Basics.Admit
open import Coinduction.Size
open import Data.Bool.Bool
open import Data.Function.Function
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Unit.Unit

open import Relation.Equality.Propositional
open import Relation.Decidable.Dec
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

- Intuitivamente, a co-indução permite observar, de forma finita,
estruturas possivelmente infinitas.

# Streams

- O tipo co-indutivo mais comum é o de Streams, ou listas infinitas.

- O parâmetro `Size` é usado por Agda para verificar definições
co-indutivas.
     - Pode ser entendido como um limite superior para o tamanho da lista.
     - Size não possui construtores: ∞ representa tamanho ilimitado,
       _⊔_ representa o máximo de dois sizes, _↑ o próximo size (sucessor)
       e Size< denota uma restrição de que o tamanho deve ser um size
       "menor".

```agda
module Stream where

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

- Interleaving

```agda
  interleave : ∀ {i A} → Stream i A → Stream i A → Stream i A
  head (interleave s1 s2) = head s1
  tail (interleave s1 s2) = interleave s2 (tail s1)
```
- Funções de ordem superior sobre Stream: map.

```agda
  map : ∀ {A B i} → (A → B) → Stream i A → Stream i B
  head (map f xs) = f (head xs)
  tail (map f xs) = map f (tail xs)
```

- Funções de ordem superior sobre Stream: zipWith

```agda
  zipWith : ∀ {A B C i} → (A → B → C) →
                           Stream i A    →
                           Stream i B    →
                           Stream i C
  head (zipWith f xs ys) = f (head xs) (head ys)
  tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)
```

- Exemplo: Sequencia de Fibonacci

```agda
  fib : ∀ {i} → Stream i ℕ
  head fib        = 0
  head (tail fib) = 1
  tail (tail fib) = zipWith _+_ fib (tail fib)
```

- Até aqui, vimos alguns exemplos de funções
definidas por co-recursão.

- Porém, como provar propriedades sobre Streams?

```agda
  ones : ∀ {i} → Stream i ℕ
  head ones = 1
  tail ones = ones
```

- Exemplo: provar que ones ≡ map suc zeros

```agda
  example : ones ≡ map suc zeros
  example = admit
```

- Não é possível a igualdade proposicional sobre Streams.
   - Igualdade proposicional requer a avaliação completa
     de seus argumentos.
   - Logo, avaliar um Stream poderá causar não terminação.
   - Como resolver?

- A solução é usar o conceito de bissimulação.

```agda
  record _∼_ {A : Set} (s s' : Stream ∞ A) : Set where
    coinductive
    field
      head : head s ≡ head s'
      tail : tail s ∼ tail s'

  open _∼_

  ones-mapsuc : ones ∼ map suc zeros
  head ones-mapsuc = refl
  tail ones-mapsuc = ones-mapsuc
```

- Exemplo: gerando números naturais

```agda
  enum : ∀ {i} → ℕ → Stream i ℕ
  head (enum n) = n
  tail (enum n) = enum (suc n)

  nats : ∀ {i} → Stream i ℕ
  nats = enum 0
```

- Exemplo: provando que todos os números
naturais pertencem a nats.

```agda
  data _∈_ {A}(x : A)(xs : Stream ∞ A) : Set where
    here  : x ≡ head xs → x ∈ xs
    there : x ∈ tail xs → x ∈ xs

  ∈-suc : ∀ {n m : ℕ} → n ∈ enum m → suc n ∈ enum (suc m)
  ∈-suc (here refl) = here refl
  ∈-suc (there n∈enumm) = there (∈-suc n∈enumm)

  ℕ∈nats : ∀ (n : ℕ) → n ∈ nats
  ℕ∈nats zero = here refl
  ℕ∈nats (suc n) = there (∈-suc (ℕ∈nats n))
```

# Modelando linguagens como tipos co-indutivos

- Vamos considerar uma aplicação da co-indução: modelagem
de linguagens de autômatos finitos.

- Primeiro, vamos definir um tipo para listas com um parâmetro
de size.

```agda
module SizedList where

  data List (i : Size)(A : Set) : Set where
    []  : List i A
    _∷_ : {j : Size< i} → A → List j A → List i A

  foldr : ∀ {i}{A B : Set} → (A → B → B) → B → List i A → B
  foldr _ v [] = v
  foldr f v (x ∷ xs) = f x (foldr f v xs)

  map : ∀ {i}{A B : Set} → (A → B) → List i A → List i B
  map _ [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  any : ∀ {i}{A : Set} → (A → Bool) → List i A → Bool
  any _ [] = false
  any p (x ∷ xs) = p x || any p xs
```

- Definindo uma linguagem, em termos da operação de
derivada.

δ(L,a) = {w | aw ∈ L}

```agda
module Language {A : Set}(_≟_ : ∀ (x y : A) → Dec (x ≡ y)) where

  open SizedList

  String : Size → Set
  String i = List i A

  record Lang i : Set where
    coinductive
    field
      null : Bool
      δ    : ∀ {j : Size< i} → A → Lang j

  open Lang
```

- Definindo quando uma string pertence a uma linguagem

```agda
  _∋_ : ∀ {i} → Lang i → String i → Bool
  l ∋ []       = null l
  l ∋ (a ∷ as) = δ l a ∋ as
```

- Definição da linguagem vazia

```agda
  ∅ : ∀ {i} → Lang i
  null ∅ = false
  δ ∅ a  = ∅

  _ : ∅ ∋ [] ≡ false
  _ = refl
```

- Definição da linguagem {ε}

```agda
  ε : ∀ {i} → Lang i
  null ε = true
  δ ε a  = ∅

  _ : ε ∋ [] ≡ true
  _ = refl
```

- Definição da linguagem de um símbolo

```agda
  symb : ∀ {i} → A → Lang i
  null (symb a) = false
  δ (symb a) a' with a ≟ a'
  ...| yes q = ε
  ...| no  q = ∅
```

- União e interseção de linguagens

```agda
  _∪_ : ∀ {i} → (l r : Lang i) → Lang i
  null (l ∪ r) = null l || null r
  δ (l ∪ r) a  = δ l a ∪ δ r a

  _∩_ : ∀ {i} → (l r : Lang i) → Lang i
  null (l ∩ r) = null l && null r
  δ (l ∩ r) a  = δ l a ∩ δ r a
```

- Complementação de linguagens

```agda
  compl : ∀ {i} → Lang i → Lang i
  null (compl l) = not (null l)
  δ (compl l) a  = compl (δ l a)
```

- Concatenação de linguagens

```agda
  _∙_ : ∀ {i}(l r : Lang i) → Lang i
  null (l ∙ r) = null l && null r
  δ (l ∙ r) {j} a
    = let k'l : Lang j
          k'l = (δ l {j} a) ∙ r
      in if null l then k'l ∪ (δ r {j} a)
            else k'l
```

- Fecho Kleene

```agda
  star : ∀ {i} → Lang i → Lang i
  null (star l) = true
  δ (star l) a = δ l a ∙ star l
```

- Definição de um autômato.

```agda
  record DFA (State : Set) : Set where
    field
      final : (s : State) → Bool
      δ     : (s : State)(a : A) → State

  open DFA {{...}}
```

- Final e δ para lista de estados.

```agda
  finalList : ∀ {i S}{{_ : DFA S}} → List i S → Bool
  finalList = any final

  δList : ∀ {i S}{{_ : DFA S}} → List i S → A → List i S
  δList {{M}} ss a = map (λ s → δ M s a) ss
```

- Linguagem aceita por um DFA

```agda
  lang : ∀ {i}{S} → DFA S → S → Lang i
  Lang.null (lang dfa s)   = DFA.final dfa s
  Lang.δ    (lang dfa s) a = lang dfa (DFA.δ dfa s a)
```

- Autômatos simples

```agda
  ∅-DFA : DFA ⊤
  DFA.final ∅-DFA s   = false
  DFA.δ     ∅-DFA s a = s

  ε-DFA : DFA Bool
  DFA.final ε-DFA s    = s
  DFA.δ     ε-DFA s a  = false

  data Triple : Set where
    init acc err : Triple

  symb-DFA : (a : A) → DFA Triple
  DFA.final (symb-DFA a) init = false
  DFA.final (symb-DFA a) acc  = true
  DFA.final (symb-DFA a) err  = false
  DFA.δ     (symb-DFA a) init x with x ≟ a
  ...| yes _ = acc
  ...| no  _ = err
  DFA.δ     (symb-DFA a) acc x = err
  DFA.δ     (symb-DFA a) err x = err
```

- Construção de produto

```agda
  product : ∀ {A B} → (Bool → Bool → Bool) → DFA A → DFA B → DFA (A × B)
  DFA.final (product _⊕_ MA MB) (a , b)
    = DFA.final MA a ⊕ DFA.final MB b
  DFA.δ     (product _⊕_ MA MB) (a , b) x
    = DFA.δ MA a x , DFA.δ MB b x

  ∪-DFA : ∀ {A B} → DFA A → DFA B → DFA (A × B)
  ∪-DFA = product _||_

  ∩-DFA : ∀ {A B} → DFA A → DFA B → DFA (A × B)
  ∩-DFA = product _&&_
```

# Conclusão

- Nesta aula vimos como tipos co-indutivos permitem a definição
de objetos infinitos em Agda.

- Apresentamos alguns exemplos envolvendo Streams e definição
de linguagens e autômatos usando co-indução.

# Referências

- Abel, Andreas. Equational Reasoning about Formal Languages in
Coalgebraic Style
