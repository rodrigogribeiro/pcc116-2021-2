---
title: Programação com tipos dependentes
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

<!--
```agda
module aula17 where

open import Algebra.Order.Order

open import Data.Bool.Bool
open import Data.Empty.Empty
open import Data.Function.Function
open import Data.Isomorphism.Isomorphism
open import Data.List.List
open import Data.List.Relation.All
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Nat.Le
open import Data.Sum.Sum
open import Data.Sigma.Sigma
open import Data.Unit.Unit

open import Relation.Equality.Propositional
open import Relation.Properties
```
-->

# Objetivos

- Discutir detalhes sobre o funcionamento do casamento
de padrões na presença de tipos dependentes.

- Apresentar como tipos dependentes permitem combinar
demonstrações à definições de programas.

# Casamento de padrão com tipos dependentes

- O casamento de padrão usando tipos dependentes
é feito, em Agda, usando a construção `with`.

- Para entendermos o funcionamento do `with`,
vamos considerar um exemplo: um teste de paridade
sobre números naturais.

```agda
data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)
```

# Casamento de padrão com tipos dependentes

- Agora, vamos mostrar que é possível construir um
valor `Parity n` para todo `n : ℕ`:

```agda
parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2))     | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)
```

- Observe que o casamento de padrão sobre `parity n`
especializou o padrão `n` para o valor esperado em
cada caso.
* Caso even k, então n = k * 2
* Caso odd k, então n = 1 + k * 2


# Casamento de padrão com tipos dependentes

- Usando `parity`, podemos construir uma função
para o obter para dividir um número natural por
2 de maneira simples.

```agda
half : ℕ → ℕ
half n with parity n
...| even k = k
...| odd k  = k
```

# Casamento de padrão com tipos dependentes

- Outra aplicação interessante: identificar o primeiro
elemento de uma lista que satisfaz um predicado.

```agda
data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A)     →
                     T (p y)       →
                     (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs}                 →
                All (T ∘ not ∘ p) xs → Find p xs
```

# Casamento de padrão com tipos dependentes

- Definição da função `find`

```agda
trueTrue : ∀ {v : Bool} → v ≡ true → T v
trueTrue refl = tt

falseFalse : ∀ {v : Bool} → v ≡ false → (T (not v))
falseFalse refl = tt

find : ∀ {A}(p : A → Bool)(xs : List A) → Find p xs
find p [] = not-found []
find p (x ∷ xs) with inspect (p x)
... | it true  eq = found [] x (trueTrue eq) xs
... | it false eq with find p xs
...    | found xs y Ty ys = found (x ∷ xs) y Ty ys
...    | not-found npxs = not-found (falseFalse eq ∷ npxs)
```

# Programação com tipos dependentes

- A principal utilidade de tipos dependentes é a de combinar
a demonstração de correção e desenvolvimento de software em
um mesmo formalismo.

- Em aulas anteriores, definimos o seguinte resultado para
listas:

     length (xs ++ ys) ≡ length xs + length ys

- É possível garantir essa propriedade _por construção_?

- A resposta é sim! Para isso, vamos definir um tipo de dados
chamado `Vec` (de Vector).

```agda
data Vec {a}(A : Set a) : ℕ → Set a where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
```

- Exemplos

```agda
_ : Vec ℕ 3
_ = 1 ∷ 2 ∷ 3 ∷ []
```

# Head

- A função `head` para listas, deve ser parcial.
   - Para isso, vamos usar o tipo `Maybe`

```agda
headList : ∀ {a}{A : Set a} → List A → Maybe A
headList [] = nothing
headList (x ∷ _) = just x
```

# Head

- Usando `Vec`, podemos definir head como uma função
total.

```agda
head : ∀ {a}{A : Set a}{n} → Vec A (suc n) → A
head (x ∷ _) = x
```

# Concatenação

- A concatenação de vectors garante, por construção,
a propriedade de tamanho.

```agda
_++V_ : ∀ {a}{A : Set a}{n m} → Vec A n → Vec A m → Vec A (n + m)
[]       ++V ys = ys
(x ∷ xs) ++V ys = x ∷ (xs ++V ys)
```

# A função `map` preserva o tamanho

- Novamente, temos que uma propriedade é dada pela
implementação da função.

```agda
mapV : ∀ {a b}{A : Set a}{B : Set b}{n} →
         (f : A → B)(xs : Vec A n)     →
         Vec B n
mapV f []       = []
mapV f (x ∷ xs) = f x ∷ mapV f xs
```

# Indexação

- Em listas, para obter um elemento na n-ésima
posição, devemos utilizar uma evidência que a
posição é menor que o número de elementos da lista.

     nth : ∀ {A} p (xs : List A) → p <= length xs → Maybe A

- Utilizando tipos dependentes, podemos definir essa função
de forma a evitar acesso de posições inválidas em tempo de
compilação.

- Para isso, primeiro devemos definir um tipo que representa
conjuntos finitos.

# Tipos finitos

- `Fin n` representa um tipo que possui `n` elementos.
    - `Fin 0` ≃ ⊥ !
    - `Fin `  ≃ ⊤ !

```agda
data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
```

# Tipos finitos

- Provando `Fin 0 ≃ ⊥`: Fin 0 é um tipo vazio.

```agda
Fin0≃⊥ : Fin 0 ≃ ⊥
Fin0≃⊥
  = record {
       to = λ ()
    ; from = λ ()
    ; to∘from = λ () 
    ; from∘to = λ () }
```

# Tipos finitos

- Provando `Fin 1 ≃ ⊤`: Fin 1 é um conjunto unitário.

```agda
Fin1≃⊤ : Fin 1 ≃ ⊤
Fin1≃⊤
  = record {
      to = λ _ → tt
    ; from = λ _ → zero
    ; to∘from = λ {tt → refl}
    ; from∘to = λ {zero → refl} }
```

# Tipos finitos

- A partir do apresentado, podemos concluir que Fin n é um
tipo com n elementos.

- Relacionando Fin n com um Vec A n, podemos indexar listas
evitando problemas de acesso a posições inválidas.

```agda
nthV : ∀ {a}{A : Set a}{n} → Fin n → Vec A n → A
nthV zero      (x ∷ _)  = x
nthV (suc idx) (_ ∷ xs) = nthV idx xs
```

# Árvores Binárias de Busca

- Podemos representar invariantes sobre árvores binárias
de busca usando tipos dependentes.

- Indexamos a estrutura pelos limites superior e inferior
armazenados na árvore.

```agda
module BinaryTree {A : Set}
                  {_≤_ : Relation A}
                  (M : IsTotalOrder _≤_) where

  open IsTotalOrder M

  data Tree : A → A → Set where
    leaf : ∀ {l u} → l ≤ u → Tree l u
    node : ∀ {l l' u u'}(d : A) →
             Tree l' d →
             Tree d u' →
             l ≤ l'    →
             u' ≤ u    →
             Tree l u
```

# Árvores binárias de busca

- Busca de um valor

```agda
  search : ∀ {l u}(d : A) → Tree l u → Maybe (∃[ d' ] (d ≡ d'))
  search d (leaf x) = nothing
  search d (node d₁ t t₁ x x₁) with total d d₁
  ...| inj₁ d≤d₁  = {!!}
  ...| inj₂ d₁≤d2 = {!!}
```
