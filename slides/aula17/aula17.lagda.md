---
title: Programação com tipos dependentes - Parte I
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
open import Data.List.List hiding (map)
open import Data.List.Relation.All
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Nat.Le renaming ( _≤_       to _≤N_
                                 ; ≤-refl    to ≤N-refl
                                 ; ≤-antisym to ≤N-antisym
                                 ; ≤-trans   to ≤N-trans
                                 )
open import Data.Sum.Sum
open import Data.Sigma.Sigma
open import Data.Unit.Unit

open import Relation.Decidable.Dec
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
parity = {!!}
```

- Observe que o casamento de padrão sobre `parity n`
especializou o padrão `n` para o valor esperado em
cada caso.
* Caso even k, então n = k * 2
* Caso odd k,  então n = 1 + k * 2


# Casamento de padrão com tipos dependentes

- Usando `parity`, podemos construir uma função
para o obter para dividir um número natural por
2 de maneira simples.

```agda
half : ℕ → ℕ
half = {!!}
```

# Casamento de padrão com tipos dependentes

- Outra aplicação interessante: identificar o primeiro
elemento de uma lista que satisfaz um predicado.

```agda
data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A)       →
                     T (p y)         →
                     (ys : List A)   → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs}                 →
                All (T ∘ not ∘ p) xs → Find p xs
```

# Casamento de padrão com tipos dependentes

- Definição da função `find`

```agda
find : ∀ {A}(p : A → Bool)(xs : List A) → Find p xs
find = {!!}
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
       to     = λ ()
    ; from    = λ ()
    ; to∘from = λ () 
    ; from∘to = λ () }
```

# Tipos finitos

- Provando `Fin 1 ≃ ⊤`: Fin 1 é um conjunto unitário.

```agda
Fin1≃⊤ : Fin 1 ≃ ⊤
Fin1≃⊤
  = record {
      to      = λ _ → tt
    ; from    = λ _ → zero
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

- Isso garantirá que as árvores atenderão sempre a propriedade
de árvore de busca.

- A seguir, vamos definir a função `!` para recuperar um valor
a ser inferido pelo mecanismo de _instance arguments_ de Agda.

```agda
variable A : Set

! : {{ x : A }} → A
! {{x}} = x
```

- Vamos usar instances para inferência de deduções sobre relações de ordem.

- Primeiro, vamos automatizar um teste de igualdade.

```agda
variable n m : ℕ

_≡ᵇ_ : ℕ → ℕ → Bool
zero ≡ᵇ zero = true
suc _ ≡ᵇ zero = false
zero ≡ᵇ suc _ = false
suc n ≡ᵇ suc m = n ≡ᵇ m

instance
  ≡-dec : {p : T (n ≡ᵇ m)} → n ≡ m
  ≡-dec {n = zero} {m = zero} = refl
  ≡-dec {n = suc n} {m = suc m}{p = p} = cong suc (≡-dec {p = p})

_ : 200 ≡ 200
_ = !
```

```agda
_<ᵇ_ : ℕ → ℕ → Bool
_ <ᵇ zero = false
zero <ᵇ suc _ = true
suc n <ᵇ suc m = n <ᵇ m

instance
  ≤-dec : {p : T (n <ᵇ suc m)} → n ≤N m
  ≤-dec {n = zero} {m = m} = z≤n
  ≤-dec {n = suc n} {m = suc m} {p = p}
    = s≤s (≤-dec {p = p})

_ : 9000 ≤N 19000
_ = !
```

- O mecanismo de instances permite que registros Agda
funcionem como uma forma "pobre" de type classes.


```agda
record Eq (A : Set) : Set₁ where
  field
    _==_    : A → A → Set
    ≡-refl  : Reflexive  _==_
    ≡-sym   : Symmetric  _==_
    ≡-trans : Transitive _==_

open Eq {{...}}

instance
  Eq-ℕ : Eq ℕ
  _==_    {{Eq-ℕ}} = _≡_ {A = ℕ}
  ≡-refl  {{Eq-ℕ}} = refl
  ≡-sym   {{Eq-ℕ}} = sym
  ≡-trans {{Eq-ℕ}} = trans

record Ord (A : Set) : Set₁ where
  field
    _≤_       : A → A → Set
    ≤-refl    : Reflexive _≤_
    ≤-antisym : AntiSymmetric _≤_
    ≤-trans   : Transitive _≤_

  _≥_ : A → A → Set
  x ≥ y = y ≤ x

open Ord {{...}} public
```

- Instance para Ord ℕ

```agda
instance
  Ord-ℕ : Ord ℕ
  _≤_ {{Ord-ℕ}}       = _≤N_
  ≤-refl {{Ord-ℕ}}    = ≤N-refl
  ≤-antisym {{Ord-ℕ}} = ≤N-antisym
  ≤-trans {{Ord-ℕ}}   = ≤N-trans
```

- Definindo uma classe para testes sobre valores.

```agda
variable x y : A

data Tri {{_ : Ord A}} : A → A → Set where
  less    : {{x≤y : x ≤ y}} → Tri x y
  equal   : {{x≡y : x ≡ y}} → Tri x y
  greater : {{x≥y : x ≥ y}} → Tri x y

record Compare (A : Set) : Set₁ where
  field
    {{Ord-A}} : Ord A
    compare   : (x y : A) → Tri x y

open Compare {{...}} public
```

- Exemplo: instância de Compare para ℕ

```agda
triℕ : (x y : ℕ) → Tri x y
triℕ zero zero = equal
triℕ zero (suc y) = less
triℕ (suc x) zero = greater
triℕ (suc x) (suc y) with triℕ x y
...| less {{x≤y}} = less {{x≤y = s≤s x≤y}}
...| equal {{ x≡y }} = equal {{x≡y = cong suc x≡y}}
...| greater {{x≥y}} = greater {{ x≥y = s≤s x≥y }}

instance
  Compare-ℕ : Compare ℕ
  Ord-A   {{Compare-ℕ}} = Ord-ℕ
  compare {{Compare-ℕ}} = triℕ
```


- Agora, vamos completar a ordem parcial com elementos
para representar o máximo e mínimo sobre o tipo A.

```agda
data [_]∞ (A : Set) : Set where
  -∞ : [ A ]∞
  ⟨_⟩ : A → [ A ]∞
  +∞ : [ A ]∞
```

- Definindo uma relação de ordem sobre o tipo [_]∞:

```agda
module Ord-[]∞ {A : Set}{{ A-≤ : Ord A }} where

  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ : ∀ {x} → -∞ ≤∞ x
    ⟨⟩-≤  : ∀ { x y : A} → x ≤ y → ⟨ x ⟩ ≤∞ ⟨ y ⟩
    +∞-≤ : ∀ {x} → x ≤∞ +∞
```

- A relação ≤∞ é reflexiva

```agda
  []∞-refl : Reflexive _≤∞_
  []∞-refl { -∞} = -∞-≤
  []∞-refl {⟨ x ⟩} = ⟨⟩-≤ ≤-refl
  []∞-refl {+∞} = +∞-≤
```

- A relação ≤∞ é transitiva

```agda
  []∞-trans : Transitive _≤∞_
  []∞-trans -∞-≤      _          = -∞-≤
  []∞-trans (⟨⟩-≤ x≤y) (⟨⟩-≤ y≤z) = ⟨⟩-≤ (≤-trans x≤y y≤z)
  []∞-trans _          +∞-≤      = +∞-≤
```

- A relação ≤∞ é antisimétrica

```agda
  []∞-antisym : AntiSymmetric _≤∞_
  []∞-antisym -∞-≤ -∞-≤ = refl
  []∞-antisym (⟨⟩-≤ x≤y) (⟨⟩-≤ y≤z) = cong ⟨_⟩ (≤-antisym x≤y y≤z)
  []∞-antisym +∞-≤ +∞-≤ = refl
```

- Definição da instância de Ord

```agda
  instance
    Ord-[]∞ : {{_ : Ord A}} → Ord [ A ]∞
    _≤_       {{Ord-[]∞}} = _≤∞_
    ≤-refl    {{Ord-[]∞}} = []∞-refl
    ≤-trans   {{Ord-[]∞}} = []∞-trans
    ≤-antisym {{Ord-[]∞}} = []∞-antisym

open Ord-[]∞ public
```

- Vamos definir alguns lemas como instâncias para
serem utilizados automaticamente por Agda.

```agda
module Lemmas {{ _ : Ord A }} where

  instance
    -∞-≤-any : {y : [ A ]∞} → -∞ ≤ y
    -∞-≤-any = -∞-≤

    +∞-≤-any : {y : [ A ]∞} → y ≤ +∞
    +∞-≤-any = +∞-≤

    ⟨⟩-≤-≤ : {x y : A} {{x≤y : x ≤ y}} → ⟨ x ⟩ ≤ ⟨ y ⟩
    ⟨⟩-≤-≤ {{x≤y = x≤y}} = ⟨⟩-≤ x≤y

open Lemmas

data Tree (A : Set){{_ : Ord A}}(l u : [ A ]∞) : Set where
  leaf : {{ l≤u : l ≤ u }} → Tree A l u
  node : (v : A)         →
         Tree A l ⟨ v ⟩  →
         Tree A ⟨ v ⟩ u  →
         Tree A l u
```

- O tipo Tree garante, estaticamente, o invariante de árvores binárias
de busca.

```agda
_ : Tree ℕ -∞ +∞
_ = node 40 (node 10 leaf leaf)
            (node 70 leaf leaf)
```

- No valor acima, o mecanismo de _instance search_ preenche, automaticamente,
as demonstrações que garantem o invarianate de árvores binárias.

- Como exemplo, consider o valor de árvore com as deduções
explicitamente preenchidas

```agda
_ : Tree ℕ -∞ +∞
_ = node 40 (node 10 (leaf {{l≤u = -∞≤10}})
                     (leaf {{l≤u = 10≤40}}))
            (node 70 (leaf {{l≤u = 40≤70}})
                     (leaf {{l≤u = 70≤+∞}}))
      where
        -∞≤10 : -∞ ≤ ⟨ 10 ⟩
        -∞≤10 = !

        10≤40 : ⟨ 10 ⟩ ≤ ⟨ 40 ⟩
        10≤40 = !

        40≤70 : ⟨ 40 ⟩ ≤ ⟨ 70 ⟩
        40≤70 = !

        70≤+∞ : ⟨ 70 ⟩ ≤ +∞
        70≤+∞ = !
```

- Tendo definido o tipo de árvores binárias, podemos
implementar operações que preservam esse invariante.


```agda
module Search {{_ : Compare A}} where

  infix 4 _∈_

  data _∈_ {l u}(x : A) : (t : Tree A l u) → Set where
    here  : ∀ {t₁ t₂} → x ≡ y  → x ∈ node y t₁ t₂
    left  : ∀ {t₁ t₂} → x ∈ t₁ → x ∈ node y t₁ t₂
    right : ∀ {t₁ t₂} → x ∈ t₂ → x ∈ node y t₁ t₂

  ∈-inv : ∀ {l u x y}
            {t₁ : Tree A l ⟨ y ⟩}
            {t₂ : Tree A ⟨ y ⟩ u} →
            x ∈ node y t₁ t₂      →
            x ≡ y ⊎ x ∈ t₁ ⊎ x ∈ t₂
  ∈-inv (here x) = inj₁ x
  ∈-inv (left p) = inj₂ (inj₁ p)
  ∈-inv (right p) = inj₂ (inj₂ p)
```

- A função para busca em uma árvore binária
possui uma definição quase imediata.

```agda
  search : ∀ {l u}(x : A)(t : Tree A l u) → Maybe (x ∈ t)
  search x leaf = nothing
  search x (node v tl tr) with compare x v
  ...| equal   = just (here !)
  ...| less    = map left (search x tl)
  ...| greater = map right (search x tr)
```

- A função para inserção é definida em um módulo
parametrizado por uma "classe" para comparação.


```agda
module Insert {{_ : Compare A}} where

  insert : ∀ {l u}(x : A)(t : Tree A l u)           →
             {{l≤x : l ≤ ⟨ x ⟩}}{{x≤u : ⟨ x ⟩ ≤ u}} →
             Tree A l u
  insert x leaf = node x leaf leaf
  insert x (node y tl tr) with compare x y
  ...| less    = node y (insert x tl) tr
  ...| equal   = node y tl tr
  ...| greater = node y tl (insert x tr)
```


# Conclusão

- Nesta aula, apresentamos como tipos dependentes podem
codificar invariantes de estruturas de dados de maneira
natural.

- O uso de _instance arguments_ provê uma forma simples
de automação de provas em Agda.

# Referências.

- McBride, Connor. How to keep your neighbours in order,
ICFP 2014.
