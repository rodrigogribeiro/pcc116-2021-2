---
title: Estudo de caso: Insertion sort
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

<!--
```agda
  module aula16 where

  open import Data.Biconditional.Biconditional
  open import Data.Biconditional.BiconditionalTheorems
  open import Data.Bool.Bool
  open import Data.Empty.Empty
  open import Data.Function.Function
  open import Data.List.List
  open import Data.List.Relation.Any
  open import Data.Sum.Sum
  open import Data.Unit.Unit

  open import Relation.Equality.Propositional
```
-->

# Objetivos

- Apresentação de definições sobre relações de
ordem.

- Implementação do algoritmo insertion sort

- Definição de um predicado para listas ordenadas
e a demonstração de que o insertion sort produz listas
ordenadas.

- Definição de um predicado para permutação de listas
e a demonstração de que o insertion sort produz uma
permutação da lista de entrada.

# Definições das relações

- Uma relação é uma função de dois argumentos de um tipo `A`.

```agda
  Relation : Set → Set₁
  Relation A = A → A → Set
```

# Definições das relações

- Propriedades de relações

```agda
  Reflexive : ∀ {A} → Relation A → Set
  Reflexive {A} _≤_ = ∀ {x} → x ≤ x

  AntiSymmetric : ∀ {A} → Relation A → Set
  AntiSymmetric {A} _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

  Transitive : ∀ {A} → Relation A → Set
  Transitive {A} _≤_ = ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

  Total : ∀ {A} → Relation A → Set
  Total {A} _≤_ = ∀ x y → x ≤ y ⊎ y ≤ x
```

# Relações de ordem

- Ordem parcial

```agda
  record IsPartialOrder {A : Set}(_≤_ : Relation A) : Set where
    field
      reflexive      : Reflexive _≤_
      anti-symmetric : AntiSymmetric _≤_
      transitive     : Transitive _≤_
```

# Relações de ordem

- Ordens totais.

```agda
  record IsTotalOrder {A : Set}(_≤_ : Relation A) : Set where
    field
      partial : IsPartialOrder _≤_
      total   : Total _≤_
```

# Definição do insertion sort

```agda
  module isort-algorithm {A : Set}
                         {_≤_ : Relation A}
                         (M : IsTotalOrder _≤_) where

    open IsTotalOrder M public

    insert : A → List A → List A
    insert x [] = [ x ]
    insert x (y ∷ ys) with total x y
    ...| inj₁ x≤y  = x ∷ y ∷ ys
    ...| inj₂ ¬x≤y = y ∷ insert x ys

    isort : List A → List A
    isort []       = []
    isort (x ∷ xs) = insert x (isort xs)
```

# Definição do predicado de listas ordenadas

```agda
  module sorted {A : Set}{_≤_ : Relation A}(M : IsTotalOrder _≤_) where

    open IsTotalOrder    M public
    open isort-algorithm M public

    data Sorted : List A → Set where
      empty : Sorted []
      single : ∀ {x} → Sorted [ x ]
      many : ∀ {y x xs} → y ≤ x
                        → Sorted (x ∷ xs)
                        → Sorted (y ∷ x ∷ xs)

    insert-sorted : ∀ {xs}{x : A} → Sorted xs → Sorted (insert x xs)
    insert-sorted empty = single
    insert-sorted {xs = [ x ]}{y} single with total M y x
    ...| inj₁ y≤x = many y≤x single
    ...| inj₂ x≤y = many x≤y single
    insert-sorted {x ∷ x' ∷ xs}{y}(many x≤x' sxs) with total M y x
    ...| inj₁ y≤x = many y≤x (many x≤x' sxs)
    ...| inj₂ x≤y with total M y x' | insert-sorted {x = y} sxs
    ...    | inj₁ y≤x' | _    = many x≤y (many y≤x' sxs)
    ...    | inj₂ x'≤y | sxs' = many x≤x' sxs'

    isort-sorted : ∀ (xs : List A) → Sorted (isort xs)
    isort-sorted []       = empty
    isort-sorted (x ∷ xs) = insert-sorted (isort-sorted xs)
```

# Definições de permutações

```agda
  module permutation {A : Set}
                     {_≤_ : Relation A}
                     (M : IsTotalOrder _≤_) where

    open IsTotalOrder M public
    open isort-algorithm M

    infix 4 _≈_

    data _≈_ : List A → List A → Set where
      empty : [] ≈ []
      skip  : ∀ {x xs ys} → xs ≈ ys
                          → (x ∷ xs) ≈ (x ∷ ys)
      swap  : ∀ {x y xs} → (x ∷ y ∷ xs) ≈ (y ∷ x ∷ xs)
      ≈-trans : ∀ {xs ys zs} → xs ≈ ys
                             → ys ≈ zs
                             → xs ≈ zs

    ≈-refl : ∀ {xs} → xs ≈ xs
    ≈-refl {[]} = empty
    ≈-refl {x ∷ xs} = skip (≈-refl {xs})

    ≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
    ≈-sym empty = empty
    ≈-sym (skip xs≈ys) = skip (≈-sym xs≈ys)
    ≈-sym swap = swap
    ≈-sym (≈-trans xs≈ys xs≈ys₁) = ≈-trans (≈-sym xs≈ys₁) (≈-sym xs≈ys)

    insert-perm : ∀ {xs ys x} → xs ≈ ys → (x ∷ xs) ≈ (insert x ys)
    insert-perm empty = ≈-refl
    insert-perm {xs = z ∷ zs}{x = x}(skip xs≈ys) with total M x z
    ...| inj₁ x≤z = skip (skip xs≈ys)
    ...| inj₂ z≤x = ≈-trans swap (skip (insert-perm xs≈ys))
    insert-perm {xs = x ∷ x' ∷ xs} {x = y} swap with total M y x'
    ...| inj₁ y≤x' = skip swap
    ...| inj₂ x'≤y with total M y x
    ...    | inj₁ y≤x = ≈-sym (≈-trans swap (skip swap))
    ...    | inj₂ x≤y = ≈-trans swap (≈-sym (≈-trans swap (skip (≈-sym (≈-trans swap (skip (insert-perm ≈-refl)))))))
    insert-perm (≈-trans xs≈ys xs≈ys₁) = ≈-trans (skip xs≈ys) (insert-perm xs≈ys₁)

    isort-perm : (xs : List A) → xs ≈ (isort xs)
    isort-perm [] = empty
    isort-perm (x ∷ xs) = insert-perm (isort-perm xs)
```
