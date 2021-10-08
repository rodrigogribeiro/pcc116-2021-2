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
    ...| inj₁ x≤y = x ∷ y ∷ ys
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
    insert-sorted {.[]} empty = single
    insert-sorted {[ y ]}{x} single with total M x y
    ...| inj₁ x≤y = many x≤y single
    ...| inj₂ y≤x = many y≤x single
    insert-sorted {(y ∷ y' ∷  ys)}{x} (many y≤y' sxs) with total M x y
    ...| inj₁ x≤y = many x≤y (many y≤y' sxs)
    ...| inj₂ y≤x with total M x y' | insert-sorted {x = x} sxs
    ...   | inj₁ x≤y' | _ = many y≤x (many x≤y' sxs)
    ...   | inj₂ y'≤x | p = many y≤y' p

    isort-sorted : ∀ (xs : List A) → Sorted (isort xs)
    isort-sorted [] = empty
    isort-sorted (x ∷ xs) = insert-sorted (isort-sorted xs)
```

# Definições de permutações

```agda
  module permutation {A : Set}
                     {_≤_ : Relation A}
                     (M : IsTotalOrder _≤_) where

    open IsTotalOrder M public
    open isort-algorithm M

    data Perm : List A → List A → Set where
      empty : Perm [] []
      skip  : ∀ {x xs ys} → Perm xs ys
                          → Perm (x ∷ xs) (x ∷ ys)
      swap  : ∀ {x y xs} → Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)
      ptrans : ∀ {xs ys zs} → Perm xs ys
                            → Perm ys zs
                            → Perm xs zs

    Perm-refl : ∀ {xs} → Perm xs xs
    Perm-refl {[]} = empty
    Perm-refl {x ∷ xs} = skip Perm-refl

    Perm-sym : ∀ {xs ys} → Perm xs ys → Perm ys xs
    Perm-sym empty = empty
    Perm-sym (skip pxys) = skip (Perm-sym pxys)
    Perm-sym swap = swap
    Perm-sym (ptrans pxys pxys₁) = ptrans (Perm-sym pxys₁) (Perm-sym pxys)

    insert-perm : ∀ {xs ys x} → Perm xs ys → Perm (x ∷ xs) (insert x ys)
    insert-perm {.[]} {.[]} {x} empty = skip empty
    insert-perm {(y ∷ ys)} {(.y ∷ zs)} {x} (skip p) with total M x y
    ...| inj₁ x≤y = skip (skip p)
    ...| inj₂ y≤x = ptrans swap (skip (insert-perm p))
    insert-perm {x ∷ x' ∷ xs} {.x' ∷ .x ∷ ys} {z} swap with total M z x'
    ...| inj₁ z≤x' = skip swap
    ...| inj₂ x'≤z with total M z x
    ...    | inj₁ z≤x = Perm-sym (ptrans swap (skip swap))
    ...    | inj₂ x≤z = Perm-sym (ptrans swap (Perm-sym (ptrans swap (skip (ptrans swap (skip (insert-perm Perm-refl)))))))
    insert-perm {xs} {ys} {x} (ptrans p p₁) = ptrans (skip p) (insert-perm p₁)

    isort-perm : (xs : List A) → Perm xs (isort xs)
    isort-perm [] = empty
    isort-perm (x ∷ xs) = insert-perm (isort-perm xs)
```
