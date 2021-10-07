---
title: Listas em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

```agda
  module aula16 where

  open import Data.Empty.Empty
  open import Data.List.List
  open import Data.Nat.Nat
  open import Data.Unit.Unit

  open import Relation.Decidable.Dec
```

# Objetivos

## Objetivos

- Formalizar o algoritmo de ordenação insertion sort.

- A correção envolve demonstrar duas propriedades:
  - O algoritmo retorna uma lista ordenada.
  - A lista retornada é uma permutação da lista original.

- Para isso, vamos parametrizar o desenvolvimento por um
  teste de ordenação sobre elementos.

```agda
  module insertion-sort {l l'}{A : Set l}
                        {_≤_ : A → A → Set l'}
                        (≤-refl : ∀ {x} → x ≤ x)
                        (≤-contra : ∀ {x y} → ¬ (x ≤ y) → y ≤ x)
                        (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
                        (_≤?_ : ∀ (x y : A) → Dec (x ≤ y)) where
```

# Insertion sort

## Insertion sort

- Ordenação por inserção utiliza como rotina a inserção
de forma ordenada em uma lista.

```agda
     insert : A → List A → List A
     insert x [] = [ x ]
     insert x (y ∷ ys) with x ≤? y
     ...| yes x≤y = x ∷ y ∷ ys
     ...| no ¬x≤y = y ∷ insert x ys
```

## Insertion sort

- Utilizando a função `insert`, a definição do insertion
sort é imediata por recursão.

```agda
     isort : List A → List A
     isort [] = []
     isort (x ∷ xs) = insert x (isort xs)
```

## Insertion sort

- Tendo definido o algoritmo, como mostrar que ele é
correto?

- Para mostrar que o algoritmo insertion sort é correto
devemos:
    - Mostrar que ele retorna uma lista ordenada.
    - Que a lista retornada é uma permutação da entrada.

## Insertion sort

- Para definir um predicado para representar
listas ordenadas, primeiro vamos definir um
que especifica quando um valor é menor que
todos em uma lista.

```agda
     data _<*_ (x : A) : List A → Set l' where
       []  : x <* []
       _∷_ : ∀ {y ys} → x ≤ y   →
                         x <* ys →
                         x <* (y ∷ ys)
```

## Insertion sort

- Exemplo

```agda

```

## Insertion sort

- Predicado para representar listas ordenadas.

```agda
     data Sorted : List A → Set l' where
       []  : Sorted []
       _∷_ : ∀ {x xs} → x <* xs   →
                         Sorted xs →
                         Sorted (x ∷ xs)
```

## Insertion sort

- Relacionando insert e <*

```agda
     <*-cons : ∀ {x y ys} → x ≤ y → y <* ys → x <* ys
     <*-cons x≤y [] = []
     <*-cons x≤y (x ∷ y<*ys)
       = (≤-trans x≤y x) ∷ <*-cons x≤y y<*ys

     <*-insert : ∀ {x y xs} → y ≤ x → y <* xs → y <* insert x xs
     <*-insert y≤x [] = y≤x ∷ []
     <*-insert {x}{y} y≤x (_∷_ {y = z} y<z y<*xs) with x ≤? z
     ...| yes k = y≤x ∷ (y<z ∷ y<*xs)
     ...| no ¬k = y<z ∷ (<*-insert y≤x y<*xs)
```


## Insertion sort

- Provando que `insert` preserva a propriedade
`Sorted`

```agda
     insert-sorted : ∀ {x xs} → Sorted xs → Sorted (insert x xs)
     insert-sorted [] = [] ∷ []
     insert-sorted {x} (_∷_ {x = y} z ys) with x ≤? y
     ...| yes p = (p ∷ (<*-cons p z)) ∷ (z ∷ ys)
     ...| no ¬p = <*-insert (≤-contra ¬p) z ∷ (insert-sorted ys)
```

## Insertion sort

- Provando que isort retorna uma lista ordenada

```agda
     isort-sorted : ∀ (xs : List A) → Sorted (isort xs)
     isort-sorted [] = []
     isort-sorted (x ∷ xs) = insert-sorted (isort-sorted xs)
```

## Insertion sort

- Para concluir a demonstração de correção, falta mostrar
que o algoritmo retorna uma permutação da lista fornecida
como entrada.

- Para isso, vamos criar uma relação para denotar permutações
de uma lista.

## Insertion sort

- A relação x ▷ ys ≈ zs denota que a lista zs é igual a
a inserção de x em algum ponto da lista ys.

```agda
     data _▷_≈_ : A → List A → List A → Set l where
       here : ∀ {x xs} → x ▷ xs ≈ (x ∷ xs)
       there : ∀ {x y xs xss} → x ▷ xs ≈ xss
                              → x ▷ (y ∷ xs) ≈ (y ∷ xss)
```

## Insertion sort

- Usando a relação x ▷ xs ≈ ys, podemos definir a noção
de permutação entre duas listas.

```agda
     data Permutation : List A → List A → Set l where
       []  : Permutation [] []
       _∷_ : ∀ {x xs ys xys} → x ▷ ys ≈ xys
                             → Permutation xs ys
                             → Permutation (x ∷ xs) xys
```

## Insertion sort

- Permutações são reflexivas

```agda
     Permutation-refl : ∀ xs → Permutation xs xs
     Permutation-refl [] = []
     Permutation-refl (x ∷ xs) = here ∷ Permutation-refl xs
```


## Insertion sort

```agda
     insert-permutation : ∀ {x} xs → Permutation (x ∷ xs) (insert x xs)
     insert-permutation [] = here ∷ []
     insert-permutation {x}(y ∷ ys) with x ≤? y
     ...| yes x≤y = Permutation-refl (x ∷ y ∷ ys)
     ...| no ¬x≤y = {!!} ∷ {!!}
```
