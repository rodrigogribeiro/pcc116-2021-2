---
title: Listas em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

# Objetivos

<!--
```agda
module aula15 where

  open import Basics.Level

  open import Data.Bool.Bool
  open import Data.Empty.Empty
  open import Data.Function.Function
  open import Data.Biconditional.Biconditional
  open import Data.Nat.Nat
  open import Data.Nat.NatTheorems
  open import Data.Nat.Le
  open import Data.Product.Product renaming ( _,_ to _:,:_)
  open import Data.Unit.Unit

  open import Relation.Decidable.Dec hiding (Decidable)
  open import Relation.Equality.Propositional

  _≥_ : ℕ → ℕ → Bool
  zero ≥ zero = true
  zero ≥ suc m = false
  suc n ≥ zero = true
  suc n ≥ suc m = n ≥ m
```
-->

## Objetivos

  - Definir o tipo de listas polimórficas.
  - Provar alguns resultados sobre funções
    envolvendo listas.

# Listas

## Listas

- Um dos tipos de dados mais utilizados em
  linguagens funcionais são as listas.

- Essa é uma tradição que existe desde a
  linguagem Lisp e seus dialetos.

## Listas

- A definição de listas em Agda é feita
  pelo seguinte tipo indutivo.

```agda
  infixr 5 _∷_

  data List {a}(A : Set a) : Set a where
    []  : List A
    _∷_ : A → List A → List A
```

## Listas

- Sintaxe especial para listas.

```agda
  pattern [_] z = z ∷ []
  pattern [_,_] y z = y ∷ z ∷ []
  pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
  pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
  pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
  pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```

## Listas

- Operações básicas sobre listas.

```agda
  length : ∀ {a}{A : Set a} → List A → ℕ
  length [] = 0
  length (x ∷ xs) = 1 + (length xs)

  _ : length [ 1 , 2 ] ≡ 2
  _ = begin
        length (1 ∷ [ 2 ])          ≡⟨⟩
        1 + length [ 2 ]            ≡⟨⟩
        1 + (1 + length {A = ℕ} []) ≡⟨⟩
        1 + (1 + 0)                 ≡⟨⟩
        2
      ∎
```

## Listas

- Concatenação

```agda
  infixr 5 _++_

  _++_ : ∀ {a}{A : Set a} → List A → List A → List A
  [] ++ ys       = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

## Listas

- Exemplo

```agda
  _ : [ 1 , 2 ] ++ [ 3 ] ≡ [ 1 , 2 , 3 ]
  _ = begin
        [ 1 , 2 ] ++ [ 3 ]      ≡⟨⟩
        1 ∷ ([ 2 ] ++ [ 3 ])    ≡⟨⟩
        1 ∷ (2 ∷ ([] ++ [ 3 ])) ≡⟨⟩
        1 ∷ 2 ∷ [ 3 ]           ≡⟨⟩
        [ 1 , 2 , 3 ]
      ∎
```

## Listas

- Um teorema simples.

```agda
  length-++ : ∀ {a}{A : Set a}(xs ys : List A) →
              length (xs ++ ys) ≡ length xs + length ys
  length-++ [] ys       = refl
  length-++ (x ∷ xs) ys
    = begin
        length ((x ∷ xs) ++ ys)
      ≡⟨⟩
        length (x ∷ (xs ++ ys))
      ≡⟨⟩
        suc (length (xs ++ ys))
      ≡⟨ cong suc (length-++ xs ys) ⟩
        suc (length xs + length ys)
      ≡⟨⟩
        length (x ∷ xs) + length ys
      ∎

```

## Listas

- A função `map`.

```agda
  map : ∀ {a b}{A : Set a}{B : Set b} →
          (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs
```

## Listas

- Exemplo

```agda
  _ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
  _ = begin
        map suc [ 0 , 1 , 2 ]
      ≡⟨⟩
        suc 0 ∷ map suc [ 1 , 2 ]
      ≡⟨⟩
        1 ∷ (suc 1 ∷ map suc [ 2 ])
      ≡⟨⟩
        1 ∷ 2 ∷ (suc 2 ∷ map suc [])
      ≡⟨⟩
        1 ∷ 2 ∷ 3 ∷ []
      ≡⟨⟩
        [ 1 , 2 , 3 ]
      ∎
```

## Listas

- Relacionando `map` e `++`

```agda
  map-++ : ∀ {a b}{A : Set a}{B : Set b}
             (f : A → B)(xs ys : List A) →
             map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f [] ys = refl
  map-++ f (x ∷ xs) ys
    = begin
        map f ((x ∷ xs) ++ ys)
      ≡⟨⟩
        map f (x ∷ (xs ++ ys))
      ≡⟨⟩
        f x ∷ map f (xs ++ ys)
      ≡⟨ cong (f x ∷_) (map-++ f xs ys) ⟩
        f x ∷ (map f xs ++ map f ys)
      ≡⟨⟩
        map f (x ∷ xs) ++ map f ys
      ∎
```

## Listas

- Relacionando `map` e `∘`:

```agda
  map-∘ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
            {g : B → C}{f : A → B}(xs : List A) →
            (map g ∘ map f) xs ≡ map (g ∘ f) xs
  map-∘ [] = refl
  map-∘ {g = g}{f = f}(x ∷ xs)
    = begin
        (map g ∘ map f) (x ∷ xs)
      ≡⟨⟩
        map g (map f (x ∷ xs))
      ≡⟨⟩
        map g (f x ∷ (map f xs))
      ≡⟨⟩
        g (f x) ∷ map g (map f xs)
      ≡⟨⟩
        (g ∘ f) x ∷ ((map g ∘ map f) xs)
      ≡⟨ cong ((g ∘ f) x ∷_) (map-∘ xs)  ⟩
        (g ∘ f) x ∷ map (g ∘ f) xs
      ≡⟨⟩
        map (g ∘ f) (x ∷ xs)
      ∎
```

## Listas

- Invertendo uma lista, versão ineficiente.

```agda
  reverse : ∀ {a}{A : Set a} → List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ++ [ x ]
```

## Listas

- Exemplo

```agda
  _ : reverse [ 1 , 2 ] ≡ [ 2 , 1 ]
  _ = begin
        reverse [ 1 , 2 ]
      ≡⟨⟩
        reverse [ 2 ] ++ [ 1 ]
      ≡⟨⟩
        (reverse [] ++ [ 2 ]) ++ [ 1 ]
      ≡⟨⟩
        ([] ++ [ 2 ]) ++ [ 1 ]
      ≡⟨⟩
        [ 2 , 1 ]
      ∎
```

## Listas

- `reverse` preserva `length`

```agda
  reverse-length : ∀ {a}{A : Set a}(xs : List A) →
                   length xs ≡ length (reverse xs)
  reverse-length [] = refl
  reverse-length (x ∷ xs)
    = begin
        length (x ∷ xs)
      ≡⟨⟩
        suc (length xs)
      ≡⟨ cong suc (reverse-length xs) ⟩
        suc (length (reverse xs))
      ≡⟨⟩
        1 + length (reverse xs)
      ≡⟨ +-comm 1 (length (reverse xs)) ⟩
        length (reverse xs) + 1
      ≡⟨⟩
        length (reverse xs) + length [ x ]
      ≡⟨ sym (length-++ (reverse xs) [ x ]) ⟩
        length (reverse xs ++ [ x ])
      ≡⟨⟩
        length (reverse (x ∷ xs))
      ∎
```

## Listas

- Relacionando `reverse` e `++`

```agda
  []-++-right : ∀ {a}{A : Set a}(xs : List A) →
                xs ++ [] ≡ xs
  []-++-right [] = refl
  []-++-right (x ∷ xs)
    = begin
         (x ∷ xs) ++ []
      ≡⟨⟩
         x ∷ (xs ++ [])
      ≡⟨ cong (x ∷_) ([]-++-right xs) ⟩
         x ∷ xs
      ∎

  postulate ++-assoc : ∀ {a}{A : Set a}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

  reverse-++ : ∀ {a}{A : Set a}(xs ys : List A) →
              reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
  reverse-++ [] ys = sym ([]-++-right (reverse ys))
  reverse-++ (x ∷ xs) ys
    = begin
        reverse ((x ∷ xs) ++ ys)
      ≡⟨⟩
        reverse (x ∷ (xs ++ ys))
      ≡⟨⟩
        reverse (xs ++ ys) ++ [ x ]
      ≡⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
        (reverse ys ++ reverse xs) ++ [ x ]
      ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
        reverse ys ++ (reverse xs ++ [ x ])
      ≡⟨⟩
        reverse ys ++ reverse (x ∷ xs)
      ∎
```

## Listas

- Operador `foldr`

```agda
  foldr : ∀ {a b}{A : Set a}{B : Set b} →
            (A → B → B) → B → List A → B
  foldr _ v []       = v
  foldr f v (x ∷ xs) = f x (foldr f v xs)
```

## Listas

- Exemplo

```agda
  _ : foldr _+_ 0 [ 1 , 2 , 3 ] ≡ 6
  _ = begin
        foldr _+_ 0 [ 1 , 2 , 3 ]
      ≡⟨⟩
        1 + (foldr _+_ 0 [ 2 , 3 ])
      ≡⟨⟩
        1 + (2 + (foldr _+_ 0 [ 3 ]))
      ≡⟨⟩
        1 + (2 + (3 + (foldr _+_ 0 [])))
      ≡⟨⟩
        1 + (2 + (3 + 0))
      ≡⟨⟩
        6
      ∎
```

## Listas

- Operador `fold`

```agda
  foldl : ∀ {a b}{A : Set a}{B : Set b} →
            (B → A → B) → B → List A → B
  foldl _ v []       = v
  foldl f v (x ∷ xs) = foldl f (f v x) xs
```

## Listas

- Exemplo

```agda
  _ : foldl _+_ 0 [ 1 , 2 , 3 ] ≡ 6
  _ = begin
        foldl _+_ 0 [ 1 , 2 , 3 ]
      ≡⟨⟩
        foldl _+_ (0 + 1) [ 2 , 3 ]
      ≡⟨⟩
        foldl _+_ ((0 + 1) + 2) [ 3 ]
      ≡⟨⟩
        foldl _+_ (((0 + 1) + 2) + 3) []
      ≡⟨⟩
         ((0 + 1) + 2) + 3
      ≡⟨⟩
         6
      ∎
```

## Listas

- Quando o resultado de `foldl f v ≡ foldr f v`?

- O resultado será o mesmo quando `f` e `v` formarem
um _monóide_.

## Listas

- Definição de monóide:

```agda
  record IsMonoid {a}{A : Set a}(_⊕_ : A → A → A)(e : A) : Set a where
    field
      assoc : ∀ {x y z : A} → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
      identityˡ : ∀ {x} → e ⊕ x ≡ x
      identifyʳ : ∀ {x} → x ⊕ e ≡ x
```

## Listas

- A adição e 0 formam o monóide

```agda
  +-Monoid : IsMonoid _+_ 0
  +-Monoid
    = record { assoc = λ {x}{y}{z} → +-assoc x y z
             ; identityˡ = refl
             ; identifyʳ = λ {x} → +-zero-right x }
```

## Listas

- Relacionando `foldr` e `++`

```agda
  foldr-++ : ∀ {a}{A : Set a}
               {_⊕_ : A → A → A}{e : A} →
               IsMonoid _⊕_ e  →
               (xs ys : List A) →
               foldr _⊕_ e (xs ++ ys) ≡ foldr _⊕_ (foldr _⊕_ e ys) xs
  foldr-++ M [] ys = refl
  foldr-++ {_⊕_ = _⊕_}{e = e} M (x ∷ xs) ys
    = begin
        foldr _⊕_ e ((x ∷ xs) ++ ys)
      ≡⟨⟩
        foldr _⊕_ e (x ∷ (xs ++ ys))
      ≡⟨⟩
        x ⊕ (foldr _⊕_ e (xs ++ ys))
      ≡⟨ cong (x ⊕_) (foldr-++ M xs ys) ⟩
        x ⊕ (foldr _⊕_ (foldr _⊕_ e ys) xs)
      ≡⟨⟩
        foldr _⊕_ (foldr _⊕_ e ys) (x ∷ xs)
      ∎
```


## Listas

- Função `filter`

```agda
  filter : ∀ {a}{A : Set a} → (A → Bool) → List A → List A
  filter p []       = []
  filter p (x ∷ xs) = let r = filter p xs
                      in if p x then x ∷ r else r
```

## Listas

- Exemplo

```agda
  _ : filter (_≥ 2) [ 1 , 2 , 5 , 1 , 4 ] ≡ [ 2 , 5 , 4 ]
  _ = begin
        filter (_≥ 2) [ 1 , 2 , 5 , 1 , 4 ]
      ≡⟨⟩
        filter (_≥ 2) [ 2 , 5 , 1 , 4 ]
      ≡⟨⟩
        2 ∷ filter (_≥ 2) [ 5 , 1 , 4 ]
      ≡⟨⟩
        2 ∷ 5 ∷ filter (_≥ 2) [ 1 , 4 ]
      ≡⟨⟩
        2 ∷ 5 ∷ filter (_≥ 2) [ 4 ]
      ≡⟨⟩
        2 ∷ 5 ∷ 4 ∷ filter (_≥ 2) []
      ≡⟨⟩
        [ 2 , 5 , 4 ]
      ∎
```

## Listas

- Exemplo

```agda
  filter-length : ∀ {a}{A : Set a}{p : A → Bool}(xs : List A) →
                  length (filter p xs) ≤ length xs
  filter-length [] = z≤n
  filter-length {p = p}(x ∷ xs) with p x
  ...| true = s≤s (filter-length xs)
  ...| false = ≤-suc (filter-length xs)
```

## Listas

- O predicado `All` denota que uma propriedade é válida
para todos os elementos de uma lista.

```agda
  data All {a b}{A : Set a}(P : A → Set b) : List A → Set (a ⊔ b) where
    []  : All P []
    _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)
```

## Listas

- Exemplo

```agda
  _ : All (λ x → T (x ≥ 2)) [ 3 , 4 , 7 ]
  _ = tt ∷ tt ∷ (tt ∷ [])
```


## Listas

- Relacionando `All` e `++`

```agda
  All-++-left : ∀ {a}{A : Set a}{P : A → Set a}(xs ys : List A) →
             All P (xs ++ ys) →  (All P xs × All P ys)
  All-++-left [] ys p = [] :,: p
  All-++-left (x ∷ xs) ys (px ∷ pxs) with All-++-left xs ys pxs
  ...| pxs' :,: pys = px ∷ pxs' :,: pys

  All-++-right : ∀ {a}{A : Set a}{P : A → Set a}(xs ys : List A) →
    (All P xs × All P ys) → All P (xs ++ ys)
  All-++-right .[] ys ([] :,: pys) = pys
  All-++-right (x ∷ xs) ys (px ∷ pxs :,: pys)
    with All-++-right xs ys (pxs :,: pys)
  ...| pxys = px ∷ pxys

  All-++ : ∀ {a}{A : Set a}{P : A → Set a}(xs ys : List A) →
             All P (xs ++ ys) ⇔ (All P xs × All P ys)
  All-++ xs ys
    = record {
        to = All-++-left xs ys
      ; from = All-++-right xs ys }
```


## Listas

- Indicando que uma propriedade é válida para algum
elemento de uma lista.

```agda
  data Any {a b}{A : Set a}(P : A → Set b) : List A → Set (a ⊔ b) where
    here  : ∀ {x xs} → P x → Any P (x ∷ xs)
    there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)
```

## Listas

- Exemplo

```agda
  _ : Any (_≡ 2) [ 1 , 2 , 3 , 2 ]
  _ = there (there (there (here refl)))
```

## Listas

- Predicado de pertinência em uma lista.

```agda
  infix 4 _∈_

  _∈_ : ∀ {a}{A : Set a} → A → List A → Set a
  x ∈ xs = Any (x ≡_) xs
```

## Listas

- Exemplo

```agda
  _ : 3 ∈ [ 1 , 2 , 3 , 2 ]
  _ = there (there (here refl))
```

## Listas

- Decidibilidade.

```agda
  Decidable : ∀ {a}{A : Set a} → (A → Set a) → Set a
  Decidable {_}{A} P = ∀ (x : A) → Dec (P x)
```

## Listas

- Decidibilidade de `All`

```agda
  All? : ∀ {a}{A : Set a}{P : A → Set a} → Decidable P → Decidable (All P)
  All? decP [] = yes []
  All? decP (x ∷ xs) with decP x | All? decP xs
  ...| yes px | yes allxs = yes (px ∷ allxs)
  ...| no ¬px | _         = no λ { (k ∷ ks) → ¬px k}
  ...| _      | no ¬allxs = no λ { (k ∷ ks) → ¬allxs ks }
```

## Listas

- Isso conclui a nossa apresentação inicial sobre listas
e seus algoritmos usando a linguagem Agda.

- Na próxima aula, veremos um exemplo completo de verificação
de um algoritmo.

## Referências

- Kokke, Wen; Wadler, Phillip; Siek, Jeremy. Programming Languages Foundations in
Agda.
