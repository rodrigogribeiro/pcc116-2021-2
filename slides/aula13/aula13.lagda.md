---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lógica em Agda - Parte I
---

# Objetivos

<!--
```agda
module aula13 where

open import Basics.Level
open import Relation.Equality.Propositional

id : ∀ {l}{A : Set l} → A → A
id x = x
```
-->

## Objetivos

- Apresentação do conceito de isomorfismo entre tipos e
sua realização em Agda.

## Objetivos

- Representação de conectivos da lógica proposicional 
em Agda.

## Objetivos

- Demonstração de equivalências lógicas usando isomorfismos.

# Isomorfismo

## Isomorfismo

- Dizemos que um tipo `A` é isomórfico a um tipo `B` se 
existem funções `f : A → B` e `g : B → A` tais que
`f ∘ g ≡ id` e `g ∘ f ≡ id`.

## Isomorfismo

- Composição de funções

```agda
_∘_ : ∀ {l1 l2 l3}
        {A : Set l1}
        {B : Set l2}
        {C : Set l3} →
        (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)
```

## Isomorfismo

- Podemos definir a noção de isomorfismo como um registro
Agda.

```agda
infix 0 _≃_

record _≃_ {l}{l'}(A : Set l)(B : Set l') : Set (l ⊔ l') where
  field
    to   : A → B
    from : B → A
    to∘from : ∀ (y : B) → (to ∘ from) y ≡ y
    from∘to : ∀ (x : A) → (from ∘ to) x ≡ x

open _≃_
```

## Isomorfismo

- Isomorfismo é uma relação reflexiva.

```agda
≃-refl : ∀ {l}{A : Set l} → A ≃ A
≃-refl
  = record { to = id
           ; from = id
           ; to∘from = λ y → refl
           ; from∘to = λ x → refl }
```

## Isomorfismo

- Isomorfismo é uma relação simétrica.

```agda
≃-sym : ∀ {l l'}{A : Set l}{B : Set l'}
        → A ≃ B → B ≃ A
≃-sym A≃B
  = record { to = from A≃B
           ; from = to A≃B
           ; to∘from = from∘to A≃B
           ; from∘to = to∘from A≃B }
```

## Isomorfismo

- Isomorfismo é uma relação transitiva.

```agda
≃-trans : ∀ {l₁ l₂ l₃}
            {A : Set l₁}
            {B : Set l₂}
            {C : Set l₃} →
            A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C
  = record { to = to B≃C ∘ to A≃B
           ; from = from A≃B ∘ from B≃C
```

## Isomorfismo

- Continuação...
```agda
  ; to∘from = λ {y →
    begin
      (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
    ≡⟨⟩
      to B≃C (to A≃B (from A≃B (from B≃C y)))
    ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
      to B≃C (from B≃C y)
    ≡⟨ to∘from B≃C y ⟩
      y
    ∎}
```

## Isomorfismo

- Continuação...

```agda
   ; from∘to = λ {y →
     begin
       (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) y)
     ≡⟨⟩
       (from A≃B (from B≃C (to B≃C (to A≃B y))))
     ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B y)) ⟩
       from A≃B (to A≃B y)
     ≡⟨ from∘to A≃B y ⟩
       y
     ∎} }
```

## Isomorfismo

- É possível definir operadores para raciocínio
equacional envolvendo isomorfismos.

## Isomorfismo

- Para isso, vamos definir um módulo para encapsular
esses operadores.

```agda
module ≃-Reasoning where

infix  1 ≃-begin_
infixr 2 _≃⟨_⟩_
infix  3 _≃-∎
```

## Isomorfismo

- Iniciando uma dedução por equações.

```agda
≃-begin_ : ∀ {A B : Set}
      → A ≃ B → A ≃ B
≃-begin A≃B = A≃B
```

## Isomorfismo

- Transitividade

```agda
_≃⟨_⟩_ : ∀ {l₁ l₂ l₃}(A : Set l₁)
                     {B : Set l₂}
                     {C : Set l₃} → 
       A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C
```

## Isomorfismo

- Finalizando uma dedução

```agda
_≃-∎ : ∀ (A : Set) → A ≃ A
A ≃-∎ = ≃-refl
```

## Isomorfismo

- Usando a infra-estrutura definida,
poderemos provar diversos resultados sobre
a lógica proposicional em Agda.

# Conjunção

## Conjunção

- De acordo com a correspondência de Curry-Howard,
a conjunção corresponde a tipos produto.

## Conjunção

- Definindo a conjunção em Agda

```agda
infixr 2 _×_
infixr 4 _,_

record _×_ {l₁ l₂}
           (A : Set l₁)
           (B : Set l₂) : Set (l₁ ⊔ l₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_
```

## Conjunção

- O construtor do tipo `_×_` 


    \_,\_ : A → B → A × B

- é equivalente à regra de introdução da conjunção.

$$
\dfrac{\Gamma \vdash A\:\:\:\Gamma \vdash B}
      {\Gamma \vdash A \land B}
$$


## Conjunção
