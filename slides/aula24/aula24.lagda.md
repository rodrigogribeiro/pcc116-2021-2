---
title: Programação genérica em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

```agda
module aula24 where

open import Data.Bool.Bool
open import Data.Fin.Fin
open import Data.List.List
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sum.Sum
open import Data.Unit.Unit
```

Objetivos
=========

- Apresentar o conceito de programação genérica (aka polimorfismo
estrutural).

- Mostrar como definir programação genérica em Agda, utilizando
tipos dependentes.

- Implementar igualdade e map para tipos quaisquer.

Introdução
==========

- Programação genérica surgiu no contexto da linguagem Haskell como
uma aplicação direta do mecanismo de classes de tipos.

- Intuitivamente, o objetivo da programação genérica é definir
funções que operem sobre tipos de dados quaisquer. A ideia é
definir a função pela estrutura algébrica de tipos.

- Antes de apresentar uma solução geral para esse problema,
vamos considerar uma versão restrita.

Contando elementos em uma estrutura
===================================

- Considere o problema de determinar o número de elementos em uma
estrutura de dados qualquer.

- Podemos construir um algoritmo para solucionar esse problema
usando _sobrecarga_, de forma que o programa funcione de forma distinta
para diferentes tipos de estruturas.

- Primeiro, vamos definir um tipo para representar códigos das estruturas
consideradas.

```agda
data Size : Set where
  `Bool : Size
  `Pair : (s s' : Size) → Size
  `List : (s : Size) → Size
```

- Em seguida, vamos definir uma interpretação desses códigos.

```agda
⟦_⟧ : Size → Set
⟦ `Bool ⟧ = Bool
⟦ `Pair s s' ⟧ = ⟦ s ⟧ × ⟦ s' ⟧
⟦ `List s ⟧ = List ⟦ s ⟧
```

- De posse dos códigos e sua intepretação, podemos definir a função desejada:

```agda
size : (s : Size) → ⟦ s ⟧ → ℕ
size `Bool v = 1
size (`Pair s s₁) (a , b) = size s a + size s₁ b
size (`List s) [] = 0
size (`List s) (x ∷ xs) = size s x + size (`List s) xs
```

- Apesar de fácil entendimento, como generalizar essa solução para diferentes
funcionalidades e uma classe maior de tipos?


Generalizando a representação de tipos
=======================================

- Vamos definir um tipo de dados para representar
a estrutura de tipos.

```agda
infixr 4 _`+_
infixr 5 _`*_

data Reg : ℕ → Set where
  `zero : ∀ {n} → Reg (suc n)
  `suc : ∀ {n}(r : Reg n) → Reg (suc n)
  `0 : ∀ {n} → Reg n
  `1 : ∀ {n} → Reg n
  _`+_ : ∀ {n}(s t : Reg n) → Reg n
  _`*_ : ∀ {n}(s t : Reg n) → Reg n
  `μ : ∀ {n}(f : Reg (suc n)) → Reg n
```

- Contexto de estruturas: usado para decodificar tipos

```agda
data Ctx : ℕ → Set where
  [] : Ctx 0
  _,_ : ∀ {n} → Ctx n → Reg n → Ctx (suc n)
```

- Representação genérica de tipos de dados.

```agda
data Data : ∀ {n} → Ctx n → Reg n → Set where
  top : ∀ {n}{t : Reg n}{Γ : Ctx n}(e : Data Γ t) → Data (Γ , t) `zero
  pop : ∀ {n}{s t : Reg n}{Γ : Ctx n}(e : Data Γ t) → Data (Γ , s) (`suc t)
  inl : ∀ {n}{s t : Reg n}{Γ : Ctx n}(e : Data Γ s) → Data Γ (s `+ t)
  inr : ∀ {n}{s t : Reg n}{Γ : Ctx n}(e : Data Γ t) → Data Γ (s `+ t)
  unit : ∀ {n}{Γ : Ctx n} → Data Γ `1
  pair : ∀ {n}{S T : Reg n}{Γ : Ctx n}
              (s : Data Γ S)
              (t : Data Γ T) →
              Data Γ (S `* T)
  rec : ∀ {n}{F : Reg (suc n)}{Γ : Ctx n}
             (x : Data (Γ , `μ F) F) → Data Γ (`μ F)
```

- Representando números naturais
   - natF: estrutura de tipos de números naturais

```agda
module NAT where

  natF : ∀ {n} → Reg n
  natF = `μ (`1 `+ `zero)
```

- nat: representação de números naturais.

```agda
  nat : ∀ {n}(Γ : Ctx n) → Set
  nat Γ = Data Γ natF
```

- construtores do tipo de dados: usando pattern
para criar novos "padrões".

```agda
  pattern z = rec (inl unit)
  pattern s n = rec (inr (top n))
```

- Exemplo: implementando a soma.

```agda
  plus : ∀ {n}{Γ : Ctx n} → nat Γ → nat Γ → nat Γ
  plus z m = m
  plus (s n) m = s (plus n m)
```

- Exemplo: representação de listas.

```agda
module LIST where

  listF : ∀ {n} → Reg (suc n)
  listF = `μ (`1 `+ (`suc `zero `* `zero))
```

- Definição do tipo de listas e seus construtores.

```agda
  list : ∀ {n} → Ctx (suc n) → Set
  list Γ = Data Γ listF

  pattern nil = rec (inl unit)
  pattern cons x xs = rec (inr (pair (pop x) (top xs)))
```

- Concatenação de listas.

```agda
  append : ∀ {n}{Γ : Ctx (suc n)} → list Γ → list Γ → list Γ
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
```

- Definição de um teste de igualdade genérico.

```agda
module EQUALITY where

  open import Data.Empty.Empty
  open import Data.Function.Function
  open import Relation.Decidable.Dec
  open import Relation.Equality.Propositional
```

- Lemas envolvendo a igualdade do tipo Data.

```agda
  top-inv : ∀ {n}{t : Reg n}{Γ : Ctx n}{x y : Data Γ t} →
              top x ≡ top y → x ≡ y
  top-inv refl = refl

  pop-inv : ∀ {n}{s t : Reg n}{Γ : Ctx n}{x y : Data Γ t} →
              pop {s = s} x ≡ pop {s = s} y → x ≡ y
  pop-inv refl = refl

  inl-inv : ∀ {n}{s t : Reg n}{Γ : Ctx n}{x y : Data Γ s}
              → inl {t = t} x ≡ inl {t = t} y → x ≡ y
  inl-inv refl = refl

  inr-inv : ∀ {n}{s t : Reg n}{Γ : Ctx n}{x y : Data Γ t}
              → inr {s = s} x ≡ inr {s = s} y → x ≡ y
  inr-inv refl = refl

  pair-inv : ∀ {n}{Γ : Ctx n}{S T : Reg n}
               {x x' : Data Γ S}{y y' : Data Γ T} →
               pair x y ≡ pair x' y' → x ≡ x' × y ≡ y'
  pair-inv refl = refl , refl

  rec-inv : ∀ {n}{Γ : Ctx n}{F : Reg (suc n)}
              {x y : Data (Γ , `μ F) F} →
              rec x ≡ rec y → x ≡ y
  rec-inv refl = refl
```

- Implementação da igualdade genérica

```agda
  decEq : ∀ {n}{Γ : Ctx n}{t : Reg n}(x y : Data Γ t) → Dec (x ≡ y)
  decEq (top x) (top y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ top-inv)
  decEq (pop x) (pop y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ pop-inv)
  decEq (inl x) (inl y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ inl-inv)
  decEq (inl x) (inr y) = no (λ ())
  decEq (inr x) (inl y) = no (λ ())
  decEq (inr x) (inr y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ inr-inv)
  decEq unit unit = yes refl
  decEq (pair x x₁) (pair y y₁) with decEq x y | decEq x₁ y₁
  ...| yes eq  | yes eq' rewrite eq | eq' = yes refl
  ...| no  neq | _  = no (neq ∘ proj₁ ∘ pair-inv)
  ...| _       | no neq' = no (neq' ∘ proj₂ ∘ pair-inv)
  decEq (rec x) (rec y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ rec-inv)
```

- Definição da função map genérica.

```agda
module MAP where
```

- Definição de morfismos entre dois tipos genéricos.

(A -> B) -> List A -> List B
(A -> B) -> Maybe A -> Maybe B

```agda
  data [_⇒_] : ∀ {n} → Ctx n → Ctx n → Set where
    id : ∀ {n}{Γ : Ctx n} → [ Γ ⇒ Γ ]
    fun : ∀ {n}{S T : Reg n}
            {Γ Δ : Ctx n}
            (m : [ Γ ⇒ Δ ])
            (f : Data Γ S → Data Δ T) → [ Γ , S ⇒ Δ , T ]
    fmap : ∀ {n}{T : Reg n}{Γ Δ : Ctx n}(m : [ Γ ⇒ Δ ]) →
             [ Γ , T ⇒ Δ , T ]
```

- Implementação do map genérico.

```agda
  gmap : ∀ {n}{Γ Δ : Ctx n}{t : Reg n} → [ Γ ⇒ Δ ] → Data Γ t → Data Δ t
  gmap id (top d) = top d
  gmap (fun m f) (top d) = top (f d)
  gmap (fmap m) (top d) = top (gmap m d)
  gmap id (pop d) = pop d
  gmap (fun m f) (pop d) = pop (gmap m d)
  gmap (fmap m) (pop d) = pop (gmap m d)
  gmap m (inl d) = inl (gmap m d)
  gmap m (inr d) = inr (gmap m d)
  gmap m unit = unit
  gmap m (pair d d₁) = pair (gmap m d) (gmap m d₁)
  gmap m (rec d) = rec (gmap (fmap m) d)
```

Conclusão
=========

- Linguagens com suporte a tipos dependentes permitem meta-programação
usando a própria linguagem, sem a necessidade de construções especiais.
    - Meta-programas são apenas "programas".



Referências
===========

- Morris, Peter; Altenkirch, Thorsten; McBride, Connor.
Exploring regular tree types.
