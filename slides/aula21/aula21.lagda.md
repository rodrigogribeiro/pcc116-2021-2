---
title: Expressões aritméticas tipadas
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---


```agda
module aula21 where

open import Data.Bool.Bool
open import Data.Empty.Empty
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sigma.Sigma
open import Data.Sum.Sum

open import Relation.Equality.Propositional
```

# Objetivos

- Usar a linguagem Agda para formalizar uma linguagem de expressões usando
o estilo extrínsico e intrínsico.

Estilos de formalização
=======================

- Existem dois estilos de formalização em assistentes de provas: o extrínsico
e o intrínsico.

- O estilo extrínsico caracteriza-se pela definição de funções e tipos de dados
"simples" (i.e. sem uso de tipos dependentes) e da formalização de teoremas
a para garantir propriedades de interesses.

- O estilo intrínsico caracteriza-se pela definição de funções e tipos de dados
usando tipos dependentes para garantir propriedades de interesse "por construção".


Estilo extrínsico
=================

- Vamos considerar a formalização da linguagem de expressões aritméticas simples
envolvendo valores naturais e booleanos.

```agda
module Extrinsic where

  data Val : Set where
    VNat : ℕ → Val
    VBool : Bool → Val
```

- Expressões são formadas por valores, adições, desigualdade e condicionais.

```agda
  infix 50 _⊕_
  infix 40 _<_

  data Exp : Set where
    val  : Val → Exp
    _⊕_  : Exp → Exp → Exp
    _<_  : Exp → Exp → Exp
    cond : Exp → Exp → Exp → Exp
```

- A linguagem de expressões possui apenas dois tipos: naturais e booleanos.

```agda
  data Type : Set where
    nat bool : Type
```

- O sistema de tipos para a linguagem anterior pode ser representado pelo
seguinte tipo de dados Agda.

```agda
  data ⊢_∷_ : Exp → Type → Set where
    T-Nat  : (n : ℕ) → ⊢ (val (VNat n)) ∷ nat
    T-Bool : (b : Bool) → ⊢ (val (VBool b)) ∷ bool
    T-Add  : {e e' : Exp} → ⊢ e  ∷ nat
                          → ⊢ e' ∷ nat
                          → ⊢ (e ⊕ e') ∷ nat
    T-Lt   : {e e' : Exp} → ⊢ e ∷ nat
                          → ⊢ e' ∷ nat
                          → ⊢ (e < e') ∷ bool
    T-cond   : ∀ {e e' e'' : Exp}{t} → ⊢ e ∷ bool
                                     → ⊢ e' ∷ t
                                     → ⊢ e'' ∷ t
                                     → ⊢ (cond e e' e'') ∷ t
```

- Definição de um type checker

```agda
  type-check : (e : Exp) → Maybe Type
  type-check e = {!!}
```


- O type checker é sound

```agda
  type-checker-sound : ∀ e t → type-check e ≡ just t → ⊢ e ∷ t
  type-checker-sound e t eq = {!!}
```

- O type checker é complete

```agda
  type-checker-complete : ∀ {e t} → ⊢ e ∷ t → type-check e ≡ just t
  type-checker-complete ⊢e∷t = {!!}
```


- Podemos representar a semântica operacional de passo pequeno pelo
  seguinte tipo de dados.

```agda
  infix 30 _↝_

  _<?_ : ℕ → ℕ → Bool
  zero <? zero = false
  zero <? suc m = true
  suc n <? zero = false
  suc n <? suc m = n <? m

  data _↝_ : Exp → Exp → Set where
    ↝-Add : (n m : ℕ) → val (VNat n) ⊕ val (VNat m) ↝ val (VNat (n + m))
    ↝-Add-l : {e₁ e₁' e₂ : Exp} → e₁ ↝ e₁'
                                 → (e₁ ⊕ e₂) ↝ (e₁' ⊕ e₂)
    ↝-Add-r : ∀ {v}{e₂ e₂' : Exp} → e₂ ↝ e₂'
                                   → (val (VNat v) ⊕ e₂) ↝ (val (VNat v) ⊕ e₂')
    ↝-Lt : (n m : ℕ) → val (VNat n) < val (VNat m) ↝ val (VBool (n <? m))
    ↝-Lt-l : ∀ {e₁ e₁'} e₂ → e₁ ↝ e₁' → e₁ < e₂ ↝ e₁' < e₂
    ↝-Lt-r : ∀ {e₂ e₂'} n → e₂ ↝ e₂' → val (VNat n) < e₂ ↝  val (VNat n) < e₂'
    ↝-cond : ∀ {e₁ e₁' e₂ e₃} → e₁ ↝ e₁'
                               → (cond e₁ e₂ e₃) ↝ (cond e₁' e₂ e₃)
    ↝-cond-true : (e e' : Exp) → cond (val (VBool true)) e e' ↝ e
    ↝-cond-false : (e e' : Exp) → cond (val (VBool false)) e e' ↝ e'
```

- A semântica é determinística.

```agda
  ↝-deterministic : ∀ {e₁ e₂ e₃} → e₁ ↝ e₂ → e₁ ↝ e₃ → e₂ ≡ e₃
  ↝-deterministic = {!!}
```

- Se uma expressão é tipável, o seu tipo deve ser único.

```agda
  ⊢-unique : ∀ {e}{t t'} → ⊢ e ∷ t → ⊢ e ∷ t' → t ≡ t'
  ⊢-unique = {!!}
```

- Teorema de preservação

```agda
  preservation : ∀ {e e' t} → e ↝ e' → ⊢ e ∷ t → ⊢ e' ∷ t
  preservation = {!!}
```

- Teorema de progresso

```agda
  progress : ∀ {e t} → ⊢ e ∷ t → ∃ (λ v → e ≡ val v) ⊎ ∃ (λ e' → e ↝ e')
  progress = {!!}
```

- Semântica de múltiplos passos e alguns teoremas.

```agda
  data _↝*_ : Exp → Exp → Set where
    done : ∀ {v} → (val v) ↝* (val v)
    step : ∀ {e₁ e₂ e₃} → e₁ ↝ e₂
                        → e₂ ↝* e₃
                        → e₁ ↝* e₃
```

- Lema 1: combinando duas semântica multi-step com operador de adição

```agda
  ↝*-⊕ : ∀ {e n e' n'} → e ↝* val (VNat n)
                        → e' ↝* val (VNat n')
                        → (e ⊕ e') ↝* val (VNat (n + n'))
  ↝*-⊕ e↝*n e↝*n' = {!!}
```

- Lema 2: combinando duas semântica multi-step com operador de menor

```agda
  ↝*-< : ∀ {e n e' n'} → e ↝* val (VNat n)
                        → e' ↝* val (VNat n')
                        → (e < e') ↝* val (VBool (n <? n'))
  ↝*-< e↝*n e↝*n' = {!!}
```

- Lema 3: combinando duas semântica multi-step para cond/true.

```agda
  ↝*-cond-true : ∀ {e e' v' e''} → e ↝* (val (VBool true))
                                    → e' ↝* val v'
                                    → (cond e e' e'') ↝* val v'
  ↝*-cond-true e↝*n e↝*n' = {!!}
```

- Lema 4: combinando duas semântica multi-step para cond/false.

```agda
  ↝*-cond-false : ∀ {e e' v'' e''} → e ↝* (val (VBool false))
                                    → e'' ↝* val v''
                                    → (cond e e' e'') ↝* val v''
  ↝*-cond-false e↝*n e↝*n' = {!!}
```

- Teorema de type soundness

```agda
  soundness : ∀ {e t} → ⊢ e ∷ t → ∃ (λ v → ⊢ (val v) ∷ t × e ↝* (val v))
  soundness ⊢e∷t = {!!}
```

Estilo intrínsico
=================

- Agora vamos considerar um estilo diferente de formalização: o intrínsico, em que
apenas programas bem tipados são considerados.

- Primeiro, vamos definir a sintaxe intrínsica.

```agda
module Intrinsic where
  open Extrinsic using (_<?_)

  data Type : Set where
    nat bool : Type

  ⟦_⟧T : Type → Set
  ⟦ nat ⟧T  = ℕ
  ⟦ bool ⟧T = Bool

  data Exp : Type → Set where
    val  : ∀ {t} → ⟦ t ⟧T → Exp t
    _⊕_  : Exp nat → Exp nat → Exp nat
    _<_  : Exp nat → Exp nat → Exp bool
    cond : ∀ {t} → Exp bool → Exp t → Exp t → Exp t
```

- Podemos definir o teorema de type soundness usando um
interpretador da sintaxe tipada.
    - O teorema de soundness é garantido por construção
      pois o resultado da função eval são exatamente
      os valores da expressão.

```agda
  eval : ∀ {t} → Exp t → ⟦ t ⟧T
  eval e = {!!}
```


# Referências

- Amin, Nada; Rompf, Tiark. Type Soundness Proofs with Definitional Interpreters.
POPL 2017.
