---
title: Formalização do Lambda-cálculo em Agda.
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

```agda
{-# OPTIONS --sized-types #-}
module aula22 where

open import Coinduction.Size
open import Relation.Equality.Propositional
```

Objetivos
=========

- Apresentar formalizações do lambda-cálculo tipado e não tipado em
Agda.

- Apresentar a mônada de Delay e sua utilização para definição de
interpretadores usando co-indução.


A mônada de Delay
=================

- Delay A representa computações possivelmente suspensas
cujo resultado é de tipo A.

```agda
module DelayMonad where

  data Delay (A : Set)(i : Size) : Set

  record ∞Delay (A : Set)(i : Size) : Set where
    coinductive
    constructor ⟨_⟩
    field
      force : {j : Size< i} → Delay A j

  open ∞Delay public

  data Delay A i where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i
```

- Primeiramente, vamos definir a operação map sobre o
tipo Delay.

```agda
  map : ∀ {A B i} → (A → B) → Delay A i → Delay B i
  ∞map : ∀ {A B i} → (A → B) → ∞Delay A i → ∞Delay B i

  force (∞map f d) = map f (force d)

  map f (now x) = now (f x)
  map f (later c) = later (∞map f c)
```

- Combinando computações

```agda
  join : ∀ {A i} → Delay (Delay A i) i → Delay A i

  ∞join : ∀ {A i} → ∞Delay (Delay A i) i → ∞Delay A i
  force (∞join d) = join (force d)

  join (now d) = d
  join (later x) = later (∞join x)
```

- Definição do bind monádico

```agda
  _>>=_ : ∀ {A B i} → Delay A i → (A → Delay B i) → Delay B i
  m >>= f = join (map f m)
```

Lambda-cálculo não tipado.
==========================

- Sintaxe do λ-cálculo não tipado.

```agda
module Untyped where
  open import Data.Nat.Nat
  open import Data.Maybe.Maybe renaming (map to mapM)
  open import Data.Fin.Fin

  data Term : ℕ → Set where
    var : ∀ {n} → Fin n → Term n
    _∙_ : ∀ {n} → Term n → Term n → Term n
    `λ  : ∀ {n} → Term (suc n) → Term n
```

- Variáveis representadas por índices De Bruijn. Em Agda,
podemos representar os índices de maneira simples usando o tipo Fin.

- O tipo Term n representa um λ-termo contendo n variáveis livres

```agda
  _ : Term 0
  _ = `λ (var zero) -- λ x . x

  _ : Term 1
  _ = (`λ (var zero)) ∙ var zero -- (λ x . x) y

  _ : Term 2
  _ = (var zero) ∙ (var (suc zero)) -- y z
```

- Para definir o processo de avaliação, vamos
definir renaming e substitution.

- Renaming:

```agda
  Ren : ℕ → ℕ → Set
  Ren n m = Fin n → Fin m -- Term n → Term m

  weak-ren : ∀ {n m} → Ren n m → Ren (suc n) (suc m)
  weak-ren r zero = zero
  weak-ren r (suc i) = suc (r i)

  rename : ∀ {n m} → Ren n m → Term n → Term m
  rename r (var x) = var (r x)
  rename r (e ∙ e₁) = rename r e ∙ rename r e₁
  rename r (`λ e) = `λ (rename (weak-ren r) e)
```

- Substitution

```agda
  Sub : ℕ → ℕ → Set
  Sub n m = Fin n → Term m

  weak-sub : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
  weak-sub s zero = var zero
  weak-sub s (suc i) = rename suc (s i) -- (λ x. e) e' => [x |-> e'] e

  substitution : ∀ {n m} → Sub n m → Term n → Term m
  substitution s (var x) = s x
  substitution s (e ∙ e₁) = substitution s e ∙ substitution s e₁
  substitution s (`λ e) = `λ (substitution (weak-sub s) e)

  [_↦_] : ∀ {n} → Term n → Term (suc n) → Term n
  [ e ↦ e' ] = substitution (λ { zero → e
                                ; (suc i) → var i})
                             e'
```

- Dando um passo de avaliação.

```agda
  step : ∀ {n : ℕ} → Term n → Maybe (Term n)
  step (var x) = nothing
  step ((`λ e) ∙ e') = just [ e' ↦ e ]
  step (e ∙ e₁) with step e
  ...| nothing = mapM (e ∙_) (step e₁)
  ...| just e' = just (e' ∙ e₁)
  step (`λ e) = mapM `λ (step e)
```

- Interpretação

```agda
  open DelayMonad

  ∞eval : ∀ {n i} → Term n → ∞Delay (Term n) i
  eval : ∀ {n i} → Term n → Delay (Term n) i

  eval e with step e
  ...| nothing = now e
  ...| just e' = later (∞eval e')

  ∞Delay.force (∞eval e) = eval e
```

- Observando um prefixo finito da entrada.

```agda
  extract : ℕ → ∀ {n} → Delay (Term n) ∞ → Maybe (Term n)
  extract n (now e) = just e
  extract zero (later ∞d) = nothing
  extract (suc n) (later ∞d) = extract n (∞Delay.force ∞d)

  run : ℕ → ∀ {n} → Term n → Maybe (Term n)
  run gas e = extract gas (eval e)
```

Simply typed λ-calculus
=======================

- Vamos considerar a representação do simply typed λ-calculus.

```agda
module Typed where
  open import Data.Empty.Empty
  open import Data.Function.Function hiding (id)
  open import Data.List.List hiding (map)
  open import Data.List.Relation.Any
  open import Data.Nat.Nat
  open import Data.Product.Product
  open import Data.Unit.Unit
  open import Relation.Decidable.Dec
```

- Definição de tipos do simply typed λ-calculus.

```agda
  data Ty : Set where
    ι    : Ty
    _⇒_ : Ty → Ty → Ty

  ⇒-inv : ∀ {t₁ t₂ t₁' t₂'} →
             (t₁ ⇒ t₂) ≡ (t₁' ⇒ t₂') →
             t₁ ≡ t₁' × t₂ ≡ t₂'
  ⇒-inv refl = refl , refl

  _≟Ty_ : ∀ (t t' : Ty) → Dec (t ≡ t')
  ι ≟Ty ι = yes refl
  ι ≟Ty (t' ⇒ t'') = no (λ ())
  (t ⇒ t₁) ≟Ty ι = no (λ ())
  (t ⇒ t₁) ≟Ty (t' ⇒ t'') with t ≟Ty t' | t₁ ≟Ty t''
  ...| yes eq | yes eq' rewrite eq | eq' = yes refl
  ...| yes eq | no  eq' rewrite eq = no (eq' ∘ proj₂ ∘ ⇒-inv)
  ...| no  eq | _ = no (eq ∘ proj₁ ∘ ⇒-inv)
```

- Definição de contextos como listas de tipos.

```agda
  Ctx : Set
  Ctx = List Ty
```

- Representação de variáveis como índices De Bruijn:
Em representação tipadas, denotadas como provas de um
tipo pertencer a um contexto: t ∈ Γ.


```agda
  infix 0 _⊢_

  data _⊢_ : Ctx → Ty → Set where
    var : ∀ {Γ t} → t ∈ Γ → Γ ⊢ t
    `λ  : ∀ {Γ t t'} → t ∷ Γ ⊢ t' → Γ ⊢ t ⇒ t'
    _∙_ : ∀ {Γ t t'} → Γ ⊢ t ⇒ t' → Γ ⊢ t → Γ ⊢ t'
```

- Vamos representar a semântica do λ-cálculo por:
    - Representar a semântica de tipos
    - Representar a semântica de contextos
    - Represetnar a semântica de variáveis.


- A semântica de tipos é dada por uma tradução em tipos Agda.

```agda
  ⟦_⟧T : Ty → Set
  ⟦ ι ⟧T = ⊤
  ⟦ t ⇒ t' ⟧T = ⟦ t ⟧T → ⟦ t' ⟧T
```

- Representaremos a semântica de contextos como produtos da semântica
de tipos.

```agda
  ⟦_⟧C : Ctx → Set
  ⟦ [] ⟧C    = ⊤
  ⟦ t ∷ Γ ⟧C = ⟦ t ⟧T × ⟦ Γ ⟧C
```

- Representaremos a semântica de variáveis como projeção sobre a
semântica de contextos

```agda
  ⟦_⟧V : ∀ {t Γ} → t ∈ Γ → ⟦ Γ ⟧C → ⟦ t ⟧T
  ⟦ here eq ⟧V env rewrite eq = proj₁ env
  ⟦ there v ⟧V env = ⟦ v ⟧V (proj₂ env)
```

- Finalmente, podemos intepretar λ-termos de maneira imediata, usando
um definitional interpreter.

```agda
  ⟦_⟧ : ∀ {Γ t} → Γ ⊢ t → ⟦ Γ ⟧C → ⟦ t ⟧T
  ⟦ var x ⟧ env = ⟦ x ⟧V env
  ⟦ `λ e ⟧ env = λ val → ⟦ e ⟧ (val , env)
  ⟦ e ∙ e' ⟧ env = ⟦ e ⟧ env (⟦ e' ⟧ env)
```

# Normalização por avaliação

- Podemos definir a normalização por avaliação para o λ-cálculo tipado
utilizando a mônada de delay.

- Inicialmente, definimos termos neutros que consistem de uma sequência
de aplicações iniciando com uma variável.

```agda
  open DelayMonad

  data Neutral (Ξ : Ctx → Ty → Set)(Γ : Ctx) : Ty → Set where
    var : ∀ {t} → t ∈ Γ → Neutral Ξ Γ t
    _∙_ : ∀ {t t'} → Neutral Ξ Γ (t' ⇒ t) → Ξ Γ t' → Neutral Ξ Γ t
```

- Valores consistem de um environment (closure) e do código
correspondente a esse closure que pode ser um termo neutro ou
uma λ-abstração.

```agda
  data Env (Δ : Ctx) : (Γ : Ctx) → Set

  data Value (Δ : Ctx) : (t : Ty) → Set where
    neutral : ∀ {t} → Neutral Value Δ t → Value Δ t
    `λ      : ∀ {Γ t t'}(e : (t' ∷ Γ) ⊢ t)(ρ : Env Δ Γ) → Value Δ (t' ⇒ t)

  data Env Δ where
    []   : Env Δ []
    _∷_  : ∀ {Γ t}(v : Value Δ t)(ρ : Env Δ Γ)  → Env Δ (t ∷ Γ)
```

- A função lookup obtem o valor associado a uma variável em um
environment

```agda
  lookup : ∀ {t Δ Γ} → t ∈ Γ → Env Δ Γ → Value Δ t
  lookup (here refl) (v ∷ ρ) = v
  lookup (there t∈Γ) (v ∷ ρ) = lookup t∈Γ ρ
```

- Definição da avaliação

```agda
  eval  : ∀ {i Γ Δ t} → Γ ⊢ t → Env Δ Γ → Delay (Value Δ t) i
  apply : ∀ {i Δ t t'} → Value Δ (t' ⇒ t) → Value Δ t' → Delay (Value Δ t) i
  beta  : ∀ {i Γ Δ t t'} → (t' ∷ Γ) ⊢ t → Env Δ Γ → Value Δ t' → ∞Delay (Value Δ t) i

  eval (var v)  ρ = now (lookup v ρ)
  eval (`λ e)   ρ = now (`λ e ρ)
  eval (e ∙ e') ρ
    = do
         f ← eval e ρ
         v ← eval e' ρ
         apply f v

  apply (neutral n) v = now (neutral (n ∙ v))
  apply (`λ n ρ) v    = later (beta n ρ v)

  force (beta n ρ v)  = eval n (v ∷ ρ)
```

- Definição de formas normais

```agda
  data Normal (Γ : Ctx) : Ty → Set where
    `λ : ∀ {t t'}(n : Normal (t' ∷ Γ) t) → Normal Γ (t' ⇒ t)
    neutral : (Neutral Normal Γ ι) → Normal Γ ι
```

- Definição de order preserving embeddings

```agda
  data _⊇_ : (Γ Δ : Ctx) → Set where
    id   : ∀ {Γ} → Γ ⊇ Γ
    weak : ∀ {Γ Δ t} → Γ ⊇ Δ → (t ∷ Γ) ⊇ Δ
    lift : ∀ {Γ Δ t} → Γ ⊇ Δ → (t ∷ Γ) ⊇ (t ∷ Δ)
```

- Transitividade de ⊇ (composition)

```agda
  _⊚_ : ∀ {Γ Δ Δ'} → Γ ⊇ Δ → Δ ⊇ Δ' → Γ ⊇ Δ'
  id ⊚ d' = d'
  weak d ⊚ d' = weak (d ⊚ d')
  lift d ⊚ id = lift d
  lift d ⊚ weak d' = weak (d ⊚ d')
  lift d ⊚ lift d' = lift (d ⊚ d')
```

- Weakening para variáveis

```agda
  weaken-var : ∀ {t Γ Δ} → Γ ⊇ Δ → t ∈ Δ → t ∈ Γ
  weaken-var id t∈Δ = t∈Δ
  weaken-var (weak Γ⊇Δ) t∈Δ = there (weaken-var Γ⊇Δ t∈Δ)
  weaken-var (lift Γ⊇Δ) (here refl) = here refl
  weaken-var (lift Γ⊇Δ) (there t∈Δ) = there (weaken-var Γ⊇Δ t∈Δ)
```

- Weakening para valores, environments e neutral.

```agda
  weaken-Value : ∀ {t Γ Δ} → Γ ⊇ Δ → Value Δ t → Value Γ t
  weaken-Neutral : ∀ {t Γ Δ} → Γ ⊇ Δ → Neutral Value Δ t → Neutral Value Γ t
  weaken-Env : ∀ {Γ Δ E} → Γ ⊇ Δ → Env Δ E → Env Γ E

  weaken-Value id v = v
  weaken-Value (weak Γ⊇Δ) (neutral x) = neutral (weaken-Neutral (weak Γ⊇Δ) x)
  weaken-Value (weak Γ⊇Δ) (`λ e ρ) = `λ e (weaken-Env (weak Γ⊇Δ) ρ)
  weaken-Value (lift Γ⊇Δ) (neutral x) = neutral (weaken-Neutral (lift Γ⊇Δ) x)
  weaken-Value (lift Γ⊇Δ) (`λ e ρ) = `λ e (weaken-Env (lift Γ⊇Δ) ρ)

  weaken-Neutral id n = n
  weaken-Neutral (weak Γ⊇Δ) (var x) = var (there (weaken-var Γ⊇Δ x))
  weaken-Neutral (weak Γ⊇Δ) (n ∙ x) = weaken-Neutral (weak Γ⊇Δ) n ∙ weaken-Value (weak Γ⊇Δ) x
  weaken-Neutral (lift Γ⊇Δ) (var x) = var (weaken-var (lift Γ⊇Δ) x)
  weaken-Neutral (lift Γ⊇Δ) (n ∙ x) = weaken-Neutral (lift Γ⊇Δ) n ∙ weaken-Value (lift Γ⊇Δ) x

  weaken-Env Γ⊇Δ [] = []
  weaken-Env Γ⊇Δ (v ∷ ρ) = weaken-Value Γ⊇Δ v ∷ weaken-Env Γ⊇Δ ρ
```

- Top level function for weakening

```agda
  wk : ∀ {t Γ} → (t ∷ Γ) ⊇ Γ
  wk = weak id

  weakening : ∀ {t t' Γ} → Value Γ t → Value (t' ∷ Γ) t
  weakening = weaken-Value wk
```

- Convertendo entre valores e formas normais

```agda
  readback : ∀ {i Γ t} → Value Γ t → Delay (Normal Γ t) i
  nereadback : ∀ {i Γ t} → Neutral Value Γ t → Delay (Neutral Normal Γ t) i
  eta : ∀ {i Γ t t'} → Value Γ (t' ⇒ t) → ∞Delay (Normal (t' ∷ Γ) t) i

  readback {t = ι} (neutral x) = map neutral (nereadback x)
  readback {t = t₁ ⇒ t₂} v = map `λ (later (eta v))
  force (eta v)
    = do
         e ← apply (weakening v) (neutral (var (here refl)))
         readback e
  nereadback (var x) = now (var x)
  nereadback (w ∙ v)
    = do
         m ← nereadback w
         map (m ∙_) (readback v)
```

- Definindo o contexto inicial

```agda
  idEnv : ∀ Γ → Env Γ Γ
  idEnv [] = []
  idEnv (t ∷ Γ) = neutral (var (here refl)) ∷ weaken-Env wk (idEnv Γ)
```

- Combinando todos os elementos no algoritmo de normalização por avaliação.

```agda
  nf : ∀ {Γ t} → Γ ⊢ t → Delay (Normal Γ t) ∞
  nf {Γ} Γ⊢t
    = do
        v ← eval Γ⊢t (idEnv Γ)
        readback v
```

# Referências

- Abel, Andreas; Chapman, James. Normalization by Evaluation in the Delay Monad:
A Case Study for Coinduction via Copatterns and Sized Types.
