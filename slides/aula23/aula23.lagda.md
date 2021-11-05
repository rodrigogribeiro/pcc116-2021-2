---
title: Definindo um intepretador para IMP.
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

```agda
{-# OPTIONS --sized-types #-}
module aula23 where

open import Algebra.Monad.Monad

open import Coinduction.Size
open import Coinduction.Delay

open import Data.Bool.Bool
open import Data.List.List
open import Data.List.Relation.All
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.List.Relation.Any
open import Data.Unit.Unit

open import Relation.Equality.Propositional
```

Objetivos
=========

- Definir um definitional intepreter para uma linguagem
imperativa utilizando a mônada de Delay.

A linguagem IMP
===============

- A linguagem IMP consiste do núcleo de linguagens imperativas.

- A sintaxe, sistema de tipos e semântica são definidas no livro
The Formal Semantics of Programming Languages do Glynn Winskel.

Sintaxe e Semântica de Expressões
=================================

- Definição de tipos e contextos

```agda
data Type : Set where
  nat bool : Type

Ctx : Set
Ctx = List Type
```

- Semântica de tipos

```agda
Value : Type → Set
Value nat = ℕ
Value bool = Bool
```

- Sintaxe de expressões

```agda
data Exp (Γ : Ctx) : Type → Set where
  val : ∀ {t}(v : Value t)  → Exp Γ t
  var : ∀ {t}(v : t ∈ Γ)      → Exp Γ t
  _⊕_ : ∀ (e e' : Exp Γ nat)  → Exp Γ nat
  _⊗_ : ∀ (e e' : Exp Γ nat)  → Exp Γ nat
  _⊝_ : ∀ (e e' : Exp Γ nat)  → Exp Γ nat
  _≐_ : ∀ (e e' : Exp Γ nat)  → Exp Γ bool
  _⊑_ : ∀ (e e' : Exp Γ nat)  → Exp Γ bool
  !_  : ∀ (e : Exp Γ bool)    → Exp Γ bool
  _∧_ : ∀ (e e' : Exp Γ bool) → Exp Γ bool
  _∨_ : ∀ (e e' : Exp Γ bool) → Exp Γ bool
```

- Definição de variáveis são feitas usando uma
expressão de inicialização.

```agda
data VarDecl (Γ : Ctx)(t : Type) : Set where
  init : (e : Exp Γ t) → VarDecl Γ t

data Decls (Γ : Ctx) : Ctx → Set where
  []  : Decls Γ Γ
  _∷_ : ∀ {t Γ'}
          (d : VarDecl Γ t)
          (ds : Decls (t ∷ Γ) Γ') → Decls Γ Γ'
```

- Sintaxe de comandos

```agda
Stmts : Ctx → Set

data Stmt (Γ : Ctx) : Set where
  _:=_  : ∀ {t}(v : t ∈ Γ)(e : Exp Γ t) → Stmt Γ
  While : ∀ (e : Exp Γ bool)(s : Stmts Γ)  → Stmt Γ
  If_Then_Else : ∀ (e : Exp Γ bool)(s₁ s₂ : Stmts Γ) → Stmt Γ

Stmts Γ = List (Stmt Γ)
```

- Definição de um programa

```agda
record Program : Set where
  constructor program
  field
    {Γ} : Ctx
    decls : Decls [] Γ
    stmts : Stmts Γ
    main  : Exp Γ nat
```

Semântica de IMP
================

- Semântica de contextos

```agda
Env : Ctx → Set
Env Γ = All Value Γ
```

- Semântica de expressões

```agda
eval : ∀ {Γ t} → Exp Γ t → Env Γ → Value t
eval (val v) env = v
eval (var v) env = lookup v env
eval (e ⊕ e₁) env = eval e env + eval e₁ env
eval (e ⊗ e₁) env = eval e env * eval e₁ env
eval (e ⊝ e₁) env = eval e env - eval e₁ env
eval (e ≐ e₁) env = eval e env ≡B eval e₁ env
eval (e ⊑ e₁) env = eval e env ≤B eval e₁ env
eval (! e) env = not (eval e env)
eval (e ∧ e₁) env = eval e env && eval e₁ env
eval (e ∨ e₁) env = eval e env || eval e₁ env
```

- Semântica de declarações

```agda
evalDecl : ∀ {Γ t}(v : VarDecl Γ t)(ρ : Env Γ) → Env (t ∷ Γ)
evalDecl (init e) ρ = eval e ρ ∷ ρ

evalDecls : ∀ {Γ Γ'}(v : Decls Γ Γ')(ρ : Env Γ) → Env Γ'
evalDecls [] ρ = ρ
evalDecls (d ∷ ds) ρ = evalDecls ds (evalDecl d ρ)
```

- Combinando o estado de IMP e a mônada de delay

```agda
module ExecM {Γ : Ctx} where

  record Exec (i : Size)(A : Set) : Set where
    field
      runExec : ∀ (ρ : Env Γ) → Delay i (A × Env Γ)

  open Exec public
```

- Operações monádicas

```agda
  returnExec : ∀ {i A} → (a : A) → Exec i A
  returnExec a .runExec ρ = return (a , ρ)

  bindExec : ∀ {i A B} → Exec i A → (A → Exec i B) → Exec i B
  bindExec m k .runExec ρ = runExec m ρ >>= λ where (a , ρ') → k a .runExec ρ'

  instance
    monadExec : ∀ {i} → Monad (Exec i)
    monadExec = record { return = returnExec
                       ; _>>=_ = bindExec }
 ```

- Modificando o ambiente

```agda
  modify : ∀ {i}(f : Env Γ → Env Γ) → Exec i ⊤
  modify f .runExec ρ = return (tt , f ρ)
```

- Executando uma expressão em Exec

```agda
  evalExp : ∀ {i t} → Exp Γ t → Exec i (Value t)
  evalExp e .runExec ρ = return (eval e ρ , ρ)
```

- Executando comandos

```agda
  evalStmts : ∀ {i} → Stmts Γ → Exec i ⊤

  evalStmt : ∀ {i} → Stmt Γ → Exec i ⊤
  evalStmt (v := e)
    = do
        x ← evalExp e
        modify (updateWith v (λ _ → x))
  evalStmt (While e s)
    = do
        true ← evalExp e where
          false → return _
        evalStmts s
        λ { .runExec ρ .force → later' (evalStmt (While e s) .runExec ρ) }
  evalStmt (If e Then s₁ Else s₂)
    = do
        b ← evalExp e
        if b then evalStmts s₁ else evalStmts s₂

  evalStmts [] = return _
  evalStmts (s ∷ ss)
    = do
        evalStmt s
        evalStmts ss
```

Conclusão
=========

- Nesta aula, vimos como definir um interpretador para a
linguagem IMP usando co-indução.


Referências
===========

Wynskel, Glynn. The Formal Semantics of Programming Languages.
