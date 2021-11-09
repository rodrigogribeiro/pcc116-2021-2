---
title: Reflection em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

```agda
module aula25 where

open import Data.Bool.Bool
open import Data.Nat.Nat

open import Reflection.API
open import Relation.Equality.Propositional
```

Objetivos
=========

- Apresentar o suporte a reflection presente em Agda.

- Discutir como usar reflection para automatizar tarefas repetitivas
no desenvolvimento Agda.


Introdução
==========

- Reflection consiste em converter código de programa em uma árvore
abstrata de forma que essa possa ser manipulada por outros programas.

- Primeiramente, vamos definir um tipo de dados simples.

```agda
data Color : Set where
  red green blue : Color
```

Tipo Name
=========

- O tipo `Name` representa identificadores quaiquer no código.

```agda
colorName : Name
colorName = quote Color

isColor : Name → Bool
isColor (quote Color) = true
isColor _ = false
```

- Importante: quote funciona apenas com idenficadores concretos:
Não é possível fazer:

wrong : Set → Name
wrong s = quote s

- O tipo `Name` suporta funções para converter em strings e
igualdade de nomes.

```agda
_ : showName (quote Color) ≡ "aula25.Color"
_ = refl

_ : showName (quote red) ≡ "aula25.Color.red"
_ = refl
```

Tipo Arg
========

- O tipo Arg representa argumentos que podem ser ocultos (hidden)
ou irrelevantes (irrelevante)
