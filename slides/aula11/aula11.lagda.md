---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Números Naturais em Agda
---

# Objetivos

<!--
```agda
module aula11 where

open import Equality.Propositional
```
-->

## Objetivos

- Apresentar a representação de números naturais na
notação de Peano.

## Objetivos

- Apresentar a definição de operações básicas da
aritmética.

- Representação de provas por indução usando Agda.

# Números Naturais

## Números Naturais

- A representação em Agda de números naturais segue a
notação de Peano:

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```
<!--
```agda
{-# BUILTIN NATURAL ℕ #-}
```
-->

## Números Naturais

- Internamente, Agda converte constantes numéricas para
o valor correspondente do tipo `ℕ`.

```agda
_ : 2 ≡ (suc (suc zero))
_ = refl
```

## Números Naturais

- Uma primeira operação da aritmética é a de adição.

```agda
infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)
```

## Números Naturais

- Exemplo

    2 + 3 ≡

## Números Naturais

- Exemplo

    2 + 3 ≡

    suc 1 + 3 ≡

## Números Naturais

- Exemplo

    2 + 3 ≡

    suc 1 + 3 ≡

    suc (1 + 3) ≡

## Números Naturais

- Exemplo

    2 + 3 ≡

    suc 1 + 3 ≡

    suc (1 + 3) ≡

    suc (suc zero + 3) ≡

## Números Naturais

- Exemplo

    2 + 3 ≡

    suc 1 + 3 ≡

    suc (1 + 3) ≡

    suc (suc zero + 3) ≡
    suc (suc (zero + 3)) ≡ suc (suc 3) ≡ 5

## Números Naturais

- Exemplo

```agda
_ : 2 + 3 ≡ 5
_ = begin
      2 + 3              ≡⟨⟩
      (suc 1) + 3        ≡⟨⟩
      suc (1 + 3)        ≡⟨⟩
      suc (suc zero + 3) ≡⟨⟩
      suc (suc (0 + 3))  ≡⟨⟩
      suc (suc 3)        ≡⟨⟩
      5
    ∎ 
```

## Números Naturais

- Um primeiro teorema

    ∀ (n : ℕ) → 0 + n ≡ n

## Números Naturais

- Primeiro teorema:

```agda
+-zero-left : ∀ {n : ℕ} → 0 + n ≡ n
+-zero-left = refl
```

## Números Naturais

- Outro fato aparentemente óbvio...

    +-zero-right : ∀ {n} → n + 0 ≡ n

    +-zero-right = refl

## Números Naturais

- Ao compilar o arquivo, obtemos uma mensagem de erro...

- Novamente, temos que a igualdade por definição não foi
refletida pela igualdade proposicional.

## Números Naturais

- Para deduzir esse teorema, temos que usar indução matemática.

- Como usar indução em Agda?

## Números Naturais

- De acordo com a correspondência de Curry-Howard, uma prova por
indução nada mais é que uma função recursiva.

# Indução em Agda

## Indução em Agda

- **Prova por indução**: função recursiva.

- Definindo o teorema como uma função.

```agda
+-zero-right : ∀ {n} → n + 0 ≡ n
+-zero-right {zero} = refl
+-zero-right {suc n} = cong suc (+-zero-right {n})
```

## Indução em Agda

- Podemos simplificar provas que usam igualdades
especificando uma cláusula _rewrite_.

## Indução em Agda

- Usando rewrite

```agda
+-zero-right-1 : ∀ {n} → n + 0 ≡ n
+-zero-right-1 {zero} = refl
+-zero-right-1 {suc n} rewrite +-zero-right-1 {n} = refl 
```

## Indução em Agda

- Ao usarmos `rewrite +-zero-right-1 {n}`, o type-checker de Agda
usa a igualdade

    n + 0 ≡ n

- Para reescrever a conclusão da forma:

    (suc n) + 0 ≡ suc n

## Indução em Agda

- Porém, `(suc n) + 0 ≡ suc n` é igual a

     suc (n + 0) ≡ suc n

## Indução em Agda 

- O que permite que o type-checker reescreva `n + 0 ≡ n` na conclusão:

    suc (n + 0) ≡ suc n

- O que nos leva à seguinte conclusão:

    suc n ≡ suc n

- que é demonstrada por `refl`.

## Indução em Agda

- Dessa forma, podemos pensar que o uso de `rewrite` nesta demonstração é
equivalente ao uso da hipótese de indução.

## Indução em Agda

- Se uma demonstração por indução é uma função recursiva, podemos
representar o princípio de indução por uma função Agda?

## Indução em Agda

- Sim!

```agda
ℕ-induction : ∀ {l}(P : ℕ → Set l)   → -- propriedade
              P 0                     → -- caso base
              (∀ n → P n → P (suc n)) → -- passo indutivo
              ∀ (n : ℕ) → P n
ℕ-induction P base ind zero = base
ℕ-induction P base ind (suc n) = ind n (ℕ-induction P base ind n)
```
