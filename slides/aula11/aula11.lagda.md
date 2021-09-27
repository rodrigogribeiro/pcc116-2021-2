---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Números Naturais em Agda
---

# Objetivos

<!--
```agda
module aula11 where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

open import Relation.Equality.Propositional
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
ℕ-induction P base ind (suc n)
   = ind n (ℕ-induction P base ind n)
```

## Indução em Agda

- Podemos usar a função `ℕ-induction` para demonstrar

    ∀ {n} → n + 0 ≡ n

## Indução em Agda

- Exemplo usando `ℕ-induction`:

```agda
+-zero-right-2 : ∀ {n} → n + 0 ≡ n
+-zero-right-2 {n}
   = ℕ-induction P base ind n
   where
     P : ℕ → Set
     P n = n + 0 ≡ n

     base : P 0
     base = refl

     ind : ∀ n → P n → P (suc n)
     ind m IH rewrite IH = refl
```

## Indução em Agda

- Outro exemplo: provar comutatividade da adição.

     ∀ (n m : ℕ) → n + m ≡ m + n

## Indução em Agda

- Iniciando a demonstração.

    +-comm : ∀ (n m : ℕ) → n + m ≡ m + n

    +-comm zero    m = ?

    +-comm (suc n) m = ?

## Indução em Agda

- No primeiro _hole_, temos o seguinte tipo:

    0 + m ≡ m + 0

## Indução em Agda

- No segundo _hole_, temos o seguinte tipo:

    (suc n) + m ≡ m + (suc n)

## Indução em Agda

- O primeiro hole

    0 + m ≡ m + 0

- Pode ser demonstrado por `+-zero-right`.

## Indução em Agda

- Para provar o segundo hole

   (suc n) + m ≡

## Indução em Agda

- Para provar o segundo hole

   (suc n) + m ≡

   suc (n + m) ≡

## Indução em Agda

- Para provar o segundo hole

   (suc n) + m ≡

   suc (n + m) ≡

   suc (m + n) ≡

## Indução em Agda

- Para provar o segundo hole:

   (suc n) + m ≡

   suc (n + m) ≡

   suc (m + n) ≡

   m + suc n

## Indução em Agda

- Porém, como podemos provar o seguinte fato:

    suc (m + n) ≡ m + suc n

## Indução em Agda

- Podemos demonstrá-lo por indução:
    - Usamos o `rewrite` para a H.I.

```agda
+-suc : ∀ (n m : ℕ) → suc n + m ≡ n + suc m
+-suc zero m = refl
+-suc (suc n) m rewrite +-suc n m = refl
```

## Indução em Agda

- Usando a função `+-suc`, a demonstração da comutatividade
é imediata.

```agda 
+-comm : ∀ (n m : ℕ) → n + m ≡ m + n
+-comm zero m = sym +-zero-right
+-comm (suc n) m
   = begin
       suc n + m   ≡⟨ refl ⟩
       suc (n + m) ≡⟨ cong suc (+-comm n m) ⟩
       suc (m + n) ≡⟨ +-suc m n ⟩
       m + suc n
     ∎ 
```

## Indução em Agda

- Exemplo: Adição é associativa.

```agda
+-assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ x + y + z
+-assoc zero y z    = refl
+-assoc (suc x) y z rewrite +-assoc x y z = refl
```

# Multiplicação

## Multiplicação

- Podemos definir a multiplicação recursivamente
da seguinte forma:

```agda
infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero    * m = zero
(suc n) * m = m + n * m
```

## Multiplicação

- Exemplo: 2 * 2.

```agda
_ : 2 * 2 ≡ 4
_ = begin
       2 * 2      ≡⟨⟩
       (suc 1) * 2 ≡⟨⟩
       2 + 1 * 2   ≡⟨⟩
       2 + (suc zero * 2) ≡⟨⟩
       2 + (2 + zero * 2) ≡⟨⟩
       2 + (2 + 0) ≡⟨⟩
       4
    ∎ 
```

## Multiplicação

- Um teorema simples

```agda
*-zero-right : ∀ {n} → n * 0 ≡ 0
*-zero-right {zero} = refl
*-zero-right {suc n} = *-zero-right {n}
```

## Multiplicação

- Distributividade da multiplicação

```agda
*-distr-+-r : ∀ (x y z : ℕ) → (x + y) * z ≡ (x * z) + (y * z)
*-distr-+-r x y zero rewrite *-zero-right {x + y} |
                             *-zero-right {x} |
                             *-zero-right {y} = refl
*-distr-+-r zero y (suc z) = refl
*-distr-+-r (suc x) y (suc z)
  rewrite sym (+-assoc z (x * suc z) (y * suc z))
    = cong suc (cong (z +_) (*-distr-+-r x y (suc z)))
```

## Multiplicação

- Multiplicação é uma operação associativa.

```agda
*-assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ x * y * z
*-assoc zero y z = refl
*-assoc (suc x) y z rewrite *-distr-+-r y (x * y) z
  | *-assoc x y z = refl
```

# Comparação

## Comparação

- Teste de igualdade

```agda
infix 6 _≡B_

_≡B_ : ℕ → ℕ → Bool
zero ≡B zero   = true
zero ≡B suc m  = false
suc n ≡B zero  = false
suc n ≡B suc m = n ≡B m
```

## Comparação 

- Como garantir que a função ≡B é correta?

## Comparação

- Precisamos provar a correção (soundness):

    n ≡B m ≡ true → n ≡ m

## Comparação

- Precisamos provar a completude (completeness):

    n ≡ m → n ≡B m = true

## Comparação

- O teste é correto

```agda
≡B-sound : ∀ {n m} → n ≡B m ≡ true → n ≡ m
≡B-sound {zero} {zero} n≡Bm = refl
≡B-sound {suc n} {suc m} n≡Bm = cong suc IH
  where
     IH : n ≡ m
     IH = ≡B-sound {n}{m} n≡Bm
```

## Comparação

- Antes de provar a completude, vamos considerar
uma propriedade auxiliar.

```agda
≡B-refl : ∀ (n : ℕ) → n ≡B n ≡ true
≡B-refl zero = refl
≡B-refl (suc n) = ≡B-refl n
```

## Comparação

- O teste é completo

```agda
≡B-complete : ∀ {n m} → n ≡ m → n ≡B m ≡ true
≡B-complete {n} refl = ≡B-refl n
```

# Par e Ímpar

## Par e Ímpar

- Podemos definir funções para determinar se um número
natural é par ou ímpar.

- Para isso, vamos usar definições mutuamente recursivas.

## Par e Ímpar

```agda
even : ℕ → Bool
odd  : ℕ → Bool

even zero    = true
even (suc n) = odd n

odd zero     = false
odd (suc n) = even n
```

## Par e Ímpar

- Um teorema mutuamente recursivo.

```agda
even-not-odd : (n : ℕ) → even n ≡ not (odd n)
odd-not-even : (n : ℕ) → odd n ≡ not (even n)

even-not-odd zero = refl
even-not-odd (suc n) = odd-not-even n

odd-not-even zero = refl
odd-not-even (suc n) = even-not-odd n
```

# Exercícios

## Exercícios

- Lista de exercícios sobre números naturais,
no arquivo Data.Nat.NatTheorems.
