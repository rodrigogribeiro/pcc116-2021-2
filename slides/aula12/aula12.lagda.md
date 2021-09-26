---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Relações em Agda
---

# Objetivos

<!--
```agda
module aula12 where

open import Basics.Level
```
-->

## Objetivos

- Discutir sobre o conceito de level polymorphism.

## Objetivos

- Definir relações de ordem sob números naturais
como tipos de dados indutivos.

# Level Polymorphism

## Level Polymorphism

- Como representar relações em Agda?

## Level Polymorphism

- Antes de apresentar a definição de relações em Agda,
precisamos discutir sobre o conceito de _level polymorphism_.

## Level Polymorphism

- Na teoria de conjuntos ingênua é possível definir o _paradoxo de Russell_:

$$
S = \{A \,|\, A \not\in A\}
$$

- Pergunta: S é um elemento de S?

## Level Polymorphism

- A solução de Russell foi definir uma hierarquia de objetos matemáticos.

- A hierarquia é indexada por um número natural de forma que
nível $n$ possui tipo de nível $n + 1$.

## Level Polymorphism

- Agda usa uma ideia similar para evitar um paradoxo similar ao de Russell.

- Para isso, existe uma hierarquia infinita de tipos.

## Level Polymorphism

- O primeiro elemento dessa hierarquia é o tipo `Set₀`, também representado como `Set`.

- Temos que `Set₀ : Set₁`, `Set₁ : Set₂` e assim por diante.

## Level Polymorphism

- Denominamos de nível (`Level`) o índice da hierarquia de tipos de Agda.

- Como algumas definições podem estar presentes em qualquer nível, faz sentido a
linguagem possuir níveis polimórficos.

## Level Polymorphism

- Operações básicas sobre níveis são definidas como postulados que são realizados
diretamente pelo compilador de Agda.

    postulate Level : Set

    postulate lzero : Level

    postulate lsuc  : Level

    postulate _⊔_   : Level → Level → Level

## Level Polymorphism

- A partir do conceito de _universe polymorphism_, podemos apresentar a definição
da igualdade proposicional em Agda.

# Igualdade

## Igualdade

- Igualdade proposicional

```agda
data _≡_ {l}{A : Set l}(x : A) : A → Set l where
  refl : x ≡ x
```

## Igualdade

- Conhecidas propriedades de igualdade são implementadas
como funções.

```agda
sym : ∀ {l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
sym refl = refl
```

## Igualdade

- Entendendo a definição anterior:

    sym refl = refl

- Como essa definição possui o tipo:

    x ≡ y → y ≡ x

## Igualdade

- Isso se deve ao casamento de padrões na presença de tipos
dependentes.

- O tipo `_≡_` possui um único construtor

    refl : x ≡ x

## Igualdade

- O parâmetro de `sym` possui tipo `x ≡ y`.

- Porém, o construtor de `≡` é

    refl : ∀ {x} → x ≡ x

## Igualdade 

- Logo, temos que para existir um argumento de tipo `x ≡ y`,
necessariamente `x` e `y` são iguais por definição. 

- Isso faz o type-checker de Agda constatar que `x` e `y`
denotam o mesmo valor e aceita `refl : y ≡ x`. 

## Igualdade

- Outro exemplo: congruência.

```agda
cong : ∀ {l l' : Level}{A : Set l'}{B : Set l'}{x y : A}
         (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
```

## Igualdade

- Um último exemplo: Leibniz equality.

```agda
subst : ∀ {l l'}{A : Set l}{x y : A}(P : A → Set l') →
          x ≡ y → P x → P y
subst P refl px = px
```

## Igualdade

- Veremos mais sobre casamento de padrão sobre igualdade
quando estudarmos sobre listas.

# Relações sobre ℕ

## Relações sobre ℕ

- Podemos definir relações, como `≤` sobre ℕ, usando
tipos de dados Agda.

## Relações sobre ℕ

- Primeiro, veremos como definir `≤` indutivamente.

- Para isso, vamos criar um _judgement_ que irá
representar a relação n ≤ m.

## Relações sobre ℕ

- Definição indutiva.

$$
\begin{array}{cc}
   \dfrac{}{0 \le m} &
   \dfrac{n \le m}{\textrm{suc }n\le\textrm{suc }m}
\end{array}
$$

<!--
```agda
open import Data.Nat.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.NatTheorems using (+-comm ; +-zero-right)
```
-->

## Relações sobre ℕ

- Definição em Agda

```agda
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {m n} →
          m ≤ n →
          (suc m) ≤ (suc n)
```

## Relações sobre ℕ

- Exemplo: `2 ≤ 5`

$$
\dfrac{}{2 \le 5}
$$

## Relações sobre ℕ

- Exemplo: `2 ≤ 5`

$$
\dfrac{
   \dfrac{}{1 \le 4}
}{2 \le 5}
$$


## Relações sobre ℕ

- Exemplo: `2 ≤ 5`

$$
\dfrac{
   \dfrac{
      \dfrac{}{0 \le 3}
   }{1 \le 4}
}{2 \le 5}
$$

## Relações sobre ℕ

- Exemplo: Representação da dedução em Agda.

```agda
_ : 2 ≤ 5
_ = s≤s (s≤s z≤n)
```

## Relações sobre ℕ

- `≤`  é uma relação reflexiva.

```agda
≤-refl : ∀ {x} → x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl
```

## Relações sobre ℕ

- `≤` é uma relação transtiva.

```agda
≤-trans : ∀ {x y z} → x ≤ y →
                      y ≤ z →
                      x ≤ z
≤-trans z≤n y≤z = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)
```

## Relações sobre ℕ

- `≤` é uma relação anti-simétrica

```agda
≤-antisym : ∀ {x y} → x ≤ y →
                      y ≤ x →
                      x ≡ y
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s x≤y) (s≤s y≤x)
   = cong {l = lzero} suc (≤-antisym x≤y y≤x)
```

## Relações sobre ℕ

- A relação `≤` é total.

```agda
data Total : ℕ → ℕ → Set where
  forward : ∀ {n m} →
              n ≤ m →
              Total n m
  flipped : ∀ {n m} →
              m ≤ n →
              Total n m
```

## Relações sobre ℕ

- A relação `≤` é total.

```agda
≤-total : ∀ (n m : ℕ) → Total n m
≤-total zero m = forward z≤n
≤-total (suc n) zero = flipped z≤n
≤-total (suc n) (suc m) with ≤-total n m
...| forward n≤m = forward (s≤s n≤m)
...| flipped m≤n = flipped (s≤s m≤n)
```

## Relações sobre ℕ

- Mais um teorema...

```agda
≤-suc : ∀ {n m : ℕ} → n ≤ m → n ≤ suc m
≤-suc z≤n = z≤n
≤-suc (s≤s n≤m) = s≤s (≤-suc n≤m)
```

## Relações sobre ℕ

- Um teorema envolvendo adição

```agda
≤-+-left : ∀ {n m p} → n ≤ m → n ≤ p + m
≤-+-left {p = zero} n≤m = n≤m
≤-+-left {n = .0} {p = suc p} z≤n = z≤n
≤-+-left {n = (suc n)}{m = suc m} {p = suc p} (s≤s n≤m)
  with ≤-+-left {p = p} n≤m
...| n≤p+m rewrite +-comm p (suc m) | +-comm m p
  = s≤s (≤-suc n≤p+m)
```

## Relações sobre ℕ

- Podemos usar um tipo de dados indutivo para
definir o predicado `Even`:

```agda
data Even : ℕ → Set where
  zero : Even 0
  suc  : ∀ {n} → Even n → Even (2 + n)
```

## Relações sobre ℕ

- Um pequeno teorema:

```agda
+-Even : ∀ {n m} → Even n → Even m → Even (n + m)
+-Even zero evm = evm
+-Even {n = n} (suc evn) zero rewrite +-zero-right n
  = suc evn
+-Even {n = suc (suc n)}{m = suc (suc m)} (suc evn) (suc evm)
  rewrite +-comm n (suc (suc m)) = suc (suc (+-Even evm evn))
```

# Exercícios

## Exercícios

- Exercícios referentes a esta aula estarão presentes nos módulos


# Referências

## Referências

- Mimram, Samuel. Program = Proof.
