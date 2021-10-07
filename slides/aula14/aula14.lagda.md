---
title: Evidências em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

# Objetivos

<!--
```agda
module aula14 where

open import Basics.Level

open import Data.Function.Function

open import Data.Bool.Bool hiding (T ; T→≡ ; ≡→T)
open import Data.Empty.Empty
open import Data.Product.Product
open import Data.Nat.Nat
open import Data.Unit.Unit

open import Relation.Equality.Propositional
```
  -->

## Objetivos

- Relacionar booleanos e tipos em Agda.

- Apresentar o conceito de _proof by reflection_.

# Evidência e Computação

  ## Evidência e Computação

- Vamos revisar a relação < sobre ℕ:

```agda
infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n} → 0 < suc n
  s<s : ∀ {n m} → n < m
                → (suc n) < (suc m)
```

## Evidência e Computação

- O tipo < representa uma _evidência_ para a
relação menor sobre ℕ.

```agda
2<4 : 2 < 4
2<4 = s<s (s<s z<s)
```

## Evidência e Computação

- Evidência para proposição (demonstração) é
algo mais "forte" que um resultado booleano.

## Evidência e Computação

- Definição do teste <.

```agda
infix 5 _<ᵇ_

_<ᵇ_ : ℕ → ℕ → Bool
zero <ᵇ zero    = false
zero <ᵇ (suc _) = true
suc _ <ᵇ zero   = false
suc n <ᵇ suc m  = n <ᵇ m
```

## Evidência e Computação

- O tipo `2 < 4` representa evidência de que
2 é menor que 4.

## Evidência e Computação

- Por sua vez, `2 <ᵇ 4` denota uma computação
que irá produzir `true`, como resultado.

```agda
_ : 2 <ᵇ 4 ≡ true
_ = refl
```

## Evidência e Computação

- Dessa forma, temos que um valor de tipo `2 < 4`
possui "mais informação" que a computação `2 <ᵇ 4`.

## Evidência e Computação

- Como relacionar o tipo < e a função <ᵇ?

- Provando soundness e completeness!

## Evidência e Computação

- Para facilitar a demonstração dessas propriedades,
vamos utilizar uma função que associa uma evidência
a valores booleanos.

```agda
T : Bool → Set
T true  = ⊤ -- tt
T false = ⊥
```

## Evidência e Computação

```agda
T→≡ : {b : Bool} → T b → b ≡ true
T→≡ {true} p = refl

≡→T : {b : Bool} → b ≡ true → T b
≡→T eq rewrite eq = tt
```

  ## Evidência e Computação

- Soundness for <ᵇ

```agda
<ᵇ-sound : ∀ {n m} → T (n <ᵇ m) → n < m
<ᵇ-sound {zero} {suc m} p = z<s
<ᵇ-sound {suc n} {suc m} p = s<s (<ᵇ-sound p)
```

## Evidência e Computação

- Completeness for <ᵇ

```agda
<ᵇ-complete : ∀ {n m} → n < m → T (n <ᵇ m)
<ᵇ-complete z<s = tt
<ᵇ-complete (s<s n<m) = <ᵇ-complete n<m
```

## Evidência e Computação

- Há alguma maneira de combinar a computação
  oferecida pelo teste baseado em valores
  booleanos e a produção de evidência?

- Sim! Para isso  vamos utilizar um novo tipo.

## Evidência e Computação

- `Dec` é um tipo que representa proposições
  decidíveis.

```agda
data Dec {l}(A : Set l) : Set l where
  yes : A   → Dec A
  no  : ¬ A → Dec A
```

## Evidência e Computação

- Usando `Dec` podemos decidir desigualdades.

- Primeiro, um resultado auxiliar.

```agda
<-suc-inv : ∀ {n m} → suc n < suc m → n < m
<-suc-inv (s<s n<m) = n<m
```

## Evidência e Computação

- Decidindo a desigualdade

```agda
_<?_ : ∀ (n m : ℕ) → Dec (n < m)
zero <? zero = no (λ ())
zero <? suc m = yes z<s
suc n <? zero = no (λ ())
suc n <? suc m with n <? m
...| yes n<m = yes (s<s n<m)
...| no ¬n<m = no (¬n<m ∘ <-suc-inv)
 -- suc n < suc m → ⊥
```

## Evidência e Computação

- Convertendo `Dec` em um booleano

```agda
⌞_⌟ : ∀ {l}{A : Set l} → Dec A → Bool
⌞ yes x ⌟ = true
⌞ no x ⌟  = false
```

## Evidência e Computação

- Obtemos a versão do teste para booleanos
simplesmente usando a função de conversão.

```agda
_<ᵇ'_ : ℕ → ℕ → Bool
n <ᵇ' m = ⌞ n <? m ⌟
```

## Evidência e Computação

- Se o tipo `Dec` é equivalente a Bool,
  então existem funções sobre `Dec`
  similares aos conectivos da lógica?

- A resposta é sim!

## Evidência e Computação

- Conjunção para `Dec`

```agda
infixr 6 _×-dec_

_×-dec_ : ∀ {a b}{A : Set a}{B : Set b} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes x₁ = yes (x , x₁)
yes x ×-dec no x₁ = no (x₁ ∘ proj₂)
no x ×-dec db = no (x ∘ proj₁)
```

# Proof by reflection

  ## Proof by reflection

- Uma aplicação importante do apresentado até o momento
é a técnica de proof by reflection.

- Como Agda é uma linguagem de programação e um assistente
  de provas, podemos usá-la para calcular uma "dedução"
  de acordo com o seu formato.

- Veremos essa técnica em um exemplo.

## Proof by reflection

- Recordando: predicado para números pares.

```agda
data Even : ℕ → Set where
  zero : Even 0
  suc  : ∀ {n} → Even n
               → Even (2 + n)

_ : Even 6
_ = suc (suc (suc zero))
```

## Proof by reflection

  - Problema: Como determinar que `Even 1099864`?

  - Para isso, precisamos de 549932 aplicações de suc terminadas em zero.

  - Podemos fazer isso de forma mais eficiente?

## Proof by reflection

- Uma definição alternativa para o predicado even.

```agda
even? : ℕ → Set
even? 0 = ⊤
even? (suc 0) = ⊥
even? (suc (suc n)) = even? n
```

## Proof by reflection

- Estabelencendo a equivalência entre as versões.

```agda
soundness : ∀ {n} → even? n → Even n
soundness {zero} p = zero
soundness {suc (suc n)} p = suc (soundness p)

completeness : ∀ {n} → Even n → even? n
completeness zero = tt
completeness (suc p) = completeness p
```

## Proof by reflection

- Usando o lema `soundness` e o fato de que uma computação
de `even? n` reduz para um valor de tipo `⊤`, para n par,
podemos obter uma dedução sem a construção efetiva de
uma árvore dedutiva.

```agda
_ : Even 1099864
_ = soundness tt -- ⊤
```

# Referências

  ## Referências

- Kokke, Wen; Wadler, Phillip; Siek, Jeremy.
Programming Languages Foundations in Agda.
