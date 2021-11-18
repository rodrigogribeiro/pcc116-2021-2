---
title: Introdução à Teoria de Tipos de Martin-Löf
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

# Objetivos

<!--
```agda
module aula26 where
```
-->

## Objetivos

- Apresentar a teoria de tipos de Martin-Löf como fundamentos
para a matemática construtiva.

## Objetivos

- Apresentar uma shallow embedding da teoria de tipos de Martin-Löf
em Agda.


# Introdução

## Introdução

- A teoria de tipos consiste de uma alternativa à teoria de conjuntos
para os fundamentos da matemática.

## Introdução

- O uso de teoria de tipos para fundamentos da matemática foi
desenvolvida pelo matemático e filósofo sueco Per Martin-Löf.

## Introdução

- Intuitivamente, a teoria de tipos organiza objetos matemáticos
utilizando tipos ao invés de conjuntos.

## Introdução

- Ao invés de usarmos $\pi \in \mathbb{R}$: uma proposição.

- Utilizamos $\pi : \mathbb{R}$: um julgamento.

## Introdução

- A diferença fundamental entre as teorias encontra-se
na interpretação do conceito de demonstração.

## Introdução

- A teoria de conjuntos adota o conceito de proposição, em que
sentenças podem ser classificadas como verdadeiras ou falsas.

## Introdução

- A teoria de tipos, por sua vez, interpreta _julgamentos_ que
possuem uma estrutura que pode ser analisada.

## Introdução

- Nem sempre um julgamento possui uma única dedução.

- Logo, a intepretação booleana não é suficiente...

## Introdução

- Em teoria de tipos, existem dois julgamentos básicos:
    - $a : A$, indicando que `a` possui o tipo A
    - $a \equiv_{A} b$, indicando que $a$ e $b$ são iguais por definição.

## Introdução

- A seguir, vamos introduzir os principais conceitos da
MLTT, usando Agda como uma forma de exposição.

# Universos

## Universos

- Para apresentarmos a MLTT, primeiramente devemos definir
o que é um tipo.

## Universos

- Para isso, vamos definir o conceito de universo.
- Intuitivamente, um universo é um _tipo de tipos_.

## Universos

- Por exemplo, dizemos que um `ℕ : Type`, em que
`Type` é um universo

## Universos

- Isso leva imediatamente à pergunta: Qual o tipo de `Type`?

- Faz sentido `Type : Type`?

## Universos

- Ao usar `Type : Type`, temos uma variante do conhecido
paradoxo de Russell da teoria de conjuntos.

- Tornando a lógica associada à teoria de tipos inconsistente.

## Universos

- Solução: introduzir uma hierarquia infinita de tipos.

$Type_0\,:\,Type_1\,:\,...$

## Universos

- Representando universos em Agda.

```agda
open import Agda.Primitive
 renaming (
            Level to Universe
          ; lzero to U₀
          ; lsuc  to _⁺
          ; Setω  to Uω
          )
 using    (_⊔_)

Type = λ ℓ → Set ℓ

variable U V T W : Universe
```

## Universos

- No código anterior, representamos o primeiro universo por
`Type U₀`.

- Se `Type U` é um universo no nível `U` então `Type (U ⁺)` é
um universo no próximo nível na hierarquia.

# Tipos

## Tipos

- Veremos como representar os tipos básicos
necessários para formalização de resultados
matemáticos.

## Tipos

- Para isso, vamos associar a cada tipo:
   - Construtores do tipo.
   - Princípio de indução.

# Tipo Unitário

## Tipo Unitário

- O tipo unitário é consiste de um único elemento.

```agda
data 𝟙 : Type U₀ where
  ⋆ : 𝟙
```

## Tipo Unitário

- A computação sobre o título unitário é feita
utilizando o princípio de indução.

```agda
𝟙-induction : (P : 𝟙 → Type U) → P ⋆ → (x : 𝟙) → P x
𝟙-induction P p ⋆ = p
```

## Tipo Unitário

- O tipo 𝟙 é um objeto terminal.

```agda
!𝟙 : {A : Type U} → A → 𝟙
!𝟙 x = ⋆
```

# Tipo Vazio

## Tipo Vazio

- O tipo vazio é um tipo que não possui
nenhum elemento.

```agda
data 𝟘 : Type U₀ where
```

## Tipo Vazio

- Princípio de indução sobre o tipo vazio.

```agda
𝟘-induction : (A : 𝟘 → Type U) → (x : 𝟘) → A x
𝟘-induction A ()
```

## Tipo Vazio

- O tipo 𝟘 é um objeto inicial.

```agda
𝟘-recursion : (A : Type U) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : Type U) → 𝟘 → A
!𝟘 = 𝟘-recursion
```

## Tipo Vazio

- Negação é um conceito derivado a partir de 𝟘.

```agda
is-empty : Type U → Type U
is-empty A = A → 𝟘

¬_ : Type U → Type U
¬ A = A → 𝟘
```

# Números Naturais

## Números Naturais

- Números naturais são definidos indutivamente,
seguindo a abordagem de Peano.

```agda
data ℕ : Type U₀ where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

## Números Naturais

- Princípio de indução

```agda
ℕ-induction : (P : ℕ → Type U) →
              P 0               →
              ((n : ℕ) → P n → P (suc n)) →
              (n : ℕ) → P n
ℕ-induction P base IH zero = base
ℕ-induction P base IH (suc n)
  = IH n (ℕ-induction P base IH n)
```

## Números Naturais

- Representando a adição

```agda
_∔_ : ℕ → ℕ → ℕ
_∔_ n m = ℕ-induction (λ _ → ℕ) m (λ n ac → suc ac) n
```

## Números Naturais

- Comparação

```agda
_≤_ : ℕ → ℕ → Type U₀
0     ≤ y     = 𝟙
suc _ ≤ zero  = 𝟘
suc x ≤ suc y = x ≤ y

_≥_ : ℕ → ℕ → Type U₀
x ≥ y = y ≤ x
```

# Tipos Soma

## Tipos Soma

- União disjunta de dois tipos.

```agda
infixl 4 _+_

data _+_ (A : Type U)(B : Type V)  :  Type (U ⊔ V) where
  inl : A → A + B
  inr : B → A + B
```

## Tipos Soma

- Princípio de indução

```agda
+-induction : {A : Type U}{B : Type V}(P : A + B → Type W) →
              ((a : A) → P (inl a))                        →
              ((b : B) → P (inr b))                        →
              (z : A + B) → P z
+-induction P f g (inl a) = f a
+-induction P f g (inr b) = g b
```

## Tipos Soma

- Usando o tipo soma, podemos definir o tipo contendo dois
elementos (booleanos).

```agda
𝟚 : Type U₀
𝟚 = 𝟙 + 𝟙

pattern false = inl ⋆
pattern true  = inr ⋆
```

## Tipos Soma

- Princípio de indução

```agda
𝟚-induction : (P : 𝟚 → Type U) →
              P false           →
              P true            →
              (n : 𝟚) → P n
𝟚-induction P Pfalse Ptrue false = Pfalse
𝟚-induction P Pfalse Ptrue true  = Ptrue
```

# Tipos Produto

## Tipos Produto

- Produtos dependentes

```agda
record Σ {A : Type U}
         (B : A → Type V) : Type (U ⊔ V) where
  constructor _,_
  field
    fst : A
    snd : B fst
```

## Tipos Produto

- Princípio de indução

```agda
Σ-induction : {A : Type U}
              {B : A → Type V}
              {P : Σ B → Type W}                  →
              ((a : A) → (b : B a) → P (a , b))  →
              ((a , b) : Σ B) → P (a , b)
Σ-induction g (a , b) = g a b
```

## Tipos Produto

- Definindo produto cartesiano.

```agda
_×_ : Type U → Type V → Type (U ⊔ V)
A × B = Σ {A = A} (λ _ → B)
```

# Funções

## Funções

- Na teoria de conjuntos, funções são um conceito derivado
a partir da noção de conjunto.

## Funções

- Por sua vez, na teoria de tipos, funções são um conceito
primitivo.

## Funções

- Na teoria de conjuntos, funções são apenas um conjunto de
pares ordenados.

## Funções

- Na teoria de tipos, funções podem ser entendidas como
_caixas pretas_.

- A partir de um valor do domínio é retornado um valor
do contradomínio.

## Funções

- Definindo tipos Π

```agda
Π : {A : Type U}(B : A → Type V) → Type (U ⊔ V)
Π {A = A} B = (x : A) → B x

_∘_ : {A : Type U}{B : Type V}{C : B → Type W} →
      ((b : B) → C b)                          →
      (f : A → B)                              →
      (a : A) → C (f a)
g ∘ f = λ a → g (f a)
```

# Identidade

## Identidade

- Dados dois valores `a, b : A`, o tipo `Id A a b`,
denota o tipo gerado pelo construtor:

  refl : Π (x : A) → Id A x x

## Identidade

- Representação em Agda

```agda
data Id {U}(A : Type U) : A → A → Type U where
  refl : (x : A) → Id A x x

infix 4 _≡_

_≡_ : {A : Type U} → A → A → Type U
x ≡ y = Id _ x y
```

## Identidade

- Indução

```agda
𝕁 : (A : Type U)(P : (x y : A) →
                     x ≡ y     → Type V) →
    ((x : A) → P x x (refl x))           →
    (x y : A)(p : x ≡ y) → P x y p
𝕁 A P f x x (refl x) = f x
```

## Identidade

- Transport

```agda
transport : {A : Type U}(P : A → Type V){x y : A} →
            x ≡ y → P x → P y
transport P (refl x) px = px
```

## Identidade

- Composição de identidades

```agda
lhs : {A : Type U}{x y : A} → x ≡ y → A
lhs {x = x} _ = x

rhs : {A : Type U}{x y : A} → x ≡ y → A
rhs {y = y} _ = y

_∙_ : {A : Type U}
      {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
xy ∙ yz = transport (lhs xy ≡_) yz xy
```

## Identidade

- Inversa

```agda
_⁻¹ : {A : Type U}{x y : A} → x ≡ y → y ≡ x
xy ⁻¹ = transport (_≡ lhs xy) xy (refl (lhs xy))
```

## Identidade

- Congruência

```agda
ap : {A : Type U}
     {B : Type V}
     (f : A → B)
     {x y : A} → x ≡ y → f x ≡ f y
ap f {x}{y} xy
  = transport (λ _ → f x ≡ f _) xy (refl (f x))
```

## Identidade

- Desigualdade

```agda
_≢_ : {A : Type U} → A → A → Type U
x ≢ y = ¬ (x ≡ y)

≢-sym : {A : Type U}{x y : A} → x ≢ y → y ≢ x
≢-sym {x = x}{y = y} x≢y = λ (p : y ≡ x) → x≢y (p ⁻¹)
```

# Leibniz

## Leibniz

- Outra definição de igualdade é a proposta por
Leibniz.

## Leibniz

- A igualdade de Leibniz considera elementos
como iguais quando toda propriedade satisfeita
por um é satisfeita pelo outro

## Leibniz

- Definição em Agda

```agda
_≐_ : {U : Universe}
      {A : Type U} → A → A → Type (U ⁺)
_≐_ {U}{A = A} x y = (P : A → Type U) → P x → P y
```

## Leibniz

- A igualdade Leibniz é reflexiva

```agda
≐-refl : {U : Universe}{A : Type U}
         {x : A} → x ≐ x
≐-refl P p = p
```

## Leibniz

- A igualdade Leibniz é simétrica

```agda
≐-sym : {U : Universe}{A : Type U}
        {x y : A} → x ≐ y → y ≐ x
≐-sym {x = x} x≐y P = x≐y (λ z → P z → P x) (λ x → x)
```

## Leibniz

- A igualdade Leibniz é transitiva

```agda
≐-trans : {U : Universe}{A : Type U}
          {x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans {x = x} x≐y y≐z P
  = y≐z (λ z → P x → P z) (x≐y P)
```

## Leibniz

- Mas, qual a relação entre o tipo identidade e
a igualdade Leibniz?

## Leibniz

- Essas duas noções são equivalentes.

```agda
≡-≐ : {U : Universe}{A : Type U}{x y : A} →
      x ≡ y → x ≐ y
≡-≐ (refl _) = ≐-refl
```

## Leibniz

- Essas duas noções são equivalentes.

```agda
≐-≡ : {U : Universe}{A : Type U}{x y : A} →
      x ≐ y → x ≡ y
≐-≡ {x = x} x≐y = x≐y (λ z → x ≡ z) (refl _)
```

# Extensionalidade

## Extensionalidade

- Dizemos que dois objetos são extensionalmente iguais se
seus componentes são iguais.

## Extensionalidade

- Veremos que essa propriedade é válida para tipos indutivos.

## Extensionalidade

- Extensionalidade de pares

```agda
×-≡ : {A B : Type U}{x x' : A}{y y' : B} →
      x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
×-≡ (refl _) (refl _) = refl _
```

## Extensionalidade

- Extensionalidade de pares

```agda
≡-× : {A B : Type U}{x x' : A}{y y' : B} →
      (x , y) ≡ (x' , y') → (x ≡ x') × (y ≡ y')
≡-× (refl _) = refl _ , refl _
```

## Extensionalidade

- Dizemos que duas funções $f$ e $g$ são
extensionalmente iguais se, para todo $x$,
$f\:x ≡ g\:x$.

## Extensionalidade

- Se duas funções iguais, elas são extensionamente
iguais.

```agda
≡-ext : {A B : Type U}{f g : A → B} →
        f ≡ g → (x : A) → f x ≡ g x
≡-ext (refl _) x = refl _
```

## Extensionalidade

- Por exemplo, não conseguimos mostrar a seguinte
igualdade.

```agda
id-add-0 : (λ n → n ∔ 0) ≡ (λ n → n)
id-add-0 = impossible
  where
    postulate impossible : {A : Type U} → A
```

## Extensionalidade

- Consequência: a extensionalidade de funções
não é demonstrável.

```agda
FE : {U : Universe} → Type (U ⁺)
FE {U} = {A B : Type U}{f g : A → B} →
     ((x : A) → f x ≡ g x) → f ≡ g
```

## Extensionalidade

- Adicionar a extensionalidade de funções como
um postulado afeta a consistência de MLTT?


## Extensionalidade

- Não!

- Porém, como não existem regras de computação
envolvendo a `FE` demonstrações envolvendo-a
serão complicadas.

## Extensionalidade

- Uma maneira para lidar com a extensionalidade
de funções é considerando uma variante da MLTT:
Homotopy type theory.

# Unicidade da identidade

## Unicidade de identidade

- Em algum momento, teóricos iniciaram o estudo
do conteúdo computacional de demonstrações da
igualdade.

## Unicidade da identidade

- Em resumo, esse estudo visava determinar a
provabilidade de:
   - UIP: uniqueness of identity proofs

```agda
UIP : {U : Universe} → Type (U ⁺)
UIP {U} = {A : Type U}{x y : A}
          (p q : x ≡ y) → p ≡ q
```

## Unicidade da identidade

- Para o caso de `x = y`, temos que a prova para
`x ≡ y` é `refl x`.
    - URP: uniqueness of reflexivity proofs

```agda
URP : {U : Universe} → Type (U ⁺)
URP {U} = {A : Type U}{x : A}
          (p : x ≡ x) → p ≡ (refl x)
```

## Unicidade da identidade

- Evidentemente, o URP é um caso particular de UIP.

```agda
UIP-URP : {U : Universe} → UIP {U} → URP {U}
UIP-URP UIP r = UIP r (refl _)
```

## Unicidade da identidade

- Para mostrar o outro lado da equivalência,
precisamos de um resultado auxiliar.

- Dados `p q : x ≡ y`, temos que:
    -  p ⁻¹ : y ≡ x
    -  p ⁻¹ ∙ q : y ≡ y

## Unicidade da identidade

- Lema auxilar

```agda
loop-≡ : {U : Universe}{A : Type U}{x y : A}(p q : x ≡ y) →
         (p ⁻¹) ∙ q ≡ (refl y) → p ≡ q
loop-≡ (refl _) (refl _) h = refl _
```

## Unicidade da identidade

- Demonstrado o outro lado da equivalência

```agda
URP-UIP : {U : Universe} → URP {U} → UIP {U}
URP-UIP {U} URP p q = loop-≡ p q (URP ((p ⁻¹) ∙ q))
```

## Unicidade da identidade

- Outra propriedade equivalente é o chamado axioma K.

```agda
K : {U : Universe} → Type (U ⁺)
K {U} = {A : Type U}{x : A}   →
        (P : x ≡ x → Type U) →
        P (refl x)            →
        (p : x ≡ x)           →
        P p
```

## Unicidade da identidade

- URP implica K

```agda
URP-K : {U : Universe} → URP {U} → K {U}
URP-K {U} URP P r p = transport P ((URP p) ⁻¹) r
```

## Unicidade da identidade

- K implica URP

```agda
K-URP : {U : Universe} → K {U} → URP {U}
K-URP {U} K p = K (λ p → p ≡ refl _) (refl _) p
```

## Unicidade da identidade

- O tipo do axioma K:

K {U} = {A : Type U}{x : A}   →
        (P : x ≡ x → Type U) →
        P (refl x)            →
        (p : x ≡ x)           →
        P p

## Unicidade da identidade

- é apenas uma restrição do tipo de 𝕁:

𝕁 : (A : Type U)(P : (x y : A) →
                     x ≡ y     → Type V) →
    ((x : A) → P x x (refl x))           →
    (x y : A)(p : x ≡ y) → P x y p

## Unicidade da identidade

- Porém, não é possível demonstrar K usando 𝕁!

## Unicidade da identidade

- Tal fato foi demonstrado por Hofmann e Streicher
que construíram um modelo da teoria de tipos usando
estruturas algébricas conhecidas como groupoids.

## Unicidade da identidade

- Outro fato: o casamento de padrão de Agda é
_demasiadamente_ permissivo.

- Por exemplo, pode-se demonstrar UIP:

```agda
UIP-proof : {U : Universe} → UIP {U}
UIP-proof (refl _) (refl _) = refl _
```

## Unicidade da identidade

- A escolha deste algoritmo de casamento de
padrão é deliberada.

- Simplifica provas envolvendo igualdades.

## Unicidade da identidade

- Caso seja necessário considerar o comportamento
refinado do casamento de padrão de igualdades,
deve-se desabilitar o axioma K, usado pelo
casamento de padrão de Agda.

## Unicidade da identidade

- Para desabilitar o axioma K, basta adicionar
o seguinte pragma no início do arquivo:

    {-# OPTIONS --without-K #-}

# Conclusão

## Conclusão

- Nesta aula apresentamos uma introdução à MLTT e
os problemas que motivaram a elaboração da homotopy
type theory.

# Referências

## Referências

- Altenkirch, Thorsten. Naive Type Theory.

- Hofmann, Martin; Streicher, Thomas. The groupoid model
of type theory.
