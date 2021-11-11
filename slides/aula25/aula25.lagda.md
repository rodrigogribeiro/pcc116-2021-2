---
title: Reflection em Agda
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

```agda
module aula25 where

open import Algebra.Functor.Functor
open import Algebra.Alternative.Alternative

open import Data.Bool.Bool
open import Data.Empty.Empty
open import Data.Function.Function
open import Data.List.List
open import Data.List.Relation.Any
open import Data.List.Relation.All
open import Data.Maybe.Maybe hiding (_>>=_ ; _>>_ ; map)
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sigma.Sigma
open import Data.String.String
open import Data.Unit.Unit

open import Reflection.API
open import Reflection.DeBruijnAPI
open import Relation.Equality.Propositional
open import Relation.Decidable.Dec
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
ou irrelevantes (irrelevante).

- Antes de definir o tipo de argumentos, precisamos de tipos
auxiliares para seus componentes.

     data Visibility : Set
       visible hidden instance′ : Visibility

     data Relevance : Set
       relevant irrelevant : Relevance

     data Quantity : Set where
       quantity-0 quantity-ω : Quantity

     data Modality : Set where
       modality : (r : Relevance)
                  (q : Quantity) → Modality

     data ArgInfo : Set where
       arg-info : (v : Visibility)
                  (m : Modality) → ArgInfo

- Finalmente, argumentos são construídos usando um valor de tipo A e
um de tipo ArgInfo.

   data Arg {a} (A : Set a) : Set a where
     arg : (i : ArgInfo) (x : A) → Arg A

- Podemos criar algumas funções para criar argumentos.

```agda
visibleArg : {A : Set} → A → Arg A
visibleArg = arg (arg-info visible
                           (modality relevant quantity-ω))

hiddenArg : {A : Set} → A → Arg A
hiddenArg = arg (arg-info hidden
                          (modality relevant quantity-ω))
```

Representação de termos
=======================

- Conseguimos converter código concreto Agda em valores
do tipo Term, que representa a sintaxe abstrata de Agda.

data Term where
  var       : (x : ℕ)
              (args : List (Arg Term)) → Term
  con       : (c : Name)
              (args : List (Arg Term)) → Term
  def       : (f : Name)
              (args : List (Arg Term)) → Term
  lam       : (v : Visibility)
              (t : Abs Term) → Term
  pat-lam   : (cs : List Clause)
              (args : List (Arg Term)) → Term
  pi        : (a : Arg Type)
              (b : Abs Type) → Term
  agda-sort : (s : Sort) → Term
  lit       : (l : Literal) → Term
  meta      : (x : Meta) → List (Arg Term) → Term
  unknown   : Term

- Tipos são apenas termos...

Type = Term

- Sorts definem a cadeia de tipos Set.

data Sort where
  set     : (t : Term) → Sort
  lit     : (n : ℕ) → Sort
  prop    : (t : Term) → Sort
  propLit : (n : ℕ) → Sort
  inf     : (n : ℕ) → Sort
  unknown : Sort

- Pattern representam padrões em cláusulas.

data Pattern where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : (t : Term)    → Pattern
  var    : (x : ℕ)     → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : (x : ℕ)     → Pattern


- Clause representam cláusulas de funções.

data Clause where
  clause        : (tel : List (Σ String λ _ → Arg Type))
                  (ps : List (Arg Pattern))
                  (t : Term) → Clause
  absurd-clause : (tel : List (Σ String λ _ → Arg Type))
                  (ps : List (Arg Pattern)) → Clause


- Exemplos

```agda
import Data.Vec.Vec as V
import Data.Fin.Fin as F
import Basics.Level as L

_ : quoteTerm ℕ ≡ def (quote ℕ) []
_ = refl

_ : quoteTerm V.Vec ≡ def (quote V.Vec) []
_ = refl

lit3 : Arg Term
lit3 = visibleArg (lit (nat 3))

_ : quoteTerm (F.Fin 3) ≡ def (quote F.Fin) [ lit3 ]
_ = refl

_ : quoteTerm 3 ≡ lit (nat 3)
_ = refl
```

- Exemplos envolvendo a igualdade

```agda
_ : quoteTerm (suc zero) ≡ con (quote suc)
                               [ visibleArg (quoteTerm zero) ]
_ = refl

_ : quoteTerm (1 ≡ 1) ≡ def (quote _≡_)
                            (hiddenArg (def (quote L.lzero) []) ∷
                             hiddenArg (def (quote ℕ) [])       ∷
                             visibleArg (lit (nat 1))           ∷
                             visibleArg (lit (nat 1))           ∷ [])
_ = refl
```

- Exemplo envolvendo variáveis: internamente, variáveis são índices De Bruijn.

```agda
hiddenVar : (index : ℕ)(args : List (Arg Term)) → Arg Term
hiddenVar idx args = arg (arg-info hidden (modality relevant quantity-ω))
                         (var idx args)

visibleVar : (index : ℕ)(args : List (Arg Term)) → Arg Term
visibleVar idx args = arg (arg-info visible (modality relevant quantity-ω))
                          (var idx args)


_ : ∀ {l}{A : Set l}(x y : A) →
    quoteTerm (x ≡ y) ≡ def (quote _≡_)
                            (hiddenVar  3 []  ∷
                             hiddenVar  2 []  ∷
                             visibleVar 1 []  ∷
                             visibleVar 0 []  ∷ [])
_ = λ x y → refl
```

- Mas qual a relação entre quote e quoteTerm?
    - Nomes "definidos" são representados como quote t
    - Parâmetros são representados por variáveis.

- Exemplo

```agda
postulate X Y : Set
postulate foo : X → Y

_ : quoteTerm foo ≡ def (quote foo) []
_ = refl

module _ {C D : Set}{foo : C → D} where

  _ : quoteTerm foo ≡ var 0 []
  _ = refl
```

- A função quoteTerm faz a verificação e redução
do código antes de produzir um valor de tipo Term.


```agda
_ : quoteTerm ((λ x → x) 1) ≡ lit (nat 1)
_ = refl
```

- Representando λ termos.

```agda
_ : quoteTerm (λ (x : Bool) → x) ≡ lam visible (abs "x" (var 0 []))
_ = refl
```

Metaprogramação
===============

- Até agora, vimos apenas como construir representações sintáticas de
código.

- Porém, como usá-las efetivamente para metaprogramação?

- Para isso, Agda provê uma interface com seu typechecker usando a
mônada TC.

- Interface básica da mônada

  TC       : ∀ {a} → Set a → Set a
  return   : ∀ {a} {A : Set a} → A → TC A
  _>>=_    : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B

- Algumas primitivas da mônada TC:

1. unify : (have : Term) (goal : Term) → TC ⊤
   * Tenta unificar o primeiro termo com o goal atual (segundo argumento)

2. catchTC : ∀ {a} {A : Set a} → TC A → TC A → TC A
   * Executa a primeira computação, se esta resultar em erro de tipo,
     executa a segunda.

3. inferType : Term → TC Type
   * Infere o tipo de um termo

4. checkType : Term → Type → TC Term
   * Verifica se o termo possui um dado tipo, preenchendo argumentos implícitos.

5. normalise : Term → TC Term
   * Calcula a forma normal de um termo

6. quoteTC : ∀ {a} {A : Set a} → A → TC Term
   * Retorna a AST correspondente a um valor de tipo A

7. unquoteTC : ∀ {a} {A : Set a} → Term → TC A
   * Retorna o valor correspondnete a um termo.

8. freshName : String → TC Name
   * Retorna um novo nome.

9. declareDef : Arg Name → Type → TC ⊤
   * Cria uma declaração de função.

10. defineFun : Name → List Clause → TC ⊤
   * Define o corpo de uma função

11. getType : Name → TC Type
   * Obtém o tipo de um nome.

12. getDefinition : Name → TC Definition
   * Retorna a definição de um nome.


Metaprogramas em Agda
=====================

- Metaprogramas são executados por unquoting ou usando macros.

- Vamos considerar um pequeno exemplo: a criação de um predicado para testar
se uma cor (tipo Color) é red.

- Primeiro, vamos criar alguns valores auxiliares:

```agda
l0 : Arg Term
l0 = hiddenArg (def (quote L.lzero) [])

color : Arg Term
color = hiddenArg (def (quote Color) [])

Red : Arg Term
Red = visibleArg (con (quote red) [])
```

- Podemos criar uma definição top-level usando unquoteDecl:

```agda
unquoteDecl IsRed
  = do
      ty ← quoteTC (Color → Set)
      declareDef (visibleArg IsRed) ty
      defineFun IsRed [ clause [ ("x" , visibleArg (def (quote Color) [])) ]
                               [ visibleArg (var 0) ]
                               (def (quote _≡_)
                                    (l0 ∷ color ∷ Red ∷ visibleVar 0 [] ∷ []))
                      ]
```

- Testando a declaração criada:

```agda
red-is-red : IsRed red
red-is-red = refl

blue-not-red : ¬ (IsRed blue)
blue-not-red ()
```

- Um inconveniente dessa abordagem, é que não podemos usar "holes" para
desenvolver metaprogramas. Para "burlar" essa limitação, primeiro vamos
definir uma função e depois executá-la usando o unquoteDecl.

```agda
defineIs : Name → Name → TC ⊤
defineIs nm qcon
  = defineFun nm [ clause [ ("x"
                          , visibleArg (def (quote Color) [])) ]
                          [ visibleArg (var 0) ]
                          (def (quote _≡_)
                               (l0 ∷ color ∷ visibleArg (con qcon [])
                                           ∷ visibleVar 0 []
                                           ∷ []))
                 ]

declareIs : Name → Name → TC ⊤
declareIs nm qcon
  = do
      ty ← quoteTC (Color → Set)
      declareDef (visibleArg nm) ty
      defineIs nm qcon

unquoteDecl NewRed = declareIs NewRed (quote red)
```

- Testando...

```agda
_ : NewRed red
_ = refl
```

- Usando para criar novas definições

```agda
unquoteDecl IsBlue = declareIs IsBlue (quote blue)
unquoteDecl IsGreen = declareIs IsGreen (quote green)
```

- Considere, a seguinte definição simples:

```agda
just-blue : Color → Color
just-blue blue  = blue
just-blue red   = blue
just-blue green = blue

just-blue-constant : ∀ {c} → just-blue c ≡ blue
just-blue-constant {blue}  = refl
just-blue-constant {red}   = refl
just-blue-constant {green} = refl
```

- Podemos automatizar uma demonstração simples como essa?

```agda
constructors : Definition → List Name
constructors (data-type vars cs) = cs
constructors _ = []

by-refls : Name → Term → TC ⊤
by-refls nm form
  = let mk-clause : Name → Clause
        mk-clause qcon = clause []
                                [ hiddenArg (con qcon []) ]
                                (con (quote refl) [])
    in do
          d ← getDefinition (quote Color)
          let clauses = map mk-clause (constructors d)
          declareDef (visibleArg nm) form
          defineFun nm clauses

_ : ∀ {c} → just-blue c ≡ blue
_ = easy
    where
      ty = quoteTerm (∀ {c} → just-blue c ≡ blue)
      unquoteDecl easy = by-refls easy ty
```

- Evidentemente, esse padrão aplica-se à seguinte definição

```agda
only-green : Color → Color
only-green green = green
only-green _     = green

_ : ∀ {c} → only-green c ≡ green
_ = easy
    where
      ty = quoteTerm (∀ {c} → only-green c ≡ green)
      unquoteDecl easy = by-refls easy ty
```

Macros
======

- Macros são funções de tipo t_1 -> ... -> Term -> TC ⊤
definidas em bloco de macro.

- Macros evitam o uso de unquote para acessar variáveis.

- Exemplo: sem macros.

```agda
number₀ : Term → TC ⊤
number₀ h = unify h (quoteTerm 42)

answer₀ : ℕ
answer₀ = unquote number₀
```

- Usando macros.

```agda
macro
  number : Term → TC ⊤
  number h = unify h (quoteTerm 42)

answer : ℕ
answer = number
```

- Uma das principais aplicações de macros é a automação
de padrões simples de provas.

- Considere o exemplo a seguir.

```agda
+-ident-r : ∀ {n} → n + 0 ≡ n
+-ident-r {zero} = refl
+-ident-r {suc n} = cong suc (+-ident-r {n})

*-ident-r : ∀ {n} → n * 1 ≡ n
*-ident-r {zero} = refl
*-ident-r {suc n} = cong suc (*-ident-r {n})
```

- Podemos abstrair esse padrão de demonstração usando
uma função de ordem superior.

```agda
ℕ-induction : ∀ (P : ℕ → Set)
                (base : P 0)
                (IH : ∀ n → P n → P (suc n)) →
                ∀ (n : ℕ) → P n
ℕ-induction P base IH zero = base
ℕ-induction P base IH (suc n) = IH n (ℕ-induction P base IH n)
```

- Podemos usar ℕ-induction para deduzir os resultados anteriores

```agda
_ : ∀ (n : ℕ) → n + 0 ≡ n
_ = ℕ-induction _ refl (λ _ → cong suc)

_ : ∀ (n : ℕ) → n * 1 ≡ n
_ = ℕ-induction _ refl (λ n → cong suc)
```

- Mas, ainda assim temos repetições... Podemos resolver isso recorrendo
a uma macro.

```agda
infixr 5 λv_↦_

λv_↦_ : String → Term → Term
λv x ↦ body = lam visible (abs x body)

macro
  simple-ident-r : ∀ (let A = ℕ)(_⊕_ : A → A → A)(e : A) →
                   Term → TC ⊤
  simple-ident-r _⊕_ e goal
    = do
        ty ← quoteTC (λ (x : ℕ) → x ⊕ e ≡ x)
        step ← quoteTC (λ (x : ℕ) → cong {x = x ⊕ e}{y = x} suc)
        unify goal (def (quote ℕ-induction)
                        ((visibleArg ty) ∷
                         (visibleArg (con (quote refl) []) ∷
                         (visibleArg step) ∷ [])))
```

- Resolvemos os lemas usando a macro anterior.

```agda
_ : ∀ (n : ℕ) → n + 0 ≡ n
_ = simple-ident-r _+_ 0

_ : ∀ (n : ℕ) → n * 1 ≡ n
_ = simple-ident-r _*_ 1
```

- Outro exemplo simples: Evitar o uso de sym para reescrita de uma
igualdade.

- Primeiro, vamos utilizar uma função para obter os parâmetro do
tipo de igualdade

```agda
≡-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-info (def (quote _≡_) (lv ∷ t ∷ arg _ l ∷ arg _ r ∷ []))
  = return (lv , t , l , r)
≡-info _ = typeError [ strErr "Not an equality type" ]
```

- Definição de uma tática que tenta reescrever usando sym.

```agda
macro
  rw : Term → Term → TC ⊤
  rw p goal = catchTC (do ty ← inferType p
                          (lv , t , l , r) ← ≡-info ty
                          unify goal (def (quote sym)
                                          (lv ∷ t ∷ hiddenArg l
                                                  ∷ hiddenArg r
                                                  ∷ visibleArg p ∷ [])))
                      (unify goal p)
```

- Exemplo.

```agda
postulate x y : ℕ
postulate zap : x + 2 ≡ y

_ : y ≡ x + 2
_ = rw zap

_ : x + 2 ≡ y
_ = rw zap
```

Exemplo: Tática para tautologias
================================

- Vamos construir uma tática para provar algumas tautologias
simples da lógica proposicional.

- Primeiro, vamos definir a sintaxe das proposições consideradas.

```agda
data `Prop : Set where
  `⊤ : `Prop
  `⊥ : `Prop
  _`⇒_ : `Prop → `Prop → `Prop

Ctx : Set
Ctx = List `Prop

⇒inv : ∀ {p₁ p₂ p₁' p₂'} → (p₁ `⇒ p₂) ≡ (p₁' `⇒ p₂') → p₁ ≡ p₁' × p₂ ≡ p₂'
⇒inv refl = refl , refl

_==_ : ∀ (p p' : `Prop) → Dec (p ≡ p')
`⊤ == `⊤ = yes refl
`⊤ == `⊥ = no (λ ())
`⊤ == (p' `⇒ p'') = no (λ ())
`⊥ == `⊤ = no (λ ())
`⊥ == `⊥ = yes refl
`⊥ == (p' `⇒ p'') = no (λ ())
(p `⇒ p₁) == `⊤ = no (λ ())
(p `⇒ p₁) == `⊥ = no (λ ())
(p `⇒ p₁) == (p' `⇒ p'') with p == p' | p₁ == p''
...| yes eq | yes eq' rewrite eq | eq' = yes refl
...| no  eq | _       = no (eq ∘ proj₁ ∘ ⇒inv)
...| _      | no eq'  = no (eq' ∘ proj₂ ∘ ⇒inv)
```

- Definindo proposições demonstráveis.

```agda
data _⊢_ : Ctx → `Prop → Set where
  var : ∀ {t Γ} → t ∈ Γ → Γ ⊢ t
  tt  : ∀ {Γ} → Γ ⊢ `⊤
  lam : ∀ {Γ t t'} → (t' ∷ Γ) ⊢ t
                   → Γ ⊢ (t' `⇒ t)
```

- Semântica de demonstrações

```agda
⟦_⟧ : `Prop → Set
⟦ `⊤ ⟧ = ⊤
⟦ `⊥ ⟧ = ⊥
⟦ p `⇒ p' ⟧ = ⟦ p ⟧ → ⟦ p' ⟧

⟦_⟧C : Ctx → Set
⟦_⟧C = All ⟦_⟧
```

- Teorema de soundness

```agda
⊢-sound : ∀ {Γ p} → Γ ⊢ p → ⟦ Γ ⟧C → ⟦ p ⟧
⊢-sound (var x₁) env = lookup x₁ env
⊢-sound tt env = tt
⊢-sound (lam p) env z = ⊢-sound p (z ∷ env)
```

- Incluindo uma nova hipótese.

```agda
strengthn : Arg Type → Type → Term → TC Term
strengthn dom a t = do
  t' ← newMeta a
  extendContext dom (unify t (weaken 1 t'))
  return t'
```

- Para construir a tática, temos que realizar o "parsing"
de valores de Term em `Prop.


```agda
{-# TERMINATING #-}
parseProp : Term → TC `Prop
parseProp t = reduce t >>= λ where
    (def (quote ⊤) []) → return `⊤
    (def (quote ⊥) []) → return `⊥
    t@(pi ax@(arg _ x) (abs _ y)) → do
      X ← parseProp x
      z ← strengthn ax set! y <|> errorNotAProp t
      Z ← parseProp z
      return (X `⇒ Z)
    t → errorNotAProp t
  where
    errorNotAProp : ∀ {A} → Term → TC A
    errorNotAProp t = typeError (strErr "Parsing failed: " ∷
                                 termErr t ∷
                                 strErr " is not a proposition!" ∷ [])
```

- Definindo uma função para provar usando uma hipótese.

```agda
assumption : (Γ : Ctx) (X : `Prop) → Maybe (X ∈ Γ)
assumption [] Y = nothing
assumption (X ∷ Γ)  Y with X == Y
assumption (X ∷ Γ) .X  | yes refl = just (here refl)
assumption (X ∷ Γ)  Y  | no x     = there <$> assumption Γ Y
```

- Principal função do solver de tautologias

```agda
solveTauto : (Γ : Ctx) (X : `Prop) → Maybe (Γ ⊢ X)
solveTauto Γ X = (var <$> assumption Γ X) <|> solveTautoAux X
  where
    solveTautoAux : (X : `Prop) → Maybe (Γ ⊢ X)
    solveTautoAux = λ where
      `⊤ → just tt
      `⊥ → nothing
      (X `⇒ Y) → lam <$> solveTauto (X ∷ Γ) Y
```

- Função top level do solver

```agda
macro
  tauto : Term → TC ⊤
  tauto goal = do
    t ← inferType goal
    X ← parseProp t
    case solveTauto [] X of λ where
      (just x) → let proof : ⟦ X ⟧
                     proof = ⊢-sound x []
                 in quoteTC proof >>= unify goal
      nothing  → typeError (strErr "Failed to solve" ∷ [])
```

- Exemplos de uso do solver.

```agda
_ : ⊥ → ⊥ → ⊥ → ⊥
_ = tauto

_ : ⊤
_ = tauto
```

- Limitações: A função de parsing não contempla alguns tipos:
⊤ → ⊤. Motivo? Não consegui entender...

Conclusão
=========

- Nesta aula, apresentamos o mecanismo de reflection de Agda.

- Reflection permite acessar uma interface para o typechecker da linguagem Agda.

Referências
===========

- A gentle introduction to Agda reflection: https://github.com/alhassy/gentle-intro-to-reflection

- Agda documentation - Reflection: https://agda.readthedocs.io/en/v2.6.2/language/reflection.html
