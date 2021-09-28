---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Lógica em Agda
---

# Objetivos

<!--
```agda
module aula13 where

open import Basics.Level
open import Data.Bool.Bool
open import Relation.Equality.Propositional

id : ∀ {l}{A : Set l} → A → A
id x = x
```
-->

## Objetivos

- Apresentação do conceito de isomorfismo entre tipos e
sua realização em Agda.

## Objetivos

- Representação de conectivos da lógica proposicional 
em Agda.

## Objetivos

- Representação de quantificadores da lógica de predicados 
em Agda.

## Objetivos

- Demonstração de equivalências lógicas usando isomorfismos.

# Isomorfismo

## Isomorfismo

- Dizemos que um tipo `A` é isomórfico a um tipo `B` se 
existem funções `f : A → B` e `g : B → A` tais que
`f ∘ g ≡ id` e `g ∘ f ≡ id`.

## Isomorfismo

- Composição de funções

```agda
_∘_ : ∀ {l1 l2 l3}
        {A : Set l1}
        {B : Set l2}
        {C : Set l3} →
        (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)
```

## Isomorfismo

- Podemos definir a noção de isomorfismo como um registro
Agda.

```agda
infix 0 _≃_

record _≃_ {l}{l'}(A : Set l)(B : Set l') : Set (l ⊔ l') where
  field
    to   : A → B
    from : B → A
    to∘from : ∀ (y : B) → (to ∘ from) y ≡ y
    from∘to : ∀ (x : A) → (from ∘ to) x ≡ x

open _≃_
```

## Isomorfismo

- Isomorfismo é uma relação reflexiva.

```agda
≃-refl : ∀ {l}{A : Set l} → A ≃ A
≃-refl
  = record { to = id
           ; from = id
           ; to∘from = λ y → refl
           ; from∘to = λ x → refl }
```

## Isomorfismo

- Isomorfismo é uma relação simétrica.

```agda
≃-sym : ∀ {l l'}{A : Set l}{B : Set l'}
        → A ≃ B → B ≃ A
≃-sym A≃B
  = record { to = from A≃B
           ; from = to A≃B
           ; to∘from = from∘to A≃B
           ; from∘to = to∘from A≃B }
```

## Isomorfismo

- Isomorfismo é uma relação transitiva.

```agda
≃-trans : ∀ {l₁ l₂ l₃}
            {A : Set l₁}
            {B : Set l₂}
            {C : Set l₃} →
            A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C
  = record { to = to B≃C ∘ to A≃B
           ; from = from A≃B ∘ from B≃C
```

## Isomorfismo

- Continuação...

```agda
  ; to∘from = λ {y →
    begin
      (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
    ≡⟨⟩
      to B≃C (to A≃B (from A≃B (from B≃C y)))
    ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
      to B≃C (from B≃C y)
    ≡⟨ to∘from B≃C y ⟩
      y
    ∎}
```

## Isomorfismo

- Continuação...

```agda
   ; from∘to = λ {y →
     begin
       (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) y)
     ≡⟨⟩
       (from A≃B (from B≃C (to B≃C (to A≃B y))))
     ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B y)) ⟩
       from A≃B (to A≃B y)
     ≡⟨ from∘to A≃B y ⟩
       y
     ∎} }
```

## Isomorfismo

- É possível definir operadores para raciocínio
equacional envolvendo isomorfismos.

## Isomorfismo

- Para isso, vamos definir um módulo para encapsular
esses operadores.

```agda
module ≃-Reasoning where

infix  1 ≃-begin_
infixr 2 _≃⟨_⟩_
infix  3 _≃-∎
```

## Isomorfismo

- Iniciando uma dedução por equações.

```agda
≃-begin_ : ∀ {A B : Set}
      → A ≃ B → A ≃ B
≃-begin A≃B = A≃B
```

## Isomorfismo

- Transitividade

```agda
_≃⟨_⟩_ : ∀ {l₁ l₂ l₃}(A : Set l₁)
                     {B : Set l₂}
                     {C : Set l₃} → 
       A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C
```

## Isomorfismo

- Finalizando uma dedução

```agda
_≃-∎ : ∀ (A : Set) → A ≃ A
A ≃-∎ = ≃-refl
```

## Isomorfismo

- Usando a infra-estrutura definida,
poderemos provar diversos resultados sobre
a lógica proposicional em Agda.

# Conjunção

## Conjunção

- De acordo com a correspondência de Curry-Howard,
a conjunção corresponde a tipos produto.

## Conjunção

- Definindo a conjunção em Agda

```agda
infixr 2 _×_
infixr 4 _,_

record _×_ {l₁ l₂}
           (A : Set l₁)
           (B : Set l₂) : Set (l₁ ⊔ l₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_
```

## Conjunção

- O construtor do tipo `_×_` 


    \_,\_ : A → B → A × B

- é equivalente à regra de introdução da conjunção.

$$
\dfrac{\Gamma \vdash A\:\:\:\Gamma \vdash B}
      {\Gamma \vdash A \land B}
$$

## Conjunção

- Regras de eliminação da conjunção são representadas
pelas projeções

    proj₁ : A × B → A

    proj₂ : A × B → B


## Conjunção

- Propriedade: conjunção é comutativa.

```agda
×-comm : ∀ {l₁ l₂}{A : Set l₁}{B : Set l₂} →
         A × B ≃ B × A
×-comm
  = record { to = λ { (x , y) → y , x }
           ; from = λ { (x , y) → y , x }
           ; to∘from = λ { (x , y) → refl}
           ; from∘to = λ { (x , y) → refl} }
```

# Verdadeiro

## Verdadeiro

- A constante ⊤ é representada por um tipo contendo
um único construtor.

- Representamos esse fato usando um registro

## Verdadeiro

- Representando ⊤

```agda
record ⊤ : Set where
  constructor tt
```

## Verdadeiro

- O construtor `tt` corresponde a única forma de construir uma
evidência (demonstração) de ⊤.

## Verdadeiro

- ⊤ é identidade para ×

```agda
×-identity-r : ∀ {l}{A : Set l} → A × ⊤ ≃ A
×-identity-r
  = record { to = λ { (x , tt) → x }
           ; from = λ x → x , tt
           ; to∘from = λ y → refl
           ; from∘to = λ { (x , tt) → refl} }
```

# Disjunção

## Disjunção

- A disjunção é representada por um tipo que codifica a união disjunta
entre dois tipos.

```agda
infix 1 _⊎_

data _⊎_ {l₁ l₂}(A : Set l₁)
                (B : Set l₂) : Set (l₁ ⊔ l₂) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
```

## Disjunção

- A regra de introdução à esquerda da disjunção é representada pelo
construtor

    inj₁ : A → A ⊎ B

## Disjunção

- A regra de introdução à esquerda da disjunção é representada pelo
construtor

    inj₂ : B → A ⊎ B

## Disjunção

- Para a eliminação da disjunção, utilizamos casamento de padrão:

```agda
⊎-elim : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
           (A → C) → (B → C) → A ⊎ B → C
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y
```

## Disjunção

- Exemplo: ⊎ é associativo.

```agda
⊎-assoc : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
          A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc
  = record { to = ⊎-elim (inj₁ ∘ inj₁)
                         (⊎-elim (inj₁ ∘ inj₂)
                                 inj₂)
           ; from = ⊎-elim (⊎-elim inj₁ (inj₂ ∘ inj₁))
                           (inj₂ ∘ inj₂)
           ; to∘from = λ { (inj₁ (inj₁ a)) → refl ;
                           (inj₁ (inj₂ b)) → refl ;
                           (inj₂ c) → refl}
           ; from∘to = λ { (inj₁ a) → refl ;
                            (inj₂ (inj₁ b)) → refl ;
                            (inj₂ (inj₂ c)) → refl } }
```

# Falso

## Falso

- A constante `⊥` é representada por um tipo sem elementos.

```agda
data ⊥ : Set where
```

## Falso 

- Como não há construtores, não há como construir uma dedução
de ⊥ diretamente.

## Falso

- Eliminação de ⊥

```agda
⊥-elim : ∀ {l}{A : Set l} → ⊥ → A
⊥-elim ()
```

## Falso

- ⊥ é identidade para ⊎

```agda
⊎-identity-l : ∀ {l}{A : Set l} → A ⊎ ⊥ ≃ A
⊎-identity-l
  = record { to = ⊎-elim id ⊥-elim
           ; from = inj₁
           ; to∘from = λ y → refl
           ; from∘to = λ { (inj₁ a) → refl ;
                           (inj₂ ())} }
```

# Implicação

## Implicação

- A implicação é representada por tipos funcionais em Agda.

- A regra de introdução da implicação é apenas a criação de
uma λ-abstração.

## Implicação

- A regra de eliminação da implicação é apenas a aplicação
de funções.

## Implicação

- Exemplo

```agda
currying : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
           (A → B → C) ≃ ((A × B) → C)
currying
  = record { to = λ f → λ { (a , b) → f a b }
           ; from = λ f x y → f (x , y)
           ; to∘from = λ f → refl
           ; from∘to = λ f → refl }
```

# Bicondicional

## Bicondicional

- Representamos o conectivo bicondicional por um registro
formado por duas implicações (funções).

```agda
record _⇔_ {l₁ l₂}(A : Set l₁)
                  (B : Set l₂) : Set (l₁ ⊔ l₂) where
  field
    to : A → B
    from : B → A
```

## Bicondicional

- Equivalência

```agda
⇔-× : ∀ {l₁ l₂}{A : Set l₁}{B : Set l₂} →
       (A ⇔ B) ≃ (A → B) × (B → A)
⇔-×
  = record { to = λ z → _⇔_.to z , _⇔_.from z
           ; from = λ z → record { to = proj₁ z
                                 ; from = proj₂ z }
           ; to∘from = λ { (f , g) → refl }
           ; from∘to = λ { record { to = to
                                    ; from = from } → refl} }
```

# Negação

## Negação

- Representamos a negação usando funções e o tipo ⊥.

```agda
infix 3 ¬_

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥
```

## Negação

- Em Agda, o princípio do 3o excluído não é demonstrável.

- Lembre-se: esse axioma não é dedutível na lógica intuicionista.

## Negação

- Porém, podemos mostrar que a dupla negação de qualquer tautologia
da lógica clássica é demonstrável na lógica intuicionista.

## Negação

- Exemplo

```agda
excluded : ∀ {l}{A : Set l} → ¬ (¬ (A ⊎ ¬ A))
excluded ¬A⊎¬A = ¬A⊎¬A (inj₂ λ a → ¬A⊎¬A (inj₁ a))
```

# Quantificadores

## Quantificadores

- Quantificador universal é uma noção primitiva em Agda.

- Intuitivamente, o tipo `∀ (x : A) → B` em que `x` não aparece
livre em `B` é representado por `A → B`.

## Quantificadores

- Dessa forma, a introdução do quantificador universal consiste
da definição de funções.

- A eliminação do quantificador universal consiste na aplicação
de funções.

## Quantificadores

- O quantificador existencial é definido por um par formado:
    - Um valor de tipo `x : A`, a evidência do ∃.
    - Um valor de tipo `P x`, que demonstra `P` para o valor `x`.

## Quantificadores 

- Para isso, definimos o tipo Σ, conhecido como produto dependente.

```agda
record Σ {l₁ l₂}
         (A : Set l₁)
         (B : A → Set l₂) : Set (l₁ ⊔ l₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ
```

## Quantificadores

- O tipo Σ é chamado de produto dependente porque o valor do segundo
componente do par depende do valor do primeiro.

- Exemplo: 

```agda
_ : Σ Bool (λ x → x ≡ false)
_ = false , refl
```

## Quantificadores

- Usando o tipo Σ, podemos definir o quantificador existencial como
um produto dependente em que o primeiro argumento é implícito.

```agda
∃ : ∀ {l₁ l₂}
      {A : Set l₁}
      (B : A → Set l₂) → Set (l₁ ⊔ l₂)
∃ {A = A} B = Σ A B
```

## Quantificadores

- Notação alternativa para o quantificador existencial.

```agda
∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```

## Quantificadores

- Exemplo

```agda
∃-⊎ : ∀ {l₁ l₂}{A : Set l₁}{B C : A → Set l₂} →
        ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-⊎
  = record { to = λ{ (x , inj₁ bx) → inj₁ (x , bx) ;
                     (x , inj₂ cx) → inj₂ (x , cx) }
           ; from = λ{ (inj₁ (x , bx)) → x , inj₁ bx  ;
                       (inj₂ (x , cx)) → x , inj₂ cx }
           ; to∘from = λ { (inj₁ (x , bx)) → refl ;
                           (inj₂ (x , cx)) → refl} 
           ; from∘to = λ { (x , inj₁ bx) → refl ;
                            (x , inj₂ cx) → refl } }
```

# Concluindo

## Concluindo

- Representamos conectivos da lógica proposicional utilizando
tipos indutivos Agda.

## Concluindo

- Equivalências lógicas utilizando isomorfismos entre tipos.

# Referências

## Referências

- Kokke, Wen; Walder, Philip; Siek, Jeremy. Programming languages foundations
in Agda.
