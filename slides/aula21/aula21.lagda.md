---
title: Expressões aritméticas tipadas
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---


```agda
module aula21 where

open import Data.Bool.Bool
open import Data.Empty.Empty
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sigma.Sigma
open import Data.Sum.Sum
open import Data.Unit.Unit

open import Relation.Equality.Propositional
open import Relation.Decidable.Dec
```

# Objetivos

- Usar a linguagem Agda para formalizar uma linguagem de expressões usando
o estilo extrínsico e intrínsico.

Estilos de formalização
=======================

- Existem dois estilos de formalização em assistentes de provas: o extrínsico
e o intrínsico.

- O estilo extrínsico caracteriza-se pela definição de funções e tipos de dados
"simples" (i.e. sem uso de tipos dependentes) e da formalização de teoremas
a para garantir propriedades de interesses.

- O estilo intrínsico caracteriza-se pela definição de funções e tipos de dados
usando tipos dependentes para garantir propriedades de interesse "por construção".


Estilo extrínsico
=================

- Vamos considerar a formalização da linguagem de expressões aritméticas simples
envolvendo valores naturais e booleanos.

```agda
module Extrinsic where

  data Val : Set where
    VNat : ℕ → Val
    VBool : Bool → Val
```

- Expressões são formadas por valores, adições, desigualdade e condicionais.

```agda
  infix 50 _⊕_
  infix 40 _<_

  data Exp : Set where
    val  : Val → Exp
    _⊕_  : Exp → Exp → Exp
    _<_  : Exp → Exp → Exp
    cond : Exp → Exp → Exp → Exp
```

- A linguagem de expressões possui apenas dois tipos: naturais e booleanos.

```agda
  data Type : Set where
    nat bool : Type
```

- O sistema de tipos para a linguagem anterior pode ser representado pelo
seguinte tipo de dados Agda.

```agda
  data ⊢_∷_ : Exp → Type → Set where
    T-Nat  : (n : ℕ) →
           -----------------------
           ⊢ (val (VNat n)) ∷ nat
    T-Bool : (b : Bool) →
           ------------------------
           ⊢ (val (VBool b)) ∷ bool
    T-Add  : {e e' : Exp} → ⊢ e  ∷ nat
                          → ⊢ e' ∷ nat
                          -------------------
                          → ⊢ (e ⊕ e') ∷ nat
    T-Lt   : {e e' : Exp} → ⊢ e ∷ nat
                          → ⊢ e' ∷ nat
                          --------------------
                          → ⊢ (e < e') ∷ bool
    T-cond   : ∀ {e e' e'' : Exp}{t} → ⊢ e ∷ bool
                                     → ⊢ e' ∷ t
                                     → ⊢ e'' ∷ t
                                     -----------------------
                                     → ⊢ (cond e e' e'') ∷ t
```

- Se uma expressão é tipável, o seu tipo deve ser único.

```agda
  ⊢-unique : ∀ {e}{t t'} → ⊢ e ∷ t → ⊢ e ∷ t' → t ≡ t'
  ⊢-unique (T-Nat n) (T-Nat .n) = refl
  ⊢-unique (T-Bool b) (T-Bool .b) = refl
  ⊢-unique (T-Add ⊢e∷t ⊢e∷t₁) (T-Add ⊢e∷t' ⊢e∷t'') = refl
  ⊢-unique (T-Lt ⊢e∷t ⊢e∷t₁) (T-Lt ⊢e∷t' ⊢e∷t'') = refl
  ⊢-unique (T-cond ⊢e∷t ⊢e∷t₁ ⊢e∷t₂) (T-cond ⊢e∷t' ⊢e∷t'' ⊢e∷t''')
    rewrite ⊢-unique ⊢e∷t₁ ⊢e∷t'' = refl
```

- Definição de um type checker

```agda
  _==_ : Type → Type → Bool
  nat  == nat  = true
  bool == bool = true
  _    == _    = false

  ==-true : ∀ {t t'} → t == t' ≡ true → t ≡ t'
  ==-true {nat}{nat} refl = refl
  ==-true {bool}{bool} refl = refl
  ==-true {bool}{nat} ()
  ==-true {nat} {bool} ()

  type-check : (e : Exp) → Maybe Type
  type-check (val (VNat x)) = just nat
  type-check (val (VBool x)) = just bool
  type-check (e ⊕ e₁) with type-check e | type-check e₁
  ...| just nat | just nat = just nat
  ...| _        | _        = nothing
  type-check (e < e₁) with type-check e | type-check e₁
  ...| just nat | just nat = just bool
  ...| _        | _        = nothing
  type-check (cond e e₁ e₂) with type-check e | type-check e₁ | type-check e₂
  ...| just bool | just t | just t' = if t == t' then just t else nothing
  ...| _         | _      | _       = nothing
```

- O type checker é sound

```agda
  just-inv : ∀ {A : Set}{x y : A} → just x ≡ just y → x ≡ y
  just-inv refl = refl

  absurd : ∀ {A B : Set}{x : A} → nothing ≡ just x → B
  absurd ()

  type-checker-sound : ∀ e t → type-check e ≡ just t → ⊢ e ∷ t
  type-checker-sound (val (VNat x)) t eq rewrite just-inv (sym eq) = T-Nat x
  type-checker-sound (val (VBool x)) t eq rewrite just-inv (sym eq) = T-Bool x
  type-checker-sound (e ⊕ e₁) t eq with inspect (type-check e) | inspect (type-check e₁)
  ... | it nothing eq₁ | it t₂ eq₂ rewrite eq₁ = absurd eq
  ... | it (just nat) eq₁ | it nothing eq₂  rewrite eq₁ | eq₂ = absurd eq
  ... | it (just bool) eq₁ | it nothing eq₂ rewrite eq₁ | eq₂ = absurd eq
  ... | it (just nat) eq₁ | it (just nat) eq₂ rewrite eq₁ | eq₂ | just-inv (sym eq)
    = T-Add (type-checker-sound _ _ eq₁) (type-checker-sound _ _ eq₂)
  ... | it (just nat) eq₁ | it (just bool) eq₂ rewrite eq₁ | eq₂ = absurd eq
  ... | it (just bool) eq₁ | it (just x₁) eq₂ rewrite eq₁ | eq₂ = absurd eq
  type-checker-sound (e < e₁) t eq with inspect (type-check e) | inspect (type-check e₁)
  ... | it nothing eq₁ | it t₂ eq₂ rewrite eq₁ = absurd eq
  ... | it (just nat) eq₁ | it nothing eq₂ rewrite eq₁ | eq₂ = absurd eq
  ... | it (just nat) eq₁ | it (just nat) eq₂ rewrite eq₁ | eq₂ | just-inv (sym eq)
    = T-Lt (type-checker-sound _ _ eq₁) (type-checker-sound _ _ eq₂)
  ... | it (just nat) eq₁ | it (just bool) eq₂ rewrite eq₁ | eq₂ = absurd eq
  ... | it (just bool) eq₁ | it t₂ eq₂ rewrite eq₁ = absurd eq
  type-checker-sound (cond e₁ e₂ e₃) t eq with inspect (type-check e₁)
                                             | inspect (type-check e₂)
                                             | inspect (type-check e₃)
  ... | it nothing eq₁ | it t₂ eq₂ | it t₃ eq₃ rewrite eq₁ = absurd eq
  ... | it (just nat) eq₁ | it t₂ eq₂ | it t₃ eq₃ rewrite eq₁ = absurd eq
  ... | it (just bool) eq₁ | it nothing eq₂ | it t₃ eq₃ rewrite eq₁ | eq₂ | eq₃ = absurd eq
  ... | it (just bool) eq₁ | it (just t₂) eq₂ | it nothing eq₃ rewrite eq₁ | eq₂ | eq₃
    = absurd eq
  ... | it (just bool) eq₁ | it (just t₂) eq₂ | it (just t₃) eq₃ with inspect (t₂ == t₃)
  ... | it true eq₄ rewrite eq₁ | eq₂ | eq₃ | eq₄ | just-inv (sym eq) | ==-true eq₄
    = T-cond (type-checker-sound _ _ eq₁)
             (type-checker-sound _ _ eq₂)
             (type-checker-sound _ _ eq₃)
  ... | it false eq₄ rewrite eq₁ | eq₂ | eq₃ | eq₄ = absurd eq
```

- O type checker é complete

```agda
  ==-true1 : ∀ {t} → t == t ≡ true
  ==-true1 {nat} = refl
  ==-true1 {bool} = refl

  type-checker-complete : ∀ {e t} → ⊢ e ∷ t → type-check e ≡ just t
  type-checker-complete (T-Nat n) = refl
  type-checker-complete (T-Bool b) = refl
  type-checker-complete (T-Add ⊢e∷t ⊢e∷t₁) rewrite type-checker-complete ⊢e∷t |
                                                   type-checker-complete ⊢e∷t₁ = refl
  type-checker-complete (T-Lt ⊢e∷t ⊢e∷t₁) rewrite type-checker-complete ⊢e∷t |
                                                  type-checker-complete ⊢e∷t₁ = refl
  type-checker-complete {t = t} (T-cond ⊢e∷t ⊢e∷t₁ ⊢e∷t₂)
              rewrite type-checker-complete ⊢e∷t |
                      type-checker-complete ⊢e∷t₁ |
                      type-checker-complete ⊢e∷t₂ |
                      ==-true1 {t} = refl
```

- Podemos representar a semântica operacional de passo pequeno pelo
  seguinte tipo de dados.

```agda
  infix 30 _↝_

  _<?_ : ℕ → ℕ → Bool
  zero <? zero = false
  zero <? suc m = true
  suc n <? zero = false
  suc n <? suc m = n <? m

  data _↝_ : Exp → Exp → Set where
    ↝-Add : (n m : ℕ) → val (VNat n) ⊕ val (VNat m) ↝ val (VNat (n + m))
    ↝-Add-l : {e₁ e₁' e₂ : Exp} → e₁ ↝ e₁'
                                    -----------------------
                                 → (e₁ ⊕ e₂) ↝ (e₁' ⊕ e₂)
    ↝-Add-r : ∀ {v}{e₂ e₂' : Exp} → e₂ ↝ e₂'
                                      ----------------------------------------
                                   → (val (VNat v) ⊕ e₂) ↝ (val (VNat v) ⊕ e₂')
    ↝-Lt : (n m : ℕ) → val (VNat n) < val (VNat m) ↝ val (VBool (n <? m))
    ↝-Lt-l : ∀ {e₁ e₁'} e₂ → e₁ ↝ e₁'
                               ------------------
                            → e₁ < e₂ ↝ e₁' < e₂
    ↝-Lt-r : ∀ {e₂ e₂'} n → e₂ ↝ e₂'
                              --------------------------------------
                           → val (VNat n) < e₂ ↝  val (VNat n) < e₂'
    ↝-cond : ∀ {e₁ e₁' e₂ e₃} → e₁ ↝ e₁'
                                  ----------------------------------
                               → (cond e₁ e₂ e₃) ↝ (cond e₁' e₂ e₃)
    ↝-cond-true : (e e' : Exp) → cond (val (VBool true)) e e' ↝ e
    ↝-cond-false : (e e' : Exp) → cond (val (VBool false)) e e' ↝ e'
```

- A semântica é determinística.

```agda
  ↝-deterministic : ∀ {e₁ e₂ e₃} → e₁ ↝ e₂ → e₁ ↝ e₃ → e₂ ≡ e₃
  ↝-deterministic (↝-Add n m) (↝-Add .n .m) = refl
  ↝-deterministic (↝-Add-l e₁↝e₂) (↝-Add-l e₁↝e₃)
    rewrite ↝-deterministic e₁↝e₂ e₁↝e₃ = refl
  ↝-deterministic (↝-Add-r e₁↝e₂) (↝-Add-r e₁↝e₃)
    rewrite ↝-deterministic e₁↝e₂ e₁↝e₃ = refl
  ↝-deterministic (↝-Lt n m) (↝-Lt .n .m) = refl
  ↝-deterministic (↝-Lt-l e₂ e₁↝e₂) (↝-Lt-l .e₂ e₁↝e₃)
    rewrite ↝-deterministic e₁↝e₂ e₁↝e₃ = refl
  ↝-deterministic (↝-Lt-r n e₁↝e₂) (↝-Lt-r .n e₁↝e₃)
    rewrite ↝-deterministic e₁↝e₂ e₁↝e₃ = refl
  ↝-deterministic (↝-cond e₁↝e₂) (↝-cond e₁↝e₃)
    rewrite ↝-deterministic e₁↝e₂ e₁↝e₃ = refl
  ↝-deterministic (↝-cond-true _ e') (↝-cond-true _ .e') = refl
  ↝-deterministic (↝-cond-false e _) (↝-cond-false .e _) = refl
```

- Teorema de preservação

```agda
  preservation : ∀ {e e' t} → e ↝ e' → ⊢ e ∷ t → ⊢ e' ∷ t
  preservation (↝-Add n m) (T-Add ⊢e∷t ⊢e∷t₁) = T-Nat (n + m)
  preservation (↝-Add-l e↝e') (T-Add ⊢e∷t ⊢e∷t₁)
    = T-Add (preservation e↝e' ⊢e∷t) ⊢e∷t₁
  preservation (↝-Add-r e↝e') (T-Add ⊢e∷t ⊢e∷t₁)
    = T-Add ⊢e∷t (preservation e↝e' ⊢e∷t₁)
  preservation (↝-Lt n m) (T-Lt ⊢e∷t ⊢e∷t₁) = T-Bool (n <? m)
  preservation (↝-Lt-l _ e↝e') (T-Lt ⊢e∷t ⊢e∷t₁)
    = T-Lt (preservation e↝e' ⊢e∷t) ⊢e∷t₁
  preservation (↝-Lt-r n e↝e') (T-Lt ⊢e∷t ⊢e∷t₁)
    = T-Lt ⊢e∷t (preservation e↝e' ⊢e∷t₁)
  preservation (↝-cond e↝e') (T-cond ⊢e∷t ⊢e∷t₁ ⊢e∷t₂)
    = T-cond (preservation e↝e' ⊢e∷t) ⊢e∷t₁ ⊢e∷t₂
  preservation (↝-cond-true _ _) (T-cond ⊢e∷t ⊢e∷t₁ ⊢e∷t₂) = ⊢e∷t₁
  preservation (↝-cond-false _ _) (T-cond ⊢e∷t ⊢e∷t₁ ⊢e∷t₂) = ⊢e∷t₂
```

- Teorema de progresso

```agda
  vbool-nat : ∀ {b}{B : Set} → ⊢ val (VBool b) ∷ nat → B
  vbool-nat ()

  vnat-bool : ∀ {b}{B : Set} → ⊢ val (VNat b) ∷ bool → B
  vnat-bool ()

  progress : ∀ {e t} → ⊢ e ∷ t → ∃ (λ v → e ≡ val v) ⊎ ∃ (λ e' → e ↝ e')
  progress (T-Nat n) = inj₁ (VNat n , refl)
  progress (T-Bool b) = inj₁ (VBool b , refl)
  progress (T-Add {e' = e₂} ⊢e∷t ⊢e∷t₁) with progress ⊢e∷t | progress ⊢e∷t₁
  ... | inj₁ (VNat x , eq₁) | inj₁ (VNat x₁ , eq₂) rewrite eq₁ | eq₂
    = inj₂ (val (VNat (x + x₁)) , ↝-Add x x₁)
  ... | inj₁ (VNat x , eq₁) | inj₁ (VBool x₁ , eq₂) rewrite eq₂ = vbool-nat ⊢e∷t₁
  ... | inj₁ (VBool x , eq₁) | inj₁ (v₂ , eq₂) rewrite eq₁ = vbool-nat ⊢e∷t
  ... | inj₁ (VNat x , eq₁) | inj₂ (e₂' , e₂↝e₂') rewrite eq₁
    = inj₂ (val (VNat x) ⊕ e₂' , ↝-Add-r e₂↝e₂')
  ... | inj₁ (VBool x , eq₁) | inj₂ (e₂' , e₂↝e₂') rewrite eq₁ = vbool-nat ⊢e∷t
  ... | inj₂ (e₁' , e₁↝e₁) | _ = inj₂ (e₁' ⊕ e₂ , ↝-Add-l e₁↝e₁ )
  progress (T-Lt {e' = e₂} ⊢e∷t ⊢e∷t₁) with progress ⊢e∷t | progress ⊢e∷t₁
  ...| inj₁ (VNat x , eq₁)  | inj₁ (VNat y , eq₂) rewrite eq₁ | eq₂
    = inj₂ (val (VBool (x <? y)) , ↝-Lt x y)
  ...| inj₁ (VBool x , eq₁) | _                   rewrite eq₁ = vbool-nat ⊢e∷t
  ...| _                    | inj₁ (VBool y , eq₂) rewrite eq₂ = vbool-nat ⊢e∷t₁
  ...| inj₁ (VNat x , eq₁)  | inj₂ (e₂' , e₂↝e₂') rewrite eq₁
    = inj₂ ((val (VNat x) < e₂') , ↝-Lt-r x e₂↝e₂')
  ...| inj₂ (e₁' , e₁↝e₁') | _
    = inj₂ ((e₁' < e₂) , ↝-Lt-l e₂ e₁↝e₁')
  progress (T-cond ⊢e∷t ⊢e∷t₁ ⊢e∷t₂) with progress ⊢e∷t
  ... | inj₁ (VNat x , eq₁) rewrite eq₁ = vnat-bool ⊢e∷t
  ... | inj₁ (VBool true , eq₁) rewrite eq₁ = inj₂ (_ , ↝-cond-true _ _)
  ... | inj₁ (VBool false , eq₁) rewrite eq₁ = inj₂ (_ , ↝-cond-false _ _)
  ... | inj₂ (e₁' , e₁↝e₁') = inj₂ (cond e₁' _ _ , ↝-cond e₁↝e₁')
```

- Semântica de múltiplos passos e alguns teoremas.

```agda
  data _↝*_ : Exp → Exp → Set where
    done : ∀ {v} → (val v) ↝* (val v)
    step : ∀ {e₁ e₂ e₃} → e₁ ↝ e₂
                        → e₂ ↝* e₃
                        → e₁ ↝* e₃
```

- Lema 1: combinando duas semântica multi-step com operador de adição

```agda
  ↝*-⊕ : ∀ {e n e' n'} → e ↝* val (VNat n)
                        → e' ↝* val (VNat n')
                        → (e ⊕ e') ↝* val (VNat (n + n'))
  ↝*-⊕ done done = step (↝-Add _ _) done
  ↝*-⊕ done (step x e↝*n') = step (↝-Add-r x) (↝*-⊕ done e↝*n')
  ↝*-⊕ (step x e↝*n) done = step (↝-Add-l x) (↝*-⊕ e↝*n done)
  ↝*-⊕ (step x e↝*n) (step x₁ e↝*n') = step (↝-Add-l x) (↝*-⊕ e↝*n (step x₁ e↝*n'))
```

- Lema 2: combinando duas semântica multi-step com operador de menor

```agda
  ↝*-< : ∀ {e n e' n'} → e ↝* val (VNat n)
                        → e' ↝* val (VNat n')
                        → (e < e') ↝* val (VBool (n <? n'))
  ↝*-< done done = step (↝-Lt _ _) done
  ↝*-< done (step x e↝*n') = step (↝-Lt-r _ x) (↝*-< done e↝*n')
  ↝*-< (step x e↝*n) done = step (↝-Lt-l (val (VNat _)) x) (↝*-< e↝*n done)
  ↝*-< (step x e↝*n) (step x₁ e↝*n') = step (↝-Lt-l _ x) (↝*-< e↝*n (step x₁ e↝*n'))
```

- Lema 3: combinando duas semântica multi-step para cond/true.

```agda
  ↝*-cond-true : ∀ {e e' v' e''} → e ↝* (val (VBool true))
                                    → e' ↝* val v'
                                    → (cond e e' e'') ↝* val v'
  ↝*-cond-true done e↝*n' = step (↝-cond-true _ _) e↝*n'
  ↝*-cond-true (step x e↝*n) e↝*n' = step (↝-cond x) (↝*-cond-true e↝*n e↝*n')
```

- Lema 4: combinando duas semântica multi-step para cond/false.

```agda
  ↝*-cond-false : ∀ {e e' v'' e''} → e ↝* (val (VBool false))
                                    → e'' ↝* val v''
                                    → (cond e e' e'') ↝* val v''
  ↝*-cond-false done e↝*n' = step (↝-cond-false _ _) e↝*n'
  ↝*-cond-false (step x e↝*n) e↝*n' = step (↝-cond x) (↝*-cond-false e↝*n e↝*n')
```

- Teorema de type soundness

```agda
  normal-form : Exp → Set
  normal-form e = ¬ ∃ (λ e' → e ↝ e')

  value : Exp → Set
  value (val x) = ⊤
  value _ = ⊥

  stuck : Exp → Set
  stuck e = normal-form e × ¬ (value e)

  soundness : ∀ {e t e'} → ⊢ e ∷ t → e ↝* e' → ¬ (stuck e')
  soundness ⊢e∷t done = λ z → proj₂ z tt
  soundness ⊢e∷t (step e↝e₂ e₂↝*e') with preservation e↝e₂ ⊢e∷t
  ...| ⊢e₂∷t with soundness ⊢e₂∷t e₂↝*e'
  ...| ¬e'stuck = λ z → ¬e'stuck (proj₁ z , proj₂ z)
```

Estilo intrínsico
=================

- Agora vamos considerar um estilo diferente de formalização: o intrínsico, em que
apenas programas bem tipados são considerados.

- Primeiro, vamos definir a sintaxe intrínsica.

```agda
module Intrinsic where
  open Extrinsic using (_<?_)

  data Type : Set where
    nat bool : Type

  ⟦_⟧T : Type → Set
  ⟦ nat ⟧T  = ℕ
  ⟦ bool ⟧T = Bool

  data Exp : Type → Set where
    val  : ∀ {t} → ⟦ t ⟧T → Exp t
    _⊕_  : Exp nat → Exp nat → Exp nat
    _<_  : Exp nat → Exp nat → Exp bool
    cond : ∀ {t} → Exp bool → Exp t → Exp t → Exp t
```

- Podemos definir o teorema de type soundness usando um
interpretador da sintaxe tipada.
    - O teorema de soundness é garantido por construção
      pois o resultado da função eval são exatamente
      os valores da expressão.

```agda
  eval : ∀ {t} → Exp t → ⟦ t ⟧T
  eval (val x) = x
  eval (e ⊕ e₁) = eval e + eval e₁
  eval (e < e₁) = eval e <? eval e₁
  eval (cond e e₁ e₂) = if eval e then eval e₁ else eval e₂
```

# Referências

- Amin, Nada; Rompf, Tiark. Type Soundness Proofs with Definitional Interpreters.
POPL 2017.
