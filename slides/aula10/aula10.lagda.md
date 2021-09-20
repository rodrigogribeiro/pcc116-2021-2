---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Introdução à linguagem Agda
---

# Objetivos

<!--
```agda
module aula10 where

postulate admitted : {A : Set} → A

infix 4 _≡_

data _≡_ {l}{A : Set l}(x : A) : A → Set l where
  refl : x ≡ x

trans : ∀ {l}{A : Set l}{x y z : A} →
        x ≡ y →
        y ≡ z →
        x ≡ z
trans refl refl = refl

{-# BUILTIN EQUALITY _≡_ #-}
```
-->

## Objetivos

- Discutir sobre o ambiente de desenvolvimento para a linguagem Agda.

- Introduzir conceitos básicos sobre a linguagem Agda.


# Ambiente

## Ambiente

- O primeiro passo para o desenvolvimento em Agda, consiste em instalar
o compilador da linguagem.

- A instalação pode ser encontrada em:

<https://wiki.portal.chalmers.se/agda/Main/Download>

## Ambiente

- Recomendo a utilização de editores de texto com suporte à linguagem Agda.

- Boas opções são o Emacs e o VSCode.

## Ambiente

- Não é necessário instalar a biblioteca padrão de Agda.

- Durante a disciplina, vamos desenvolver tudo "do zero".

## Ambiente

- Após a configuração do ambiente, podemos iniciar o estudo da linguagem 
usando o tipo de dados `Bool`, de valores lógicos.

# Booleanos

## Booleanos

- O tipo de dados `Bool` é definido como:

```agda
data Bool : Set where
   true  : Bool
   false : Bool
```

## Booleanos

- A linha 

    data Bool : Set

- Define o tipo de dados `Bool` tendo o tipo `Set`.

- `Set` é o tipo de "tipos" em Agda...

## Booleanos

- Após a palavra reservada `where`, temos a definição dos
_construtores_ do tipo `Bool`:

    true : Bool

    false : Bool

- Que indicam que os dois únicos valores para o tipo booleano
são as constantes `true` e `false`.

## Booleanos

- Podemos compilar um arquivo Agda usando o comando "Agda->Load"

- Atalho no Emacs: Ctrl + c Ctrl + l

## Booleanos

- Agora que vimos como carregar código Agda, podemos definir algumas
funções sobre este.


## Booleanos

- A primeira função que vamos considerar é a negação.

- O tipo da função de negação é:

    not : Bool → Bool

## Booleanos

- Vamos definir esta função por casamento de padrão sobre
o parâmetro de entrada.

```agda
not : Bool → Bool
not true  = false
not false = true
```

## Booleanos

- De maneira similar, podemos definir a operação de conjunção.

```agda
infixr 6 _&&_

_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false
```

## Booleanos

- Após essa breve introdução, vamos considerar a importante noção
de igualdade proposicional em Agda.

# Igualdade

## Igualdade

- Igualdade é um conceito central na matemática e na teoria de tipos.

## Igualdade

- Em assistentes de prova, como Agda, existem pelo menos, duas definições
de igualdade:
    - Igualdade por definição (_definitional equality_).
    - Igualdade proposicional (_propositional equality_).

## Igualdade

- A igualdade por definição consiste é implementada pela linguagem Agda.

## Igualdade

- A igualdade por definição consiste é implementada pela linguagem Agda.

- Consiste no processo de redução, seguido por um teste de α-equivalência

## Igualdade

- A igualdade por definição consiste é implementada pela linguagem Agda.

- Consiste no processo de redução, seguido por um teste de α-equivalência

- A priori, inacessível ao programador.

## Igualdade

- Se a igualdade por definição é inacessível ao desenvolvedor, como
podemos mostrar que dois valores são iguais?

## Igualdade

- A ideia usada por assistentes de prova é usar um tipo que
representa uma aproximação da igualdade por definição.

## Igualdade

- A ideia usada por assistentes de prova é usar um tipo que
representa uma aproximação da igualdade por definição.

- Esse tipo é conhecido por igualdade proposicional.

## Igualdade

- A igualdade proposicional é representada pelo tipo `_≡_`

- O símbolo `≡` pode ser digitado usando `\==`.

## Igualdade

- A igualdade proposicional é um tipo Agda e, portanto,
possui construtores de valores.

- Em especial, esse tipo possui um único construtor:

    refl : x ≡ x

## Igualdade

- Exemplo

```agda
true-refl : true ≡ true
true-refl = refl
```

## Igualdade

- A igualdade proposicional "reflete" a igualdade por definição
porquê para testar que `refl` é um construtor válido para
deduzir `x ≡ y`, temos que realizar a normalização de ambos os
lados de uma equação.

## Igualdade

- Exemplo

```agda
not-not-true : not (not true) ≡ true
not-not-true = refl
```

## Igualdade

- No exemplo anterior, o type-checker de Agda reduz o termo
`not (not true)` até a forma normal.

- E então compara ambos os lados da equação.

## Igualdade

- Dessa forma, a seguinte função é recusada pelo type-checker de
Agda

    false-true : false ≡ true

    false-true = refl

- Pois os construtores são evidentemente diferentes e Agda retornará
uma mensagem de erro indicando esse fato.

## Igualdade

- Em matemática, é comum representarmos uma dedução de igualdades
como uma cadeia de equações, como a seguir:

     (true && false) && not true ≡

     (true && false) && false    ≡

     false && false              ≡

     false


## Igualdade

- Agda possui um mecanismo simples e expressivo para criação de
operadores.

- Basta indicar com "_" a posição de um argumento para o operador.

## Igualdade

- Adicionalmente, podemos declarar a associatividade e precedência
de operadores.

## Igualdade

- Usando esse mecanismo, podemos definir operadores para o desenvolvimento
de equações.

## Igualdade

- Iniciando o desenvolvimento de uma equação

```agda
infix 1 begin_

begin_ : ∀ {l}{A : Set l}{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y
```

## Igualdade

- Combinando equações (sem justificativa)
   - Símbolo ⟨ é representado por `\<`
   - Símbolo ⟩ é representado por `\>`

```agda
infixr 2 _≡⟨⟩_

_≡⟨⟩_ : ∀ {l}{A : Set l}(x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y
```

## Igualdade

- Combinando equações (com justificativa)

```agda
infixr 2 step-≡ 

step-≡ : ∀ {l}{A : Set l}(x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
```

## Igualdade

- Finalizando uma sequência de equações
    - O símbolo ∎ é represntado por `\qed`. 

```agda
infix 3 _∎

_∎ : ∀ {l}{A : Set l}(x : A) → x ≡ x
_∎ _ = refl
```

## Igualdade

- Exemplo: `not (not true) ≡ true`

```agda
_ : not (not true) ≡ true
_ = begin
      not (not true) ≡⟨⟩
      not false      ≡⟨⟩
      true
    ∎
```

# Booleanos

## Booleanos

- Após esse breve interlúdio sobre a igualdade,
podemos usar Agda para demonstrar alguns fatos
sobre o tipo `Bool`.

## Booleanos

- Primeiro teorema: Para todo `b : Bool`, temos que `not (not b) ≡ b`.

## Booleanos


- De acordo com a correspondência de Curry-Howard, temos que o teorema
anterior pode ser representado por uma função Agda.

- O tipo desta função é:

    (b : Bool) → not (not b) ≡ b


## Booleanos

- Dedução usando o "IDE" de Agda.

```agda
not-elim : (b : Bool) → not (not b) ≡ b
not-elim b = {!!}
```

## Booleanos

- Outros exemplos

```agda
not-not-false : not (not false) ≡ false
not-not-false = {!!}
```

## Booleanos

- Exemplo

```agda
&&-idem : (b : Bool) → b && b ≡ b
&&-idem = {!!}
```

## Booleanos

- Agda permite definirmos parâmetros como _implícitos_.

- Parâmetros implícitos são definidos entre chaves.

```agda
&&-idem-implicit : {b : Bool} → b && b ≡ b
&&-idem-implicit {true}  = refl
&&-idem-implicit {false} = refl
```

## Booleanos

- Exemplo

```agda
_ : true && true ≡ true
_ = &&-idem-implicit
```

## Booleanos

- Considere o seguinte fato óbvio sobre a conjunção:

     true && b ≡ b

## Booleanos

- Esse fato é facilmente demonstrado:

```agda
&&-true-left : {b : Bool} → true && b ≡ b
&&-true-left = refl
```
## Booleanos

- Note que a igualdade `true && b ≡ b` é verdadeira
devido a seguinte equação:

    true && b = b

## Booleanos

- Essa prova é uma consequência direta da igualdade por definição
implementada pelo type-checker de Agda.

## Booleanos

- Considere, agora, o seguinte fato:

    b && true ≡ b

## Booleanos

- Porém, esse fato não possui uma demonstração imediata como o anterior...

    &&-true-right : {b : Bool} → b && true ≡ b
    &&-true-right = refl -- agda complains!!

## Booleanos

- O que aconteceu?


## Booleanos

- O que aconteceu?

- Observe que `b && true` não é igual a `b` usando a apenas definição de `&&`:

    true  && b = b

    false && _ = false

## Booleanos

- Para demonstrar esse fato, vamos realizar casamento de padrão sobre o tipo `Bool`

```agda
&&-true-right : {b : Bool} → b && true ≡ b
&&-true-right {b} = {!!}
```

## Booleanos

- Exemplo: teorema com hipóteses

```agda
&&-≡-true-left : (a b : Bool) → a && b ≡ true → a ≡ true
&&-≡-true-left a b a&&b≡true = {!!}
```

# Exercícios

## Exercícios

- Todos os exercícios para essa semana estarão disponíveis no repositório

<https://github.com/rodrigogribeiro/pcc116-agda-lib>


