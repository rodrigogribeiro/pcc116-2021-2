---
title: Programação com tipos dependentes - Parte II
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
---

<!--
```agda
module aula18 where

open import Basics.Admit

open import Data.Bool.Bool
open import Data.Char.Char
open import Data.Empty.Empty
open import Data.Function.Function
open import Data.List.List
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sigma.Sigma   renaming (_,_ to _,,_)
open import Data.String.String hiding (_++_)
open import Data.Sum.Sum
open import Data.Unit.Unit
open import Data.Vec.Vec renaming (_++_ to _++V_)
```
-->


# Objetivos

- Uso de tipos para garantir a correção de uma
função para formatação de saída (a lá `printf`).

- Apresentação do conceito de universo e de seu
uso para definição de linguagens para descrição
de dados.

- Desenvolvimento de uma função para demonstração
de equações sobre monóides.


# Formalização de formatação de dados


- O uso de funções para formatação de strings é
presentes em diversas linguagens de programação.

- A função printf de C é, provavelmente, seu
exemplo mais famoso.

- Para construir uma versão tipável de printf,
vamos definir um tipo para representar formatos.

```agda
data Format : Set where
  ℕ-Format : Format     → Format
  S-Format : Format     → Format
  Literal  : (c : Char) → Format → Format
  Empty    : Format
```

- Em seguida, vamos definir uma função para
realizar o parsing de uma string de formatos.

```agda
parseFormat : List Char → Format
parseFormat ('%' ∷ 'n' ∷ cs) = ℕ-Format (parseFormat cs)
parseFormat ('%' ∷ 's' ∷ cs) = S-Format (parseFormat cs)
parseFormat (c ∷ cs) = Literal c (parseFormat cs)
parseFormat [] = Empty
```

- A partir de uma representação de formatos,
podemos calcular o tipo de uma função para
impressão seguindo o formato especificado.

```agda
⟦_⟧F : Format → Set
⟦ ℕ-Format f ⟧F  = ℕ      → ⟦ f ⟧F
⟦ S-Format f ⟧F  = String → ⟦ f ⟧F
⟦ Literal c f ⟧F = ⟦ f ⟧F
⟦ Empty ⟧F       = String
```

- Usando a função para parsing de formato e ⟦_⟧F,
podemos definir o tipo de printf:

```agda
Printf : String → Set
Printf = ⟦_⟧F ∘ parseFormat ∘ stringToList
```
- A definição de printf é baseada na ideia de que
formatos são um "programa" a ser executado. Logo,
vamos definir um interpretador de formatos.

```agda
showNat : ℕ → List Char
showNat = stringToList ∘ ℕtoString

interpFormat : List Char → (f : Format) → ⟦ f ⟧F
interpFormat s (ℕ-Format f)
  = λ n → interpFormat (s ++ showNat n) f
interpFormat s (S-Format f)
  = λ s' → interpFormat (s ++ (stringToList s')) f
interpFormat s (Literal c f)
  = interpFormat (s ++ [ c ]) f
interpFormat s Empty = (stringFromList s)
```

- Usando o interpretador acima, a definição
de printf é imediata.

```agda
printf : (s : String) → Printf s
printf s = interpFormat [] (parseFormat (stringToList s))

_ : String
_ = printf "Hello %s! %n is the answer!" "World" 42
```

# Uma linguagem para descrição de dados

- Atualmente, existem diversos formatos de dados: sejam
textuais ou mesmo binários.

- Um problema recorrente é o de produzir parsers e
pretty genéricos para esses formatos.

- Uma alternativa para isso, é a criação de linguagens
para descrição de formatos de dados.

- Porém, como descrever os tipos suportados por formatos
que podem ser expressos?

- Para isso, vamos definir um universo, composto por códigos:

```agda
data Code : Set where
  BIT  : Code
  CHAR : Code
  NAT  : Code
  VEC  : Code → ℕ → Code
```

- e de uma função que os interpreta.

```agda
data Bit : Set where
  O I : Bit

el : Code → Set
el BIT  = Bit
el CHAR = Char
el NAT  = ℕ
el (VEC c n) = Vec (el c) n
```

- Aplicação: Definir um parser para valores dos
tipos descritos pelo universo.

```agda
readNat : Vec Bit 8 → ℕ
readNat bs = {!!}

readChar : Vec Bit 8 → Char
readChar = ℕtoChar ∘ readNat

read : {c : Code} → List Bit → Maybe (el c × List Bit)
read {BIT} [] = nothing
read {BIT} (b ∷ bs) = just (b , bs)
read {CHAR} (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs)
  = just ( readChar (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ [])
         , bs
         )
read {CHAR} _ = nothing
read {NAT} (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs)
  = just ( readNat (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ [])
         , bs
         )
read {NAT} _ = nothing
read {VEC c n} bs = {!!}
```

- Utilizando o universo descrito pelo tipo Code e
a função el, podemos definir um novo universo
para descrever formatos de arquivos.

```agda
data File : Set
⟦_⟧ : File → Set

data File where
  Bad  : File
  End  : File
  Base : Code → File
  Plus : File → File → File
  Skip : File → File → File
  Read : (f : File) → (⟦ f ⟧ → File) → File

⟦ Bad ⟧ = ⊥
⟦ End ⟧ = ⊤
⟦ Base x ⟧ = el x
⟦ Plus f f₁ ⟧ = ⟦ f ⟧ ⊎ ⟦ f₁ ⟧ 
⟦ Skip f f₁ ⟧ = ⟦ f₁ ⟧
⟦ Read f x ⟧ = Σ ⟦ f ⟧ (λ y → ⟦ x y ⟧ )
```

- A partir do universo definido, podemos criar
alguns combinadores. O primeiro é o que especifica
um caractere em um formato.

```agda
char : Char → File
char c = Read (Base CHAR)
              (λ c' → if c ≟ c'
                       then End
                       else Bad)
```

- Outro combinador é o `satisfy` que permite
definir formatos baseados em um predicado.

```agda
satisfy : (f : File) → (⟦ f ⟧ → Bool) → File
satisfy f p
  = Read f (λ x → if p x then End else Bad)
```

- Combinadores monádicos para File formats.

```agda
infixl 1 _>>=_ _>>_

_>>_ : File → File → File
f >> f' = Skip f f'

_>>=_ : (f : File) → (⟦ f ⟧ → File) → File
f >>= g = Read f g
```

- Exemplo: formato pbm

```agda
pbm : File
pbm
  = char 'P'  >>
    char '4'  >>
    char ' '  >>
    Base NAT  >>= λ n →
    char ' '  >>
    Base NAT  >>= λ m →
    char '\n' >>
    Base (VEC (VEC BIT n) m) >>= λ bs →
    End
```

- Usando o universo File, podemos definir
parsers e pretty-printers genéricos.

```agda
parser : (f : File) → List Bit → Maybe (⟦ f ⟧ × List Bit)
parser Bad bs = nothing
parser End bs = just (tt , bs)
parser (Base x) bs = {!!}
parser (Plus f f₁) bs = {!!}
parser (Skip f f₁) bs = {!!}
parser (Read f x) bs = {!!}
```
