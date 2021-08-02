---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Apresentação da disciplina
---

<!--
```agda
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

module aula01 where

postulate admitted : {A : Set} → A
```
-->


Objetivos
=========

- Motivação para a disciplina.

- Apresentar os critérios de avaliação, ementa e 
bibliografia.


Motivação
=========


Teste de software
=================

- Abordagem padrão para garantia da qualidade 
em software.

Teste de software
=================

- Úteis para encontrar erros simples.

Teste de software
=================

- Uso de um grande número de testes é capaz
de cobrir a maior parte do comportamento de 
programas.

Teste de software
=================

- Porém, como apontado por Dijkstra, testes
apenas atestam a presença e nunca a ausência
de bugs.

Testes
======

- O uso de testes não é exclusividade da ciência da computação.

- Matemáticos usam testes como uma forma de validar sua 
intuição.

Exemplo
======

- Suponha que um matemático descubra, usando métodos numéricos que:

$$
\int_{0}^{\infty}\dfrac{\sin(t)}{t}\mathrm{d} t = \dfrac{\pi}{2}
$$

Exemplo
======

- Após algumas experimentações, ele supõe que:

$$
\int_{0}^{\infty}\dfrac{\sin(t)}{t}\dfrac{\sin(\frac{t}{101})}{\frac{t}{101}}\mathrm{d} t = \dfrac{\pi}{2}
$$

Exemplo
======

- O próximo teste confirma que:

$$
\int_{0}^{\infty}\dfrac{\sin(t)}{t}\dfrac{\sin(\frac{t}{201})}{\frac{t}{201}}\mathrm{d} t = \dfrac{\pi}{2}
$$

Exemplo
=======

- Confiante, o matemática postula que:

$$
\forall n. n \in \mathbb{N} \to \int_{0}^{\infty}\dfrac{\sin(t)}{t}\dfrac{\sin(\frac{t}{100n + 1})}{\frac{t}{(100n + 1)}}\mathrm{d} t = \dfrac{\pi}{2}
$$

Exemplo
=======

- Porém, a confiança é logo derrotada pois para $n = 15$, 
a igualdade anterior não é válida.

Testes
======

- Na matemática, testes são utilizados para ajudar na 
compreensão de problemas.

Testes
======

- Para ter certeza de que uma propriedade de interesse é válida,
matemáticos usam _provas_.


Correção de programas
=====================

- De maneira similar, se desejamos garantir que um programa possui
uma propriedade de interesse, devemos usar _provas_ e não 
_testes_.

Correção de programas
=====================

- Porém, quem garante que as provas estão corretas?

- Nos últimos anos, diversos trabalhos usam os chamados 
_assistentes de provas_ para atestar a validade de demonstrações.

Assistentes de provas
=====================

- Linguagens de programação que reduzem o problema de 
verificar demonstrações à tarefa de verificar tipos em 
um programa.

Assistentes de provas
=====================

- Propriedades são expressas como tipos...

- Programas possuindo esses tipos correspondem a 
provas destas propriedades.

Linguagem Agda
==============

- Neste curso, utilizaremos a linguagem Agda, que pode ser entendida
como uma linguagem funcional e um assistente de provas.

Linguagem Agda
==============

- Agda possui um sistema de tipos muito expressivo.
- Capaz de representar propriedades quaisquer da lógica.

Linguagem Agda
==============

- Logo, podemos especificar programas simplesmente usando um
tipo capaz de representar sua propriedade de correção.

Linguagem Agda
==============

- Com isso, o compilador de Agda é capaz de verificar se a
implementação do programa atende a sua especificação.

Exemplo
=======

- Uma função que retorna o quociente e o resto de 
dois números inteiros seria:

```agda
div : ℕ → ℕ → ℕ × ℕ
div n m = admitted
```

Exemplo
=======

- O tipo anterior pode ser expresso em linguagens
funcionais como Haskell ou ML.

Exemplo
=======

- Porém, esse tipo não é capaz de garantir que a função `div`
realmente implementa a divisão de números naturais.

Exemplo
=======

- Dividir $n$ por $m$ resulta em $(q,r)$:
   - $n = qm + r$
   - $r < m$

Exemplo
=======

- Expressando em lógica, temos:

$$
\forall n\,m. n \in \mathbb{N} \to m \in \mathbb{N} \to \exists q\,r. n = mq + r \land q < r
$$


Exemplo
=======

- Essa propriedade expressa como um tipo, seria:

```agda
div1 : ∀ (n m : ℕ) → ∃₂ (λ q r → n ≡ m * q + r × r < m)
div1 n m = admitted
```

Exemplo
=======

- Usando o tipo anterior, o compilador de Agda garante
que a implementação de `div1` satisfaz a propriedade
codificada pelo tipo:

```agda
-- ∀ (n m : ℕ) → ∃₂ (λ q r → n ≡ m * q + r × r < m)
```

Aplicações
==========

- Assistentes de provas tem sido usados com sucesso na verificação
de diversas demonstrações não triviais.

Aplicações
==========

- Compiladores: CompCert
- Sistemas operacionais (seL4, certiKOS)
- Provas matemáticas: Teorema das 4 cores e Feith-Thompson.


Ementa
======

Ementa
======

- Revisão de lógica e programação funcional.

- $\lambda$-cálculo atipado e tipado simples.

- Teoria de tipos de Martin-Löf.

Ementa
======

- Introdução à linguagem Agda.

- Indução e recursão.

- Formalizações e programação com tipos dependentes.

Ementa
======

- Noções de semântica formal.

- Introdução à homotopy type theory.

Critérios de Avaliação
======================

Avaliação
=========

- Listas de exercícios sobre o conteúdo abordado.

Software
========

Software
========

- Utilizaremos as linguagens Agda e Haskell.

- Editor de texto (recomenda-se Emacs ou vscode).

- Slides produzidos usando pandoc e reveal.js.

Material
========

- Vídeos serão disponibilizados pelo Moodle.

- Código de exemplo e slides serão disponibilizados
no seguinte repositório:

[https://github.com/rodrigogribeiro/pcc116-2021-2]


Atendimento
===========

Atendimento
===========

- Aulas serão assíncronas. Vídeos do conteúdo serão
disponibilizados pelo YouTube.

- Os participantes serão adicionados em um canal
do Slack para atendimento.

Atendimento
===========

- Atendimento também poderá ser feito por e-mail:

[rodrigo.ribeiro@ufop.edu.br]


Bibliografia
============


Bibliografia
============

- MIMRAM, Samuel. Program = Proof, 2020.

- Wadler, et. al. Programming Language Foundations in Agda, 2020.

- NEDERPELT, Rob; Geuvers, Herman. Type Theory and Formal Proof. Cambridge University Press, 2014.

Bibliografia
============

- Artigos relevantes sobre os temas abordados na disciplina.
