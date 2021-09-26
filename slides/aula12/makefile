default: slides

slides:
	pandoc  --mathjax -t revealjs -s -o slides.html aula12.lagda.md -V theme=white -V revealjs-url=../revealjs -V slidenum=true --slide-level 2

pdf:
	pandoc  --mathjax -t beamer -s -o slides.pdf aula12.lagda.md
