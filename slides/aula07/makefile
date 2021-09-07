default: slides

slides:
	pandoc -s --mathjax -t revealjs -o slides.html Aula07.md -V theme=white -V revealjs-url=../revealjs -V slidenum=true --slide-level 2

pdf:
	pandoc --mathjax -t beamer -s -o slides.pdf Aula07.md
