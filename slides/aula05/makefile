default: slides

slides:
	pandoc -s --mathjax -t revealjs -o slides.html Aula05.md -V theme=white -V revealjs-url=../revealjs -V slidenum=true --slide-level 2

pdf:
	pandoc --mathjax -t beamer -s -o slides.pdf Aula05.md
