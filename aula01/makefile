default: slides

slides:
	pandoc -f markdown+lhs --mathjax -t revealjs -s -o slides.html aula01.lagda.md -V theme=white -V revealjs-url=../revealjs -V slidenum=true

pdf:
	pandoc -f markdown+lhs --mathjax -t beamer -s -o slides.pdf aula01.lagda.md
