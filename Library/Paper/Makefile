all: paper.pdf

upperbound=4
LTX_OPTS=-halt-on-error

paper.tex : introduction.lagda univ-alg.lagda transforming-algebras.lagda paper.lagda conclusions.lagda equational.lagda unicode.fmt
	lhs2TeX --agda paper.lagda -o paper.tex

paper.pdf : paper.tex  biblio.bib
	pdflatex $(LTX_OPTS) paper.tex
	bibtex paper
	pdflatex $(LTX_OPTS) paper.tex
	pdflatex $(LTX_OPTS) paper.tex

clean :
	rm -f *.aux *.bbl *blg *.log *.ptb *.tex paper.pdf
