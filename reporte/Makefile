all: correct-compiler.pdf


reporte.tex : reporte.lagda unicode.fmt
	lhs2TeX --agda reporte.lagda -o reporte.tex

upperbound=4
LTX_OPTS=-halt-on-error

reporte.pdf : reporte.tex  biblio.bib
	pdflatex $(LTX_OPTS) reporte.tex
	bibtex reporte
	pdflatex $(LTX_OPTS) reporte.tex

correct-compiler.tex : correct-compiler.lagda unicode.fmt
	lhs2TeX --agda correct-compiler.lagda -o correct-compiler.tex

correct-compiler.pdf : correct-compiler.tex  biblio.bib
	pdflatex $(LTX_OPTS) correct-compiler.tex
	bibtex correct-compiler
	pdflatex $(LTX_OPTS) correct-compiler.tex

clean :
	rm -f *.aux *.bbl *blg *.log *.ptb *.tex correct-compiler.pdf reporte.pdf
