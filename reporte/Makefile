all: reporte.pdf


reporte.tex : reporte.lagda unicode.fmt
	lhs2TeX --agda reporte.lagda -o reporte.tex

upperbound=4
LTX_OPTS=-halt-on-error

reporte.pdf : reporte.tex  biblio.bib
	pdflatex $(LTX_OPTS) reporte.tex
	bibtex reporte
	pdflatex $(LTX_OPTS) reporte.tex

clean :
	rm -f *.aux *.bbl *blg *.log *.ptb *.tex reporte.pdf
