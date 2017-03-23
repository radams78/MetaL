LAGDAFILES = $(shell find agda -name *.lagda)
TEXFILES = $(LAGDAFILES:agda/%.lagda=latex/%.tex)

latex/main.pdf: latex/main.tex $(TEXFILES)
	cd latex; latexmk -g -pdf main
latex/%.tex: agda/%.lagda
	cd agda; agda -i ${AGDA_LIBDIR} -i . --latex $*.lagda --latex-dir=../latex
