LAGDAFILES = $(shell find agda -name *.lagda)
TEXFILES = $(LAGDAFILES:agda/%.lagda=latex/%.tex)
AGDA_LIBDIR ?= /usr/share/agda-stdlib-0.13

latex/main.pdf: latex/main.tex $(TEXFILES)
	cd latex; latexmk -g -pdf -interaction=nonstopmode main
latex/%.tex: agda/%.lagda
	cd agda; agda -i $(AGDA_LIBDIR) -i . --latex $*.lagda --latex-dir=../latex
