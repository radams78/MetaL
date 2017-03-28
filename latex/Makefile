LAGDAFILES = $(shell find ../agda -name *.lagda)
TEXFILES = $(LAGDAFILES:../agda/%.lagda=%.tex)
AGDA_LIBDIR ?= /usr/share/agda-stdlib-0.13

lmain.pdf: main.tex $(TEXFILES)
	latexmk -g -pdf main
%.tex: ../agda/%.lagda
	cd ../agda; agda -i $(AGDA_LIBDIR) -i . --latex $*.lagda --latex-dir=../latex
