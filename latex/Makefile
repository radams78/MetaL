main.pdf: main.tex Grammar/Taxonomy.tex STLC/Grammar.tex
	latexmk -g -pdf -interaction=nonstopmode main
Grammar/Taxonomy.tex: ../agda/Grammar/Taxonomy.lagda
	cd ..; cd agda; agda -i ${AGDA_LIBDIR} -i . --latex Grammar/Taxonomy.lagda --latex-dir=../latex
STLC/Grammar.tex: ../agda/STLC/Grammar.lagda
	cd ..; cd agda; agda -i ${AGDA_LIBDIR} -i . --latex STLC/Grammar.lagda --latex-dir=../latex