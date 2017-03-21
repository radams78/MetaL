latex/main.pdf: latex/main.tex latex/Grammar/Taxonomy.tex
	cd latex; latexmk -g -pdf main
latex/Grammar/Taxonomy.tex: agda/Grammar/Taxonomy.lagda
	cd agda; agda -i ${AGDA_LIBDIR} -i . --latex Grammar/Taxonomy.lagda --latex-dir=../latex
