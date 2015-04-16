all: presentation.pdf

.PHONY: all

%.pdf: %.tex
	pdflatex $< && ( grep -s "Rerun to get" $$(basename $< .tex) && pdflatex $< || true )

%.tex: %.lhs
	lhs2TeX $< > $@

%.aux: %.tex
	luatex $<

%.bbl: %.aux %.bib
	bibtex $$(basename $< .aux)

