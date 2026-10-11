# Build the manuscript and the source archive for arXiv.
#
#   make            build main.pdf
#   make figures    redraw the figures in figures/ (python3 with numpy and matplotlib)
#   make arxiv      build arxiv/ambidextrous-sofa.tar.gz, the files to upload to arXiv,
#                   and check that they compile on their own
#   make clean      remove the build products

MAIN := main
SECTIONS := $(shell python3 -c 'import re; print(" ".join(x+".tex" for x in re.findall(r"\\input\{(sections/[^}]+)\}", open("main.tex").read())))')
SRC  := $(MAIN).tex macros.tex refs.bib $(SECTIONS) $(wildcard figures/*.pdf)
TAR  := arxiv/ambidextrous-sofa.tar.gz

.PHONY: pdf figures check arxiv clean
pdf: $(MAIN).pdf

$(MAIN).pdf: $(SRC)
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

figures:
	python3 figures/make_figures.py

check: $(MAIN).pdf
	@if rg -n -i 'undefined|multiply defined|Overfull|LaTeX Error' $(MAIN).log; then echo "manuscript check failed"; exit 1; fi
	@if rg -n 'Warning--' $(MAIN).blg; then echo "bibliography check failed"; exit 1; fi

# arXiv compiles the upload itself, with its own BibTeX run only when there is no .bbl, so the
# archive carries the .bbl; the test build below uses pdflatex alone, like a fresh checkout.
arxiv: check
	rm -rf arxiv
	mkdir -p arxiv/src/sections arxiv/src/figures
	cp $(MAIN).tex macros.tex refs.bib $(MAIN).bbl arxiv/src/
	cp $(SECTIONS) arxiv/src/sections/
	cp figures/*.pdf arxiv/src/figures/
	cd arxiv/src && pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null \
	  && pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null \
	  && pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null
	@if rg -n -i 'undefined|multiply defined|Overfull|LaTeX Error' arxiv/src/$(MAIN).log; then echo "source archive check failed"; exit 1; fi
	tar -czf $(TAR) -C arxiv/src $(MAIN).tex macros.tex refs.bib $(MAIN).bbl sections figures
	@echo "$(TAR): $$(tar -tzf $(TAR) | wc -l) entries, test build $$(pdfinfo arxiv/src/$(MAIN).pdf | rg Pages)"

clean:
	latexmk -C $(MAIN).tex
	rm -rf arxiv
