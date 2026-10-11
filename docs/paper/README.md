# Manuscript

- [Read the paper](main.pdf): *Optimality and uniqueness of Romik's ambidextrous sofa*.
- The introduction lays out the optimality and uniqueness strategies and explains the organization.
- Separate sections cover the motion reduction, selection of maximizers, variations, full-turn geometry, support-function bound, proper-turn exclusion, equality caps, and recovery of the body.
- Mathematical appendices give the ordinary-sofa input, Romik's construction and exact area, and the supporting estimates.
- [Review and checks](REVIEW.md) records the mathematical review and build checks.

## Build

From this directory, with `latexmk`, `pdflatex`, `bibtex`, `rg`, and `pdfinfo` installed:

```sh
make             # main.pdf
make check       # references, bibliography, and overflowing lines
make arxiv       # source archive, with a separate test build
```

- `make arxiv` includes the manuscript sources, bibliography, and six figure PDFs, then tests compilation with `pdflatex` alone.
- `make figures` regenerates the figures with Python, NumPy, and Matplotlib and checks the illustrated geometry numerically.
- `make clean` removes the PDF and temporary build products, including the source archive.

## Source and notation

- [main.tex](main.tex) contains the title, abstract, section order, and bibliography settings.
- [macros.tex](macros.tex) defines the notation.
- [sections/](sections) contains the text; [refs.bib](refs.bib) contains the references.
- Section 2 defines the hallways, motions, caps, roofs, swept niche `n`, partial barrier `N`, and score `P`.
- Appendix B defines the root `Y`, constant `M`, reference support coordinates, cap, hull, niche, and sofa.
