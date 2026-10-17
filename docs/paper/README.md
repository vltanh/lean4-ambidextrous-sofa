# Manuscript

- [Read the paper](main.pdf): *Optimality and uniqueness of Romik's ambidextrous sofa*.
- The introduction lays out the optimality and uniqueness strategies and explains the organization.
- Separate sections cover the motion reduction, selection of maximizers, variations, full-turn geometry, support-function bound, proper-turn exclusion, equality caps, and recovery of the body.
- Mathematical appendices give the ordinary-sofa input, Romik's construction and exact area, and the supporting estimates.
- [Review and checks](REVIEW.md) records the mathematical review and build checks.

## How the arguments go

- Each argument explains which geometric obstruction or variation motivates an estimate before calculating it.
- Initial angle: the argument integrates fixed wall pieces and completes two squares.
  - Weighted Cauchy–Schwarz pays for the tent apex, so no feasible critical point or moving-intersection
    concavity proof is needed.
  - Its width split and residual tent gap come from the diagonal offset and angular endpoint. The later corner
    width solves the separation equality at that endpoint.
- Wide caps: the exclusion uses the diagonal endpoint budget to price the exact span of both nearby-angle peaks.
  - Its three separate width and height cuts and the full-cap endpoint niche box are removed; two square
    inequalities give the final supporting plane.
- Intermediate tilt: the bound uses one common price for the clipped exterior losses and the diagonal niche.
  - Their support coordinates cancel, leaving one quadratic to complete.
  - Comparing directly with the reference area gives `h < 1/3` throughout the later estimates.
- Reference and triangles: the reference phases are matched by an angle identity, and the triangle comparisons
  use stationarity and concavity.
  - Their floor corrections share one tilt payment and one Newton comparison of the whole area bound.
- Horizontal caps: the argument compares the end of curvature excess with endpoint contact.
  - Its dry endpoints reduce the width test to a chord-area bound and the energy threshold `√17/6`.
  - Corner confinement uses circle inequalities and two quadratics.
- Tilted selector: it splits at the height where its two energy tests meet, with the corresponding radius fixing
  its width.
  - A triangle payment excludes every larger width at all heights; below it the dry endpoint leaves a defining
    equality and one elementary floor-energy endpoint check.
  - For small heights, the same width reduction turns a radius failure into a joint pressure budget, paid by the
    ordinary-area gain between the two circle radii.
- Tilted and reflected excess: it is compared with zero tilt; the loss of floor energy pays for the delay of the
  first crossing.
  - One joint crossing-and-decay lemma covers all reflected heights.
- Proper terminal angles: the argument prices both middle orientations with one angular budget and the atom with
  its inset squared.
  - Its cubic overlap pays the terminal margin throughout the slope range.
  - For the terminal circle, a tangent pays for shifting the chord center, reducing the whole cosine range to two
    width endpoints. Their actual minimum gap pays for the cubic overlap, with no separate reserve.
- Calibration: its width condition follows from boundary flux, and the small-tilt losses are compared at one
  endpoint.
- Newton formulas generate the auxiliary root bounds.
- The remaining interval and stopping-time checks use exact wide-triangle demand and a tilt-canceling price; they
  are stated in the appendices and inventoried in the review.

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
