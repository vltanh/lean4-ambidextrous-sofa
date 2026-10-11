# Manuscript review and checks

Date: 11 October 2026, US Central Time.

The manuscript presents a mathematical proof of optimality, uniqueness, and the quarter-turn conclusion. Its eleven main sections follow the proof stages explained in the introduction. Eight mathematical appendices supply the ordinary-sofa input, the reference construction, and the auxiliary estimates.

## Mathematical review

Three writers reviewed sections written by the others. The review checked the following points:

- The reduction retains the actual two motions and permits pauses, reversals, different initial translations, and proper terminal angles. The terminal first wall is included over the whole projection.
- Connectedness makes the signed envelope fibers nonnegative. The reduction records the nonnegative deficits needed to identify both original caps in the equality case.
- Penalized polygon selection approximates each prescribed maximum. The two weighted source measures give the variation laws without assuming convergence of unweighted niche boundary length.
- The full-turn argument includes the ordered contacts, joint occupation, two-unit strip moments, and folded-wing energy estimate. The geometric exclusions precede the support-functional comparison.
- The calibration applies to the stated class of continuously differentiable support profiles, proves the coercivity constant, and identifies the unique root of the stationary cubic.
- The proper-angle argument applies to each prescribed maximizing pair, with its actual terminal facet and reflected impulse. The circle and curvature estimates exclude that pair's proper angle.
- The preliminary width and tilt exclusions use the actual barrier. Exact rational calculations check the seven leakage intervals and the scalar certificates.
- The reference support curve, face atoms, phase matching, niche constraints, two passages, and exact area are proved explicitly. Differentiation checks all three area primitives and the endpoint fluxes.
- Equal cap scores align the original caps through their common projection. Containment and regular closedness recover equality of compact sets and the conclusion for every witnessing pair of motions.

The review found no unresolved substantive mathematical error. It clarified the competitive range for a concavity argument and the reference hull's nonempty interior. This is an agent review; human mathematical review remains outstanding.

## Build and layout checks

- `make check` passes: no undefined references, duplicate labels, overflowing lines, or BibTeX warnings.
- The manuscript has 107 pages. All 317 labels and 318 cross-reference uses resolve in the active source files.
- `make arxiv` produces a 31-entry source archive and compiles its 107-page PDF separately with `pdflatex` alone. The archive contains only the active manuscript inputs, bibliography, and figure PDFs.
- Representative pages were inspected visually: the title and main theorem, introduction and organization, support-functional section, reference appendix, contact-energy calculation, and exact rational table.
- The six figure assets retain their numerical geometry checks from the preceding build.
- Whitespace and source scans pass. The archived research manuscript is unchanged.

## References

The bibliography uses mathematical sources. The preceding citation check consulted the primary sources for [Romik's construction](https://arxiv.org/abs/1606.08111), [Baek's theorem](https://arxiv.org/abs/2411.19826), [Kallus and Romik's bounds](https://arxiv.org/abs/1706.06630), [Georgiev, Gómez-Serrano, Tao and Wagner](https://arxiv.org/abs/2511.02864), and [O'Keefe's work](https://github.com/devinokeefe/ambidextrous-sofa-bounds). This was a targeted citation check rather than an exhaustive literature survey.
