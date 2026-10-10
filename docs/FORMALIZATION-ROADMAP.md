# Roadmap from the written proof to Lean

## Status and target

This roadmap tracks the formalization from its initial foundations through
the actual cap, motion, integral, and reference-geometry layers. Written Gate
0–3 completion does not constitute completion of any Lean gate. The pull
request contains complete source proof bodies for every declared theorem,
**uncompiled** at the user's request. Source review is recorded separately
from kernel checks.

The source proof is pinned to research commit
[`20489723dc8777a82ee70ae60510115dc6f21085`][research]. Its controlling
[execution plan][plan] and [assembled manuscript][manuscript] supply the
mathematical target and identify the retained external inputs.

The eventual theorem must quantify over every compact connected body with
two genuine corridor passages from a common incoming orientation, prove the
sharp area bound `M`, construct an attaining reference body, and prove exact
compact-set uniqueness up to congruence. Backtracking, independent terminal
angles, subunit incoming height, asymmetry, facets, and degenerate auxiliary
fibers must be handled explicitly. Motion witnesses need not be unique.

The new project has no theorem claiming that target and no axiom or certificate
field assuming it. Each theorem below will enter the source tree only with a
complete proof body.

## Ordered work packages

| Stage | Written-proof dependency | Deliverable and acceptance criterion | Current Lean status |
| --- | --- | --- | --- |
| F0: foundations | MS.1–2, ED.1–6, TB4 | Exact constant; original coordinate domain; signed fiber algebra; finite-measure regular-closed recovery | Complete source bodies in this PR; uncompiled |
| F1: actual hull and cap analysis | Gate 0, MS.4–7 | Hull compactness, cap roofs and support, measurability, true barriers, signed envelope and area integrals | Complete source bodies for this geometric and integral layer; uncompiled |
| F2: original-motion bridge | Gate 0 / original-motion audit | Lift proper rigid paths, recover both actual terminal strips, justify canonical angular intervals and common-hull containment | Support tightening, real endpoint walls, reflected paths, IVT reach, and normalized terminal-passage area assembly implemented; full reduction remains |
| F3: reference geometry | Gate 1 calibration, MS.11–13 | Construct the reference support, hull, physical body and both motions; prove its area equals `M` | Exact parameters, piecewise C¹ coordinates, phase curvature, and explicit compact symmetric hull implemented; support realization and attainment remain |
| F4: full-turn cap theorem | Written Gate 1 | Universal score at most `M/2` on the full cap domain; exact reference attainment | Actual score and elementary small-width branch implemented; universal variational theorem remains |
| F5: partial-turn cap theorem | Written Gate 2 | Independent terminal-angle bound retaining the whole outgoing wall, including the full-turn endpoint | Actual partial barriers and two-cap assembly implemented; universal sharp partial-cap estimate remains |
| F6: equality and original body | Written Gate 3 | Equality classification, inverse canonicalization, proper-angle strictness, actual hull and literal set recovery | Actual four-term geometric deficit, exact a.e. partition equality, literal two-cap hull recovery, and generic physical-set recovery implemented; sharp equality classification remains |
| F7: final verification | All stages | Unconditional original-domain optimality and uniqueness with audited standard axioms | Deferred; no compilation or CI in this PR |

### F0 — exact constants and reusable elementary lemmas

`ExactConstant.lean` obtains existence by the intermediate value theorem and
uniqueness by strict monotonicity on the entire real line. Its rational signs
are exact: the cubic is `-17/343` at `2/7` and `1/125` at `3/10`.
Classical choice selects the proved root. The module does not use a decimal
approximation or assume an algebraic-number oracle.

`Algebra/Deficit.lean` proves the four-wall fiber is the interval with lower
endpoint `max dV nU` and upper endpoint `1 - max dU nV`. Nonemptiness is
equivalent to a nonnegative **signed** length. Negative auxiliary lengths
are retained in the comparison identities. The middle and exterior positive
parts give exact defects and exact pointwise equality conditions.

The original four-term theorem in `Algebra/Deficit.lean` is arithmetic.
The subsequent `Measure/Partition.lean` and `Measure/CapAssembly.lean`
instantiate it with genuine integrals, the actual body, and the ordinary
measure of the missing envelope. Scalar sharpness is still not a conclusion
of any of these identities.

`Topology/RegularClosed.lean` proves the finite-measure set-recovery step in
a general space. An open null difference is empty, then closedness recovers
the closure of the larger set's interior. Equal infinite measures would not
suffice, so finite measure is explicit or supplied by compactness.

### F1 — hulls, roofs, support and integration

`HullCompact.lean` proves compactness of `actualHull S` itself. Carathéodory's
theorem expresses the hull as a finite union of continuous images of compact
simplices and compact point tuples; zero through three vertices cover the
two-dimensional case. No closure is silently substituted for the hull.

`CapGeometry.lean` proves that downward filling preserves compactness and
convexity, that roofs are attained and concave on the projection, and that the
zero-extended roof is upper semicontinuous and measurable. `Support.lean`
proves compact support attainment and continuity, actual-hull support
invariance, support determination by separation, and the required rotation,
reflection, translation, and downward-filling identities.

`Reflection.lean` proves that the original connected compact body's projection
is unchanged by convexification. Both actual hull caps have precisely that
projection, and their reflected intersection is literally the actual hull.
All boundary points are retained.

`Barriers.lean` defines every interior-angle corner constraint and the entire
proper-terminal first wall. At `π/2`, the latter becomes the top-support
excess and is proved redundant for a cap in the unit strip. `BarrierAnalysis.lean`
proves the swept supremum bounded above for every horizontal coordinate:
at least one of sine and cosine is at least `1/2`, so one wall bounds their
minimum. This yields lower semicontinuity, measurability, and actual
integrability on compact intervals, including intervals outside the cap
projection. Roof integrability is also proved.

`Measure/Fibers.lean` proves Tonelli/Cavalieri formulas. Ordinary envelope
area uses the positive part of signed fiber length until physical nonemptiness
is supplied. `Measure/Partition.lean` proves equal measures of the middle and
exterior regions, the integrated partition identity, and exact a.e. equality
conditions. `Measure/CapAssembly.lean` supplies physical fibers from the
original connected projection and instantiates the complete actual-body
area and deficit identities. No positive-width assumption is needed.

### F2 — preserve the original motion domain

The current `RigidMotionPath` uses continuous real angle lifts and continuous
translations on `[0,1]`. `SameInitialOrientation` is equality of rotation
maps, allowing different angle representatives. Prove the correspondence
with continuous paths of proper Euclidean isometries, including existence of
angle lifts and invariance of area under rigid placements. The coordinate
plane uses the product topology; its product norm must not be mistaken for
the Euclidean norm when applying isometry APIs.

Completed source results in `Hallway.lean` tighten the supports while
preserving the actual retained body and separately recover the real outgoing
strip. `AngularDomain.lean` proves the intermediate-angle result by the IVT,
with no monotonicity premise, both for a genuine terminal angle and for a
visited full quarter turn. It also constructs the explicit reflected upper
motion and proves its lower-passage property. `CapAssembly.lean` derives the
actual area inequality from independent normalized terminal passages with
angles in `(0,π/2]`, discharging cap regularity and integration conditions.

The remaining Gate 0 work is the global wrong-way exclusion and angular-reach
dichotomy, common incoming normalization, area invariance under the coordinate
rigid maps, the correspondence with arbitrary proper-isometry paths, and the
compact parameter-domain/gap-compression reductions used later. These are
substantive obligations. The normalized terminal theorem does not imply them,
and its angle premises have not been added to `IsAmbidextrous`.

**Lean Gate 0 acceptance:** an end-to-end theorem from the stated two original
motions to the correct signed joint inequality problem, with both actual
terminal strips retained and physical area justified.

### F3–F4 — reference body and the universal full-turn bound

`Reference/Parameters.lean` proves the exact trigonometric matching equations
from the cubic, including the sign choice needed in the doubled-angle
factorization. `Reference/Support.lean` gives all six phase formulas, first
and second derivatives, matching values and derivatives at both switches,
reflection identities, endpoint conditions, and the strict middle curvature
margin. A one-sided derivative gluing proof establishes actual global C¹
regularity of the displayed coordinates.

`Reference/Hull.lean` defines the four-family half-plane intersection, proves
that the explicit center `(k,1/2)` lies in it, obtains a compact bounding box
from endpoint normals, and proves compactness, convexity, connectedness, and
literal reflection symmetry. The actual hull support is bounded above by the
prescribed functions. **Reverse support inequalities are not yet proved.**
The next reference work is support realization, the physical niche-cut sofa,
its two feasible motions, and exact area `M`.

`Measure/CapScore.lean` defines the actual integral score and proves the
elementary bound `Pα(U) ≤ width(U)/2` for every cap and every `α`. It therefore
closes the scalar small-width branch `width(U) ≤ M`, with strict inequality
when the width is smaller. This is one branch of the scalar problem, not the
universal sharp cap theorem.

For arbitrary caps, formalize the chord and height reductions, compactness
of the cap optimization problem, source-measure extraction and approximation,
and the variational/contact equations. The extraction must apply to an
arbitrary prescribed maximizing cap; existence of one regular optimizer
does not classify every optimizer.

Prove the real periodic support extension, its endpoint matching and `H¹`
calibration on the actual analytic domain. Discharge every width and tilt
exclusion with exact inequalities and cover nonsmooth and degenerate limits.

The written proof invokes the ordinary one-turn area theorem and a rational
Gerver-area enclosure in strict exclusion branches. These are **formal
dependencies still to discharge**. Either import an appropriate completed
theorem from an audited, compatible formalization or prove the needed result
here. Inspect its transitive axioms before accepting the dependency. Importing
the old repository wholesale, assuming its result, or assuming an external
equality theorem does not close this obligation.

**Lean Gate 1 acceptance:** the universal full-turn scalar bound and exact
reference attainment, plus the corresponding original two-full-turn body
bound, on the full stated domain without extra regularity assumptions.

### F5 — independent proper terminal angles

Formalize the actual partial barrier, retaining its entire terminal first
wall and its positive part. Develop terminal-facet approximation, reflected
source-measure impulse, weighted companion/calibration estimates, and the
boundary variation used by the written Gate 2 proof.

The terminal-angle ranges must overlap or meet with all endpoints checked.
Exact rational inequalities can be proved with kernel-producing arithmetic
tactics; numerical samples cannot establish continuum coverage. Treat
`α = π/2` using the full-turn theorem and keep `α` and `γ` independent in the
two-cap assembly.

**Lean Gate 2 acceptance:** a universal partial-cap bound, the signed joint
bound, and the area bound for every original compact connected ambidextrous
body. This stage proves optimality once F3 supplies attainment; uniqueness
still requires F6.

### F6 — equality, inverse reductions and exact set recovery

The actual four-term deficit is now instantiated in
`actual_cap_four_term_deficit`. The partition term is nonnegative and the
filling term is actual missing area. The two scalar terms require the still
open sharp cap estimates before their nonnegativity can be concluded. Once
those are proved, equality will identify both **original** cap scores and
force both remainders to vanish.

Classify every full-turn equality cap, including the translation mode, and
reverse the chord cut and vertical extrusion exactly. The current extrusion
identity is only pointwise algebra; integrability, reference niche continuity,
and strict positivity near the middle endpoints remain to be proved. Establish
strict inequality at every proper terminal angle before recovering the two
actual equality caps and their common hull.

Construct and prove regular closedness of the genuine reference body. Apply
the generic recovery theorem only after proving containment, equal finite
area, and the required regularity. State exact equality of compact sets up
to congruence, rather than only almost-everywhere equality or equality of
auxiliary caps. Prove the reference satisfies the original motion predicate
to obtain the converse equality direction.

**Lean Gate 3 acceptance:** the unconditional optimality-and-uniqueness
theorem in the original two-motion domain, actual-hull identification and
necessary full angular reach, with every retained mathematical input proved.

## Next implementation sequence

1. Complete the original-motion normalization and reach dichotomy, including
   rigorous area estimates for excluded angular excursions. Join the existing
   terminal and visited-full-turn branches, allowing different branches for
   the two independent motions.
2. Prove support realization for the explicit reference hull, construct the
   physical reference sofa and its two motions, and evaluate its exact area.
3. Develop compactness, chord/height reductions, prescribed-optimizer
   regularity, and the variational/calibration machinery for the universal
   full-turn scalar theorem. Discharge the retained ordinary one-turn input.
4. Formalize the proper-terminal variational estimate with its whole wall,
   then classify equality, reverse reductions, and apply exact set recovery.
5. When separately requested, elaborate the entire pinned project and run
   the prepared transitive axiom queries. Repair every compilation issue
   while preserving the source policy. No such verification is performed
   by this uncompiled draft.

## Source discipline and later verification

The only permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No new axiom, admission, native evaluation shortcut, or
trust-bypassing declaration is acceptable. Natural local hypotheses in
reusable lemmas are explicit; an assumption equivalent to the desired global
theorem is not a completed formalization.

This pull request adds no CI and performs no Lean execution. After compilation
is separately requested, check the pinned project, repair elaboration failures
without introducing gaps, run the prepared axiom queries, and inspect the
transitive dependency sets. An uncompiled source review is never recorded as
a kernel pass. The manually assembled lockfile also requires validation in
that future pass.

[research]: https://github.com/vltanh/lean4-moving-sofa/commit/20489723dc8777a82ee70ae60510115dc6f21085
[plan]: https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/SHARP-OPTIMALITY-EXECUTION-PLAN.md
[manuscript]: https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/GATE3-MANUSCRIPT.md
