# Roadmap from the written proof to Lean

## Status and target

This roadmap starts a new formalization project. Written Gate 0–3 completion
does not constitute completion of any Lean gate. The initial pull request
contains complete source proof bodies for a limited foundation, **uncompiled**
at the user's request. Source review is recorded separately from kernel checks.

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
| F1: actual hull and cap analysis | Gate 0, MS.4–7 | Hull compactness, cap roofs and support, measurability, true barriers, signed envelope and area integrals | Not yet formalized |
| F2: original-motion bridge | Gate 0 / original-motion audit | Lift proper rigid paths, recover both actual terminal strips, justify canonical angular intervals and common-hull containment | Definitions only in this PR |
| F3: reference geometry | Gate 1 calibration, MS.11–13 | Construct the reference support, hull, physical body and both motions; prove its area equals `M` | Exact scalar parameter only in this PR |
| F4: full-turn cap theorem | Written Gate 1 | Universal score at most `M/2` on the full cap domain; exact reference attainment | Not yet formalized |
| F5: partial-turn cap theorem | Written Gate 2 | Independent terminal-angle bound retaining the whole outgoing wall, including the full-turn endpoint | Not yet formalized |
| F6: equality and original body | Written Gate 3 | Equality classification, inverse canonicalization, proper-angle strictness, actual hull and literal set recovery | Pointwise deficit algebra and generic recovery lemma only |
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

The four-term deficit theorem is explicitly arithmetic. Its parameters named
`area`, `envelope`, and `scoreU` are arbitrary real numbers; their geometric
interpretation and bounds are hypotheses, not established geometric results.
Its usefulness is to isolate the final algebra after those facts are proved.

`Topology/RegularClosed.lean` proves the finite-measure set-recovery step in
a general space. An open null difference is empty, then closedness recovers
the closure of the larger set's interior. Equal infinite measures would not
suffice, so finite measure is explicit or supplied by compactness.

### F1 — hulls, roofs, support and integration

Start with `actualHull S`, not an unrelated maximizer. Prove compactness and
preservation of the horizontal projection for a connected compact physical
body. Establish that upper and reflected-lower hull caps satisfy
`IsDownwardCap`, with no positive-width or full-height premise added silently.

Define roof values, projection endpoints, width and the middle-half interval.
Separate zero-width cases before division by width or use of nondegenerate
integral formulas. Prove measurability and integrability of roofs and barriers.
Define full-turn positive niches and the proper-terminal barrier with the
actual outgoing first wall. Handle the endpoint `π/2` separately wherever
the cosine denominator vanishes.

Construct the envelope from the four walls. Establish Fubini/Cavalieri area
formulas and the equal lengths of the middle and exterior regions. The
pointwise identities already in F0 then yield the integral partition deficit.
For auxiliary hulls with empty fibers, ordinary area uses the positive part
of the signed length. The original-body bridge must justify nonempty fibers
before identifying signed integral and physical envelope area.

### F2 — preserve the original motion domain

The current `RigidMotionPath` uses continuous real angle lifts and continuous
translations on `[0,1]`. `SameInitialOrientation` is equality of rotation
maps, allowing different angle representatives. Prove the correspondence
with continuous paths of proper Euclidean isometries, including existence of
angle lifts and invariance of area under rigid placements. The coordinate
plane uses the product topology; its product norm must not be mistaken for
the Euclidean norm when applying isometry APIs.

Formalize the Gate 0 wrong-way angular reach, both independent terminal
strips, common incoming normalization, and actual-hull tightening. Preserve
whole-body endpoint conditions. Carry connectedness to nonempty envelope
fibers, and prove the compact parameter-domain and gap-compression reductions
used later. Do not infer a full quarter-turn passage from a proper terminal
angle.

**Lean Gate 0 acceptance:** an end-to-end theorem from the stated two original
motions to the correct signed joint inequality problem, with both actual
terminal strips retained and physical area justified.

### F3–F4 — reference body and the universal full-turn bound

Construct the piecewise reference support from `Y` and `beta`. Prove exact
matching values and first derivatives, nonnegative curvature measure, the
actual convex support body, the compact physical sofa, and its two feasible
motions. Prove exact area `M` and the geometric facts later needed for equality.

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

Instantiate the four-term deficit with actual cap scores, the integrated
partition remainder, and the measure omitted from the actual envelope. Show
all four terms are nonnegative. Equality then identifies both **original**
cap scores and forces both remainders to vanish.

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
