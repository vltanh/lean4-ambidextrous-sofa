# Uncompiled draft: source-review record

**Review date:** October 10, 2026.

**Verification mode:** source inspection and source-policy checks only.
No Lean execution or CI.

This record covers the foundations and the subsequent actual-cap, motion,
integral, and reference-geometry extension. It is not a Lean build log, a
kernel axiom report, or an external referee's acceptance of the underlying
research manuscript.

## Reviewed source scope

The **21 implementation modules** contain **441 named theorems**, each with
a complete source proof body, and **536 explicitly named declarations** in
total. The preceding foundations draft contained 67 theorems in six modules;
this extension adds 374 theorems in 15 modules. The library entry point imports
all implementation modules and does not import the audit.

`AxiomAudit.lean` contains one prepared, **unexecuted** `#print axioms` query
for every explicitly named declaration. The inventory respects the distinct
`AmbidextrousSofa` and `AmbidextrousSofa.Reference` namespaces. Automatically
generated recursors, projections, and equation lemmas are not additional
explicit source declarations; their transitive use is part of the later
kernel audit.

| Implementation module | Theorems | Named declarations | Review emphasis |
| --- | ---: | ---: | --- |
| `Algebra/Deficit.lean` | 22 | 26 | Signed fibers, positive-part defects, exact zero conditions, arithmetic deficit and extrusion identities |
| `ExactConstant.lean` | 22 | 26 | IVT endpoints, strict monotonicity, classical selection from proved existence, exact rational bounds |
| `Geometry/AngularDomain.lean` | 9 | 11 | IVT despite backtracking, visited versus terminal angles, reflected rigid-path conjugation |
| `Geometry/BarrierAnalysis.lean` | 23 | 23 | A proved finite supremum at every abscissa, semicontinuity, measurability, bounded integrability |
| `Geometry/Barriers.lean` | 15 | 21 | Minimum of both inner rays, all interior angles, complete terminal first wall |
| `Geometry/CapGeometry.lean` | 34 | 38 | Compact downward filling, attained concave roofs, exact fibers, upper semicontinuity |
| `Geometry/Caps.lean` | 9 | 13 | Actual convex hull, broad intrinsic cap domain, no full-height premise |
| `Geometry/Hallway.lean` | 15 | 19 | Retained-body support tightening, actual outgoing strip, continuous canonical placement |
| `Geometry/HullCompact.lean` | 8 | 9 | Finite simplex parametrization of the actual planar hull, including the empty case |
| `Geometry/Motions.lean` | 2 | 8 | Whole-body passage conditions, independent paths, same initial rotation maps |
| `Geometry/Plane.lean` | 9 | 20 | Correct reflected corridors; Euclidean squared length distinct from the product norm |
| `Geometry/Reflection.lean` | 37 | 40 | Reflected support correction, reversed fibers, original connected projection, literal hull recovery |
| `Geometry/Support.lean` | 40 | 45 | Compact attainment and continuity, separation, actual-hull and transformation identities |
| `Measure/CapAssembly.lean` | 9 | 13 | Actual cap endpoints, physical fibers, ordinary area, exact geometric deficit, independent passages |
| `Measure/CapScore.lean` | 14 | 17 | Actual integral score, elementary width branch, full-turn identity, zero-width null sets |
| `Measure/Fibers.lean` | 31 | 34 | Tonelli, positive-part area, justified signed formulas, finite ordinary missing area |
| `Measure/Partition.lean` | 23 | 26 | Equal-measure split, integral identities, a.e. equality conditions, geometric four-term deficit |
| `Reference/Hull.lean` | 31 | 36 | Explicit center witness, endpoint rectangle, compact convex symmetric intersection |
| `Reference/Parameters.lean` | 27 | 34 | Cubic factorization, exact trigonometric matching, positivity selecting the correct branch |
| `Reference/Support.lean` | 58 | 74 | Phase derivatives, switch matching, global C¹ gluing, curvature and center inequalities |
| `Topology/RegularClosed.lean` | 3 | 3 | Finite measure, null open difference, literal closed-set recovery |
| **Total** | **441** | **536** | **Source reviewed; uncompiled** |

## Independent source reviews

Separate collaborating reviewers inspected the mathematical statements,
proof bodies, interfaces, and relevant Mathlib declarations. The cap/support
and reference components were reviewed across their implementation authors.
The hallway and barrier definitions received both geometric and analytical
reviews. `CapAssembly.lean` received separate geometric and measure/API reviews.
These are reviews within this session, not external validation.

The reviews specifically checked several points that can invalidate an
apparently plausible moving-sofa reduction:

- Tightening preserves the original retained points. It does not establish
  that the entire convex hull fits the nonconvex hallway.
- A proper terminal angle retains its outgoing whole-body first wall. At a
  full quarter turn, redundancy follows from the actual top-support bound.
- The angular sweep includes every interior angle. The IVT supplies those
  angles even when the original path backtracks.
- Reflection of a rigid path uses angle `-a` and shift
  `(bx - sin a, 1 - cos a - by)`, so both body and placements are conjugated
  by the actual strip-center reflection.
- Both cap windows are the original connected projection interval. Original
  points certify nonnegative signed fibers before signed integrals are
  identified with ordinary envelope area.
- The reference hull is a real half-plane intersection with an explicit
  witness. Its support upper bounds are not confused with support attainment.
- The exact four-term identity does not establish nonnegativity of the two
  scalar score deficits; that requires the remaining sharp cap theorem.

The planar hull proof was refined to make the two finite-sum reindexings
explicit. The initial squared-length proof also had a redundant tactic
removed during its original review. The audit-generator review also added
explicit rejection of unsupported declaration prefixes, preventing future
inventory omissions. No additional concrete Lean proof correction was
requested by the final independent reviews. Successful elaboration remains
untested.

## Pinned primary-source API checks

Relevant external declarations were inspected through the GitHub API at
Mathlib revision [`c55e6e786f49471c72fbddbec5415808896aec1e`][mathlib].

| Source | Checked use |
| --- | --- |
| [Intermediate value theorem][ivt] | `intermediate_value_Icc`, image-witness equality orientation, restriction to a visited time |
| [Monotone functions][mono], [arctangent][atan], [trigonometric identities][trig] | Strict monotonicity/injectivity, exact switching-angle bounds and identities |
| [Carathéodory][caratheodory], [standard simplex][simplex], [finite affine dimension][affine] | Positive finite convex combinations, simplex compactness, affine-independent cardinality bound |
| [Convex hulls][hull], [convex combinations][combination] | Hull minimality, finite convex combinations, actual-set containment |
| [Finite-dimensional linear algebra][dimension] | Planar dimension and finite product rank |
| [Geometric Hahn–Banach separation][separation] | Strict point-versus-closed-convex-set separation for support determination |
| [Compactness][compact] | Compact subtypes, finite unions, compact ranges, actual supremum/infimum attainment |
| [One-dimensional derivatives][deriv], [order-closed topology][orderclosed], [continuous derivatives][contdiff] | One-sided derivative congruence and union, `Continuous.if_le`, `contDiff_one_iff_deriv` |
| [Positive measure on open sets][openpos], [measure difference][measure], [finite measure on compacts][finite] | Finite equal-area recovery and ordinary missing-envelope area |

The measure implementations additionally use the pinned product
measure/Tonelli APIs, real interval volume, `Integrable.mono'`, integral
subtraction and set difference, conversion between nonnegative real integrals
and `ENNReal` lintegrals, and semicontinuity/Borel measurability. Their
significant signatures and hypothesis orders were inspected by the
implementing and reviewing agents. No current-branch declaration was
substituted for a pinned declaration merely because a search result used a
newer revision.

Mathlib's `lean-toolchain` specifies `leanprover/lean4:v4.35.0-rc3`, matching
this project. Its eight transitive package revisions were read from the
[pinned upstream lockfile][lockfile]. The project lockfile was assembled from
those entries plus the exact Mathlib dependency. No Lake command generated
the lockfile and no dependencies were installed.

## Source-policy verification

The source-only policy command is:

```sh
python3 scripts/check_source_policy.py
```

It strips comments and strings, rejects admissions, custom axioms and the
prohibited native/metaprogramming constructs, checks imports and cycles,
checks entry-point coverage, inventories namespace-qualified declarations,
verifies future axiom-query coverage, checks full dependency revisions and
`autoImplicit = false`, and rejects CI configuration.

The inventory can be emitted as JSON with `--inventory-json`. The
`--write-axiom-audit` option regenerates prepared query text from a valid
source inventory; it does not run those queries. The checker is a conservative
lexical guard, not a Lean parser. It does not contain a subprocess or invoke
Lean.

The final source inventory passed with:

- 23 authored Lean files, including the library entry point and audit.
- 21 implementation modules.
- 441 named theorems and 536 named declarations.
- Exactly 536 prepared, unexecuted axiom queries.
- No source-policy errors, missing imports, import cycles, dependency-pin
  mismatches, or CI configuration.

Git whitespace and local documentation-target checks also passed. Publication
uses the GitHub Git Data API; the published tree and blob hashes are compared
with the reviewed local files.

## Unexecuted verification and remaining mathematics

No Lean, Lake, elan, language server, compilation, native evaluation, axiom
query, or GitHub Actions workflow was invoked. No CI workflow is added.
The intended axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
The actual transitive dependency sets must still be obtained and checked
during a later separately requested Lean verification pass.

The project does not yet contain the universal sharp full-turn or partial-turn
cap theorem, the global original-motion reach reduction, reference physical
body feasibility and exact attainment, or optimality and uniqueness for
`IsAmbidextrous`. The completed actual-body deficit identity and generic
regular-closed recovery lemma do not discharge those obligations. The
[roadmap](FORMALIZATION-ROADMAP.md) identifies their order and the retained
ordinary one-turn dependency. No missing global result is installed as an
axiom, placeholder theorem, or target-shaped certificate.

[mathlib]: https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e
[ivt]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Order/IntermediateValue.lean
[mono]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Order/Monotone/Basic.lean
[atan]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean
[trig]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Complex/Trigonometric.lean
[caratheodory]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Convex/Caratheodory.lean
[simplex]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Convex/StdSimplex.lean
[affine]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean
[hull]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Convex/Hull.lean
[combination]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Convex/Combination.lean
[dimension]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/LinearAlgebra/Dimension/Constructions.lean
[separation]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/LocallyConvex/Separation.lean
[compact]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Compactness/Compact.lean
[deriv]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Calculus/Deriv/Basic.lean
[orderclosed]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Order/OrderClosed.lean
[contdiff]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean
[openpos]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Measure/OpenPos.lean
[measure]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Measure/Basic.lean
[finite]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean
[lockfile]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/lake-manifest.json
