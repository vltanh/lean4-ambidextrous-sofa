# Initial source-review record

**Review date:** October 10, 2026.

**Verification mode:** source inspection only; no Lean execution or CI.

This record concerns the initial foundation draft. It is not a Lean build
log, a kernel axiom report, or an independent referee's acceptance of the
underlying research manuscript.

## Scope

The six implementation modules contain **67 named theorems**, each with a
complete source proof body. They contain **96 explicitly named declarations**
in total, including definitions, structures and the plane abbreviation.
`AxiomAudit.lean` prepares one unexecuted axiom query for each declaration.
The library entry point imports all six modules and does not import the audit.

| Module | Named theorems | Source-review emphasis |
| --- | ---: | --- |
| `ExactConstant.lean` | 22 | IVT endpoints, global strict monotonicity, uniqueness direction, root selection, exact rational and trigonometric bounds |
| `Geometry/Plane.lean` | 9 | Correct reflected corridors and explicit Euclidean squared length, without confusing the product norm with a Euclidean norm |
| `Geometry/Motions.lean` | 2 | Whole-body image conditions, independent paths, common initial rotation maps, and faithful subset inheritance |
| `Geometry/Caps.lean` | 9 | Actual convex hull; no full-height premise; necessary baseline assumptions for projection and downward filling |
| `Algebra/Deficit.lean` | 22 | All-real signed identities, nonempty fibers, exact zero-defect conditions, and explicit arithmetic hypotheses |
| `Topology/RegularClosed.lean` | 3 | Null difference, positivity on open sets, finite measure, and literal set recovery |

Separate collaborating reviewers inspected the proof sources and the relevant
Mathlib declarations. The exact-constant, deficit, topology, and geometry
modules received independent source review in addition to the implementation
review. These are reviews within this session, not external validation.

One likely elaboration issue was repaired in the Euclidean squared-length
proof: a rewrite could already close a definitional equality, leaving a
redundant `rfl`. The final source uses one `simp only` call for that step.
No other concrete source defect was identified during this review. Successful
elaboration remains untested.

## Pinned API checks

All external signatures below were inspected at Mathlib revision
[`c55e6e786f49471c72fbddbec5415808896aec1e`][mathlib] through the GitHub API.

| Official source | Checked declarations |
| --- | --- |
| [Intermediate value theorem][ivt] | `intermediate_value_Icc`, including the image-witness equality direction |
| [Monotone functions][mono] | `StrictMono.lt_iff_lt`, `StrictMono.injective` |
| [Arctangent][atan] | `Real.tan_arctan`, `arctan_lt_pi_div_two`, `arctan_lt_arctan_iff`, `arctan_one`, `arctan_pos` |
| [Trigonometric identities][trig] | `Real.cos_sq_add_sin_sq` |
| [Convex hulls][hull] | `subset_convexHull`, `convex_convexHull`, `convexHull_mono` and their explicit/implicit parameters |
| [Existing product-eta use][eta] | `Prod.mk.eta` occurs in this pinned Mathlib source |
| [Positive measure on open sets][openpos] | `Measure.IsOpenPosMeasure`, `IsOpen.eq_empty_of_measure_zero` |
| [Measure difference][measure] | `measure_sdiff`, with null measurability and a finite smaller measure |
| [Borel space compatibility][borel] | `IsClosed.nullMeasurableSet` under `OpensMeasurableSpace` |
| [Basic topology][topology] and [closure][closure] | `IsOpen.sdiff`, `closure_minimal` |
| [Finite measure on compacts][finite] | `IsFiniteMeasureOnCompacts`, `IsCompact.measure_ne_top` |

Mathlib's `lean-toolchain` at this commit specifies
`leanprover/lean4:v4.35.0-rc3`, matching this project. Its eight transitive
package revisions were read from the [pinned upstream lockfile][lockfile].
The project lockfile was assembled from those entries, marked inherited,
plus the exact Mathlib root dependency. No Lake command generated it.

## Source-policy check

The only verification command for the source policy is:

```sh
python3 scripts/check_source_policy.py
```

It strips comments and strings for lexical checks, rejects admissions,
custom axioms and the prohibited native/metaprogramming constructs, checks
project import closure and cycles, checks coverage of the future axiom
queries, verifies full dependency revisions and `autoImplicit = false`, and
rejects CI configuration. It does not contain a subprocess or call Lean.

The check completed successfully with this output:

```text
Source policy passed: 8 Lean files; 67 named theorems;
96 named declarations covered by unexecuted axiom queries.
Imports and dependency pins checked; no CI configuration found.
No Lean execution occurred. This is not a kernel proof or axiom audit.
```

The source policy checks the eight authored Lean files, including the library
entry point and the unexecuted audit file. Its result is a source-policy
result only. In particular, it cannot prove that tactics elaborate, that
record inference succeeds, or that transitive proof dependencies contain
only the three permitted foundational axioms.

## Deferred verification and mathematics

No Lean, Lake, elan, language server, compilation, native evaluation, or
GitHub Actions workflow was invoked for this draft. No CI workflow is added.
The prepared axiom queries have not been run; their actual output must later
be checked against `propext`, `Classical.choice`, and `Quot.sound`.

The project has no Lean theorem for the global cap bound, reference-body
attainment, original-motion optimality, or uniqueness of the physical sofa.
The generic recovery theorem does not construct the reference body, and the
arithmetic deficit theorem does not establish the geometric score bounds.
The [roadmap](FORMALIZATION-ROADMAP.md) lists the remaining bridges and the
ordinary one-turn dependency. No missing result is installed as an axiom.

[mathlib]: https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e
[ivt]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Order/IntermediateValue.lean
[mono]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Order/Monotone/Basic.lean
[atan]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean
[trig]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Complex/Trigonometric.lean
[hull]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Convex/Hull.lean
[eta]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean
[openpos]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Measure/OpenPos.lean
[measure]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Measure/Basic.lean
[borel]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean
[topology]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Basic.lean
[closure]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Closure.lean
[finite]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean
[lockfile]: https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/lake-manifest.json
