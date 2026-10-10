# Definitions

[Back to the README](../README.md)

Read these before trusting the results: Lean's kernel checks the proofs, not that the statements mean what
you intend. The statements of record, in [`Challenge.lean`](../Challenge.lean), use only Mathlib and the
definitions below, in the namespace `Ambidextrous`. The Challenge may import only Mathlib, so it copies them
verbatim from the marked block of [`AmbidextrousSofa/ChallengeDefs.lean`](../AmbidextrousSofa/ChallengeDefs.lean)
([`scripts/sync_challenge_defs.py`](../scripts/sync_challenge_defs.py), checked in CI).
[`AmbidextrousSofa/Main.lean`](../AmbidextrousSofa/Main.lean) proves that each of them is the definition that the
library uses: all are equal by definition (`rfl`), except that the Challenge takes the root `Y` as a
parameter with its defining property where the library fixes it (`Main.eq_Y`).

Equation labels (MS.1, …) refer to the [manuscript](archive/GATE3-MANUSCRIPT.md); an independent review
compared every definition with its text and found no difference.

## The plane, the two hallways and motions

The plane is `ℝ × ℝ`, and the area of a set is its Lebesgue measure, `volume.real S`, which is finite for
the compact sets of the theorems. `rotate θ` is the counterclockwise rotation by `θ`:

```lean
def rotate (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * p.1 - Real.sin θ * p.2, Real.sin θ * p.1 + Real.cos θ * p.2)

def incomingArm : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}
def lowerOutgoingArm : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}
def upperOutgoingArm : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2}
```

The two hallways share the incoming arm `(-∞, 1] × [0, 1]`. The hallway `incomingArm ∪ lowerOutgoingArm`
turns right (downward), into `[0, 1] × (-∞, 1]`; the hallway `incomingArm ∪ upperOutgoingArm` turns left
(upward), into `[0, 1] × [0, ∞)`. The second is the reflection of the first in the line `y = 1/2`: this is
the manuscript's corridor and "its reflection in `y = 1/2`" (Chapter 1, §1).

A motion places each point `p` of a set `S` at `rotate (θ t) p + c t` at the time `t ∈ [0, 1]`.
`MovesThrough S hallway incoming outgoing θ c` says that the angle `θ` and the translation `c` are continuous,
that `S` starts in `incoming`, stays in `hallway`, and ends in `outgoing`:

```lean
def MovesThrough (S hallway incoming outgoing : Set (ℝ × ℝ)) (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ) :
    Prop :=
  ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
    (∀ p ∈ S, rotate (θ 0) p + c 0 ∈ incoming) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rotate (θ t) p + c t ∈ hallway) ∧
    (∀ p ∈ S, rotate (θ 1) p + c 1 ∈ outgoing)
```

The motion may pause, turn back and turn through any angle: nothing requires it to be monotone or to turn
by exactly a quarter turn. A continuous angle and a continuous translation describe exactly the continuous
paths of proper rigid motions (a continuous path of rotations lifts to a continuous angle); the manuscript's
"continuous path of proper rigid motions".

## Ambidextrous sofas

```lean
def IsAmbidextrous (S : Set (ℝ × ℝ)) : Prop :=
  IsCompact S ∧ IsConnected S ∧
    ∃ (θ₁ θ₂ : ℝ → ℝ) (c₁ c₂ : ℝ → ℝ × ℝ), rotate (θ₁ 0) = rotate (θ₂ 0) ∧
      MovesThrough S (incomingArm ∪ lowerOutgoingArm) incomingArm lowerOutgoingArm θ₁ c₁ ∧
      MovesThrough S (incomingArm ∪ upperOutgoingArm) incomingArm upperOutgoingArm θ₂ c₂
```

An ambidextrous sofa is a compact connected (in particular nonempty) set with two motions, one through each
hallway, that start with the same orientation, `rotate (θ₁ 0) = rotate (θ₂ 0)`. Their translations and the
rest of the two motions are independent. This is the manuscript's domain (Chapter 1, §1: "The two initial
translations may differ, but their incoming body orientation is common.").

The common orientation is what makes the problem ambidextrous. Without it, every ordinary moving sofa
symmetric under a reflection in a vertical line, such as Gerver's sofa (area 2.2195…), would pass the
left-turning hallway after a rotation by `π`, since its rotation by `π` is then its reflection in a
horizontal line. When each of the two motions turns the shape by exactly a quarter turn, as they do for
Romik's sofa, the shape can also travel along a single hallway that turns right and then left: after the
first turn it meets the second corner in the same orientation, relative to the corridor, as it met the first.
The [animation](figures/ambidextrous-moving.gif) shows Romik's sofa doing this.

## Romik's ambidextrous sofa

![Romik's ambidextrous sofa between the lines y = 0 and y = 1: its convex hull, dashed, without the two niches, in orange](figures/romik-sofa.svg)

The sofa is built from the positive root `Y = 0.2980…` of `4Y³ + 3Y = 1` (MS.1). The theorems take any `Y`
with this property, and `existsUnique_root` shows that there is one. With `β = arctan Y`:

```lean
def coeffA (Y : ℝ) : ℝ := 1 / (4 * Real.sin (Real.arctan Y))
def coeffK (Y : ℝ) : ℝ := 1 - 4 / 3 * coeffA Y
def coeffR (Y : ℝ) : ℝ :=
  Real.cos (Real.arctan Y) / Real.cos (3 / 2 * (Real.pi / 4 - Real.arctan Y))
```

These are the manuscript's `A_* = 1/(4 sin β_*)`, `k = 1 − 4A_*/3` and `ℛ = cos β_* / cos T_*` with
`T_* = (3/2)(π/4 − β_*)`.

**The hull.** Its support function `h` is given on the upper half of the circle by `h(t) = f(t)` and
`h(t + π/2) = g(t)` for `t ∈ [0, π/2]`, in three phases `[0, β]`, `[β, π/2 − β]`, `[π/2 − β, π/2]` (MS.11):

```lean
def supportF (Y t : ℝ) : ℝ :=
  if t ≤ Real.arctan Y then Real.cos t + 1 / 2 * Real.sin t
  else if t ≤ Real.pi / 2 - Real.arctan Y then
    coeffR Y * Real.cos (t / 2 + Real.pi / 8) + coeffK Y * Real.cos t + 1 / 2 * Real.sin t
  else (1 - 2 / 3 * coeffA Y) * Real.cos t + 1 / 2 * Real.sin t + 1 / 2

def supportG (Y t : ℝ) : ℝ :=
  if t ≤ Real.arctan Y then (2 * coeffA Y - 1) * Real.sin t + 1 / 2 * Real.cos t + 1 / 2
  else if t ≤ Real.pi / 2 - Real.arctan Y then
    coeffR Y * Real.sin (t / 2 + Real.pi / 8) - coeffK Y * Real.sin t + 1 / 2 * Real.cos t
  else (8 / 3 * coeffA Y - 1) * Real.sin t + 1 / 2 * Real.cos t
```

The phases agree in value and first derivative at `β` and `π/2 − β`, by the cubic equation (MS.12). The hull is
the intersection of the half-planes `p · (cos t, sin t) ≤ f(t)` and `p · (cos (t + π/2), sin (t + π/2)) ≤ g(t)`
for `t ∈ [0, π/2]`, and of their reflections in the line `y = 1/2`, which give the lower half of the circle:

```lean
def halfPlanes (Y t : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 * Real.cos t + p.2 * Real.sin t ≤ supportF Y t ∧
    p.1 * Real.cos (t + Real.pi / 2) + p.2 * Real.sin (t + Real.pi / 2) ≤ supportG Y t}

def referenceHull (Y : ℝ) : Set (ℝ × ℝ) :=
  ⋂ t ∈ Icc (0 : ℝ) (Real.pi / 2), halfPlanes Y t ∩ (fun p => (p.1, 1 - p.2)) ⁻¹' halfPlanes Y t
```

`convexHull_referenceSofa` proves that this is the convex hull of the sofa (MS.14). Its projection is
`[1 − 8A/3, 1]`, of width `8A/3 = 2.3340…` (Romik's (6)), and its top and bottom faces are the middle half
`J = [1 − 2A, 1 − 2A/3]` of the projection, at the heights `1` and `0`.

**The niche.** `support K v` is the support function `sup {p · v | p ∈ K}`. When the hallway that turns right
is turned by `θ ∈ (0, π/2)` about the hull, with its two outer walls supporting the hull, its inner walls are
the lines `p · (cos θ, sin θ) = h(θ) − 1` and `p · (−sin θ, cos θ) = h(θ + π/2) − 1`, and the points above the
abscissa `x` below both lines lie in its inner corner. The niche `n(x)` is the supremum of that height over
the turn, or `0`:

```lean
def support (K : Set (ℝ × ℝ)) (v : ℝ × ℝ) : ℝ := sSup ((fun p => p.1 * v.1 + p.2 * v.2) '' K)

def niche (K : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  max (sSup ((fun θ => min
    ((support K (Real.cos θ, Real.sin θ) - 1 - x * Real.cos θ) / Real.sin θ)
    ((support K (-Real.sin θ, Real.cos θ) - 1 + x * Real.sin θ) / Real.cos θ)) ''
      Ioo 0 (Real.pi / 2))) 0
```

![The sofa in its own frame inside the hallway that turns right, turned by π/4 about it](figures/supporting-hallway.svg)

The inner corner traces the orange path during the turn; the niche is the region below it and above
`y = 0`. For Romik's hull the niche lives over `J` and stays below `1/2` (Technical proof 2).

**The sofa.** It is the hull without the two open niches, the one swept by the inner corner of the hallway
that turns right, from below, and its mirror image, swept by the inner corner of the hallway that turns
left, from above:

```lean
def referenceSofa (Y : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ referenceHull Y ∧ niche (referenceHull Y) p.1 ≤ p.2 ∧
    niche (referenceHull Y) p.1 ≤ 1 - p.2}
```

This is the manuscript's `Σ_*` ("removing the two open canonical swept niches from `K_*`", Chapter 1, §3),
and it is Romik's shape `Σ = S_x ∩ ρ(S_x)` of his Theorem 5, in his coordinates (`A(0) = (1, 1/2)`): the
review reproduced the values of his Table 2 from these definitions. Computed from the definitions,
its area is `1.64498`, against `M = 1.6449552…` ([`scripts/figures/romik.py`](../scripts/figures/romik.py)).
The manuscript centers its body horizontally in Chapters 3 to 5; the two differ by a translation, which none
of the theorems sees.
