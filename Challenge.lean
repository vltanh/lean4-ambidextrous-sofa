module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Analysis.Convex.Hull

/-!
# The ambidextrous moving sofa: the largest area and the unique optimal shape

The statements of record (`comparator.json`, with the solution `Solution.lean`), in Mathlib's
vocabulary only. An *ambidextrous sofa* is a compact connected planar shape that, from one and the
same starting position in the incoming arm, can be moved around the right-angled corner of a hallway
of unit width that turns to the right, and also around the corner of the reflected hallway, which
turns to the left. Dan Romik (*Differential equations and exact solutions in the moving sofa
problem*, Experimental Mathematics 27 (2018), 316–330) constructed an ambidextrous sofa of area
`1.64495…` and proposed it as a likely solution of the problem of the largest ambidextrous sofa. The
theorems below prove that every ambidextrous sofa has area at most that of Romik's, and that every
ambidextrous sofa of that area is a rotated and translated copy of Romik's.

## Definitions

The definitions are a verbatim copy of `AmbidextrousSofa/ChallengeDefs.lean`
(`scripts/sync_challenge_defs.py`).

**The plane** is `ℝ × ℝ`; the area of a set is its Lebesgue measure, `volume.real S` (finite for the
compact sets of the theorems). `rotate θ` is the counterclockwise rotation by `θ` about the origin.

**The two hallways.** Both have the incoming arm `(-∞, 1] × [0, 1]`. The hallway that turns
downward (to the right) continues with the outgoing arm `[0, 1] × (-∞, 1]`, and the hallway that
turns upward (to the left) with the outgoing arm `[0, 1] × [0, ∞)`; the second hallway is the
reflection of the first in the center line `y = 1/2` of the incoming arm.

**Motions.** `MovesThrough S hallway incoming outgoing θ c` says that the rigid motion placing each
point `p ∈ S` at `rotate (θ t) p + c t` at the time `t ∈ [0, 1]`, with a continuous angle `θ` and a
continuous translation `c`, starts with `S` in `incoming`, keeps it in `hallway`, and ends with it in
`outgoing`. The motion may pause, turn back, and turn through any angle.

**Ambidextrous sofas.** `IsAmbidextrous S` says that `S` is compact and connected (in particular
nonempty), and that it moves through both hallways, from the incoming arm to the respective outgoing
arm, by two motions that start with the same orientation (`rotate (θ₁ 0) = rotate (θ₂ 0)`). The two
motions may start at different translations and are otherwise independent. The common orientation
matters: Gerver's sofa, which is symmetric under the reflection in a vertical line, passes the
left-turning hallway after a rotation by `π`, so without that condition the problem would be the
ordinary moving sofa problem.

**Romik's ambidextrous sofa** is built from the positive root `Y = 0.2980…` of `4Y³ + 3Y = 1` (the
theorems take `Y` with this property; `existsUnique_root` says that it is unique), through
`β = arctan Y`, `A = 1 / (4 sin β)`, `k = 1 - 4A/3` and `R = cos β / cos (3(π/4 - β)/2)`. Its hull
`referenceHull Y`, its convex hull by `convexHull_referenceSofa`, is the
intersection of the half-planes `p · (cos t, sin t) ≤ h(t)` over the whole circle, where the support
function `h` is, on the upper half,
`h(t) = f(t)` and `h(t + π/2) = g(t)` for `t ∈ [0, π/2]`, with, on `[0, β]`, `[β, π/2 - β]` and
`[π/2 - β, π/2]`:

* `f(t) = cos t + sin t / 2`, `R cos (t/2 + π/8) + k cos t + sin t / 2`,
  `(1 - 2A/3) cos t + sin t / 2 + 1/2`;
* `g(t) = (2A - 1) sin t + cos t / 2 + 1/2`, `R sin (t/2 + π/8) - k sin t + cos t / 2`,
  `(8A/3 - 1) sin t + cos t / 2`;

and on the lower half the reflection of the upper half in the line `y = 1/2`. The sofa
`referenceSofa Y` is this hull with two open regions removed: the
points `(x, y)` with `y < n(x)` and those with `1 - y < n(x)`, where `n = niche (referenceHull Y)` is
the height, above each abscissa, of the region swept by the open inner corner of the downward-turning
hallway as the hallway, with its outer walls supporting the hull, turns through the quarter turn about
it. Precisely, `n(x)` is the supremum over `θ ∈ (0, π/2)` of
`min ((h_K(u_θ) - 1 - x cos θ) / sin θ, (h_K(v_θ) - 1 + x sin θ) / cos θ)`, or `0` if that is
negative, where `K` is the hull, `h_K = support K` its support function, `u_θ = (cos θ, sin θ)` and
`v_θ = (-sin θ, cos θ)`: at the angle `θ` the two inner walls of the hallway are the lines
`p · u_θ = h_K(u_θ) - 1` and `p · v_θ = h_K(v_θ) - 1`, and the minimum is the height above `x` below
which the points lie beyond both of them, inside the hallway's inner corner.

## The theorems

`existsUnique_root`: the equation `4Y³ + 3Y = 1` has exactly one positive solution, so the
definitions above describe one sofa and one number.

`value_eq_romik`: the number `1 + 4Y² + arctan Y = 1.64495…` is Romik's closed form
`∛(3 + 2√2) + ∛(3 - 2√2) - 1 + arctan (½ (∛(√2 + 1) - ∛(√2 - 1)))` for the area of his sofa.

`volume_le` (**optimality**): every ambidextrous sofa has area at most `1 + 4Y² + arctan Y`.

`isAmbidextrous_referenceSofa` and `volume_referenceSofa`: Romik's sofa is an ambidextrous sofa,
of area `1 + 4Y² + arctan Y`; so the bound is the largest area of an ambidextrous sofa.
`isAmbidextrous_image_referenceSofa`: so is every image of Romik's sofa by a rotation followed by a
translation. `convexHull_referenceSofa`: the convex hull of Romik's sofa is `referenceHull Y`.

`volume_eq_iff` (**uniqueness**): an ambidextrous sofa has area `1 + 4Y² + arctan Y` if and only if
it is the image of Romik's sofa by a rotation about the origin followed by a translation.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace Ambidextrous

-- BEGIN CHALLENGE DEFINITIONS

/-- The counterclockwise rotation of the plane `ℝ × ℝ` by the angle `θ` about the origin. -/
def rotate (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * p.1 - Real.sin θ * p.2, Real.sin θ * p.1 + Real.cos θ * p.2)

/-- The incoming arm `(-∞, 1] × [0, 1]` that the two hallways share. -/
def incomingArm : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The outgoing arm `[0, 1] × (-∞, 1]` of the hallway that turns downward, to the right. -/
def lowerOutgoingArm : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- The outgoing arm `[0, 1] × [0, ∞)` of the hallway that turns upward, to the left. -/
def upperOutgoingArm : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2}

/-- `S` moves through `hallway` from `incoming` to `outgoing` along the rigid motion that places
each point `p ∈ S` at `rotate (θ t) p + c t` at the time `t ∈ [0, 1]`: the angle `θ` and the
translation `c` are continuous, `S` starts in `incoming`, stays in `hallway`, and ends in
`outgoing`. The motion may pause and turn back. -/
def MovesThrough (S hallway incoming outgoing : Set (ℝ × ℝ)) (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ) :
    Prop :=
  ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
    (∀ p ∈ S, rotate (θ 0) p + c 0 ∈ incoming) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rotate (θ t) p + c t ∈ hallway) ∧
    (∀ p ∈ S, rotate (θ 1) p + c 1 ∈ outgoing)

/-- An ambidextrous sofa: a compact connected set in the plane that moves through both hallways
of unit width, the one that turns downward and the one that turns upward, starting in their
common incoming arm with the same orientation. The two motions are otherwise independent: they
may start from different translations, and each turns through whatever angle it needs. -/
def IsAmbidextrous (S : Set (ℝ × ℝ)) : Prop :=
  IsCompact S ∧ IsConnected S ∧
    ∃ (θ₁ θ₂ : ℝ → ℝ) (c₁ c₂ : ℝ → ℝ × ℝ), rotate (θ₁ 0) = rotate (θ₂ 0) ∧
      MovesThrough S (incomingArm ∪ lowerOutgoingArm) incomingArm lowerOutgoingArm θ₁ c₁ ∧
      MovesThrough S (incomingArm ∪ upperOutgoingArm) incomingArm upperOutgoingArm θ₂ c₂

/-! Romik's ambidextrous sofa is built from the positive root `Y = 0.2980…` of `4Y³ + 3Y = 1`
through the angle `β = arctan Y`. Its convex hull is the intersection of the half-planes
`p · (cos t, sin t) ≤ h(t)`, whose support function `h` is given on the upper half of the circle
by `h(t) = f(t)` and `h(t + π/2) = g(t)` for `t ∈ [0, π/2]`, and on the lower half by the
reflection `(x, y) ↦ (x, 1 - y)` in the center line of the incoming arm. -/

/-- The coefficient `A = 1 / (4 sin β)` of the support function. -/
def coeffA (Y : ℝ) : ℝ := 1 / (4 * Real.sin (Real.arctan Y))

/-- The coefficient `k = 1 - 4A/3` of the middle phase of the support function. -/
def coeffK (Y : ℝ) : ℝ := 1 - 4 / 3 * coeffA Y

/-- The amplitude `R = cos β / cos (3(π/4 - β)/2)` of the middle phase of the support function. -/
def coeffR (Y : ℝ) : ℝ :=
  Real.cos (Real.arctan Y) / Real.cos (3 / 2 * (Real.pi / 4 - Real.arctan Y))

/-- The support function `f(t) = h(t)`, `t ∈ [0, π/2]`, in three phases separated by `β` and
`π/2 - β`. -/
def supportF (Y t : ℝ) : ℝ :=
  if t ≤ Real.arctan Y then Real.cos t + 1 / 2 * Real.sin t
  else if t ≤ Real.pi / 2 - Real.arctan Y then
    coeffR Y * Real.cos (t / 2 + Real.pi / 8) + coeffK Y * Real.cos t + 1 / 2 * Real.sin t
  else (1 - 2 / 3 * coeffA Y) * Real.cos t + 1 / 2 * Real.sin t + 1 / 2

/-- The support function `g(t) = h(t + π/2)`, `t ∈ [0, π/2]`, in the same three phases. -/
def supportG (Y t : ℝ) : ℝ :=
  if t ≤ Real.arctan Y then (2 * coeffA Y - 1) * Real.sin t + 1 / 2 * Real.cos t + 1 / 2
  else if t ≤ Real.pi / 2 - Real.arctan Y then
    coeffR Y * Real.sin (t / 2 + Real.pi / 8) - coeffK Y * Real.sin t + 1 / 2 * Real.cos t
  else (8 / 3 * coeffA Y - 1) * Real.sin t + 1 / 2 * Real.cos t

/-- The two half-planes with the normals `(cos t, sin t)` and `(cos (t + π/2), sin (t + π/2))`
and the support values `f(t)` and `g(t)`. -/
def halfPlanes (Y t : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 * Real.cos t + p.2 * Real.sin t ≤ supportF Y t ∧
    p.1 * Real.cos (t + Real.pi / 2) + p.2 * Real.sin (t + Real.pi / 2) ≤ supportG Y t}

/-- The hull of Romik's ambidextrous sofa: the intersection of the half-planes for every
`t ∈ [0, π/2]`, and of their reflections in the line `y = 1/2`. It is the convex hull of the sofa
(`convexHull_referenceSofa`). -/
def referenceHull (Y : ℝ) : Set (ℝ × ℝ) :=
  ⋂ t ∈ Icc (0 : ℝ) (Real.pi / 2), halfPlanes Y t ∩ (fun p => (p.1, 1 - p.2)) ⁻¹' halfPlanes Y t

/-- The support function `h_K(v) = sup {p · v | p ∈ K}` of a set `K`. -/
def support (K : Set (ℝ × ℝ)) (v : ℝ × ℝ) : ℝ := sSup ((fun p => p.1 * v.1 + p.2 * v.2) '' K)

/-- The niche of `K` above the abscissa `x`: the supremum, over the angles `θ ∈ (0, π/2)` of the
turn, of the height up to which the open inner corner of the downward-turning hallway reaches on
the vertical line through `x`, when the hallway is turned by `θ` and placed with its two outer walls
supporting `K`; or `0` if that supremum is negative. At the angle `θ` the two inner walls are the
lines `p · (cos θ, sin θ) = h_K(cos θ, sin θ) - 1` and `p · (-sin θ, cos θ) = h_K(-sin θ, cos θ) - 1`;
the points above `x` that lie beyond both of them are those below the minimum of the two heights. -/
def niche (K : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  max (sSup ((fun θ => min
    ((support K (Real.cos θ, Real.sin θ) - 1 - x * Real.cos θ) / Real.sin θ)
    ((support K (-Real.sin θ, Real.cos θ) - 1 + x * Real.sin θ) / Real.cos θ)) ''
      Ioo 0 (Real.pi / 2))) 0

/-- **Romik's ambidextrous sofa**: its convex hull with the two niches removed, the one swept
by the inner corner of the downward-turning hallway from below and its reflection, swept by the
inner corner of the upward-turning hallway, from above. -/
def referenceSofa (Y : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ referenceHull Y ∧ niche (referenceHull Y) p.1 ≤ p.2 ∧
    niche (referenceHull Y) p.1 ≤ 1 - p.2}

-- END CHALLENGE DEFINITIONS

/-- The equation `4Y³ + 3Y = 1` has exactly one positive solution, `Y = 0.2980…`. -/
theorem existsUnique_root : ∃! Y : ℝ, 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1 := by
  sorry

/-- **Romik's value.** The area `1 + 4Y² + arctan Y` of Romik's ambidextrous sofa is
`∛(3 + 2√2) + ∛(3 - 2√2) - 1 + arctan (½ (∛(√2 + 1) - ∛(√2 - 1))) = 1.64495…`. -/
theorem value_eq_romik (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    1 + 4 * Y ^ 2 + Real.arctan Y =
      (3 + 2 * √2) ^ (1 / 3 : ℝ) + (3 - 2 * √2) ^ (1 / 3 : ℝ) - 1 +
        Real.arctan (((√2 + 1) ^ (1 / 3 : ℝ) - (√2 - 1) ^ (1 / 3 : ℝ)) / 2) := by
  sorry

/-- **Optimality.** Every ambidextrous sofa has area at most `1 + 4Y² + arctan Y`. -/
theorem volume_le (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) (S : Set (ℝ × ℝ))
    (hS : IsAmbidextrous S) : volume.real S ≤ 1 + 4 * Y ^ 2 + Real.arctan Y := by
  sorry

/-- Romik's ambidextrous sofa is an ambidextrous sofa. -/
theorem isAmbidextrous_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    IsAmbidextrous (referenceSofa Y) := by
  sorry

/-- Romik's ambidextrous sofa has area `1 + 4Y² + arctan Y`. -/
theorem volume_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    volume.real (referenceSofa Y) = 1 + 4 * Y ^ 2 + Real.arctan Y := by
  sorry

/-- Every image of Romik's ambidextrous sofa by a rotation about the origin followed by a translation
is an ambidextrous sofa. -/
theorem isAmbidextrous_image_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) (θ : ℝ)
    (v : ℝ × ℝ) : IsAmbidextrous ((fun p => rotate θ p + v) '' referenceSofa Y) := by
  sorry

/-- The convex hull of Romik's ambidextrous sofa is `referenceHull Y`. -/
theorem convexHull_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    convexHull ℝ (referenceSofa Y) = referenceHull Y := by
  sorry

/-- **Uniqueness.** An ambidextrous sofa has area `1 + 4Y² + arctan Y` if and only if a rotation
about the origin followed by a translation maps Romik's ambidextrous sofa onto it. -/
theorem volume_eq_iff (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) (S : Set (ℝ × ℝ))
    (hS : IsAmbidextrous S) :
    volume.real S = 1 + 4 * Y ^ 2 + Real.arctan Y ↔
      ∃ (θ : ℝ) (v : ℝ × ℝ), S = (fun p => rotate θ p + v) '' referenceSofa Y := by
  sorry

end Ambidextrous
