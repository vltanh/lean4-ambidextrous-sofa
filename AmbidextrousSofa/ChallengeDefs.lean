module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# The definitions that `Challenge.lean` copies

The block between the markers below is copied word for word into `Challenge.lean`
(`scripts/sync_challenge_defs.py`), so that the Challenge and the Solution state their theorems
about the same constants. It uses only Mathlib. `AmbidextrousSofa/Main.lean` relates each of these
definitions to the definitions of the library.
-/

@[expose] public section

noncomputable section

open Set

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

end Ambidextrous
