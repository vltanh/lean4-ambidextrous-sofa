module

public import AmbidextrousSofa.ChallengeDefs
public import AmbidextrousSofa.Theorems.Optimality
public import AmbidextrousSofa.Reference.Body
public import AmbidextrousSofa.Reference.Value
public import AmbidextrousSofa.Reference.Regularity
public import AmbidextrousSofa.Measure.ReferenceOrbit

/-!
# The main theorems in the vocabulary of the Challenge

`ChallengeDefs` restates, with Mathlib only, the definitions that the main theorems need: the
two hallways, the motions, ambidextrous sofas and Romik's ambidextrous sofa, which it builds from
any positive root `Y` of `4Y³ + 3Y = 1`. This module proves that each of them is the library's
definition, and derives the main theorems of the manuscript in that vocabulary:

* `existsUnique_root`: the cubic `4Y³ + 3Y = 1` has exactly one positive root;
* `volume_le`: every ambidextrous sofa has area at most `M = 1 + 4Y² + arctan Y` (MS.3);
* `value_eq_romik`: `M` is Romik's closed form `∛(3 + 2√2) + ∛(3 - 2√2) - 1 + arctan (…)`;
* `isAmbidextrous_referenceSofa`, `volume_referenceSofa`: Romik's ambidextrous sofa is an
  ambidextrous sofa of area `M` (MS.15), and so is each of its images by a rotation and a
  translation (`isAmbidextrous_image_referenceSofa`);
* `convexHull_referenceSofa`: its convex hull is the hull of the Challenge (MS.14);
* `volume_eq_iff`: an ambidextrous sofa has area `M` if and only if a rotation followed by a
  translation maps Romik's ambidextrous sofa onto it (the equality case of MS.3).

`Solution.lean` restates them under the names of `Challenge.lean`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Main

/-- The Challenge's rotation is the library's. -/
theorem rotate_eq : Ambidextrous.rotate = rotate := rfl

/-- The Challenge's rigid motions are the library's. -/
theorem image_rotate_add (θ : ℝ) (v : Plane) (S : Set Plane) :
    (fun p => Ambidextrous.rotate θ p + v) '' S = rigidMap θ v '' S := rfl

/-- A motion in the Challenge's sense is a passage in the library's sense. -/
theorem movesThrough_iff {S hall incoming outgoing : Set Plane} {θ : ℝ → ℝ} {c : ℝ → Plane} :
    Ambidextrous.MovesThrough S hall incoming outgoing θ c ↔
      ∃ path : RigidMotionPath, path.angle = θ ∧ path.shift = c ∧
        Passage S hall incoming outgoing path := by
  constructor
  · rintro ⟨hθ, hc, hstart, hinside, hfinish⟩
    refine ⟨⟨θ, c, hθ, hc⟩, rfl, rfl, ⟨?_, ?_, ?_⟩⟩
    · rintro t ht _ ⟨p, hp, rfl⟩
      exact hinside t ht p hp
    · rintro _ ⟨p, hp, rfl⟩
      exact hstart p hp
    · rintro _ ⟨p, hp, rfl⟩
      exact hfinish p hp
  · rintro ⟨path, rfl, rfl, hpass⟩
    refine ⟨path.continuous_angle, path.continuous_shift, ?_, ?_, ?_⟩
    · exact fun p hp => hpass.start ⟨p, hp, rfl⟩
    · exact fun t ht p hp => hpass.inside t ht ⟨p, hp, rfl⟩
    · exact fun p hp => hpass.finish ⟨p, hp, rfl⟩

/-- The Challenge's ambidextrous sofas are the library's. -/
theorem isAmbidextrous_iff (S : Set Plane) :
    Ambidextrous.IsAmbidextrous S ↔ IsAmbidextrous S := by
  constructor
  · rintro ⟨hcompact, hconn, θ₁, θ₂, c₁, c₂, horient, hlower, hupper⟩
    obtain ⟨lower, rfl, rfl, hl⟩ := movesThrough_iff.mp hlower
    obtain ⟨upper, rfl, rfl, hu⟩ := movesThrough_iff.mp hupper
    exact ⟨hconn.nonempty, hcompact, hconn, lower, upper, horient, hl, hu⟩
  · rintro ⟨_, hcompact, hconn, lower, upper, horient, hl, hu⟩
    exact ⟨hcompact, hconn, lower.angle, upper.angle, lower.shift, upper.shift, horient,
      movesThrough_iff.mpr ⟨lower, rfl, rfl, hl⟩, movesThrough_iff.mpr ⟨upper, rfl, rfl, hu⟩⟩

/-- The positive root of `4Y³ + 3Y = 1` is the library's `Y`. -/
theorem eq_Y {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) : Y' = Y :=
  eq_Y_of_cubic_eq_zero (by unfold cubic; linarith [hY.2])

/-- The cubic `4Y³ + 3Y = 1` has exactly one positive root. -/
theorem existsUnique_root : ∃! Y' : ℝ, 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1 :=
  ⟨Y, ⟨Y_pos, Y_equation⟩, fun _ hY => eq_Y hY⟩

/-- `(x ^ (1/3)) ^ 3 = x` for `x ≥ 0`. -/
theorem rpow_one_third_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- **Romik's closed form.** With `a = ∛(√2 + 1)` and `b = ∛(√2 - 1)`, the number `(a - b) / 2` is
the positive root of `4Y³ + 3Y = 1` (Cardano's formula; `ab = 1`), and
`1 + 4((a - b) / 2)² = ∛(3 + 2√2) + ∛(3 - 2√2) - 1`. -/
theorem cardano :
    let a := (√2 + 1) ^ (1 / 3 : ℝ)
    let b := (√2 - 1) ^ (1 / 3 : ℝ)
    0 < (a - b) / 2 ∧ 4 * ((a - b) / 2) ^ 3 + 3 * ((a - b) / 2) = 1 ∧
      1 + 4 * ((a - b) / 2) ^ 2 =
        (3 + 2 * √2) ^ (1 / 3 : ℝ) + (3 - 2 * √2) ^ (1 / 3 : ℝ) - 1 := by
  intro a b
  have h2 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : (0 : ℝ) ≤ √2 + 1 := by linarith
  have hm : (0 : ℝ) ≤ √2 - 1 := by linarith
  have ha3 : a ^ 3 = √2 + 1 := rpow_one_third_pow_three hp
  have hb3 : b ^ 3 = √2 - 1 := rpow_one_third_pow_three hm
  have hab : a * b = 1 := by
    rw [← Real.mul_rpow hp hm]
    have : (√2 + 1) * (√2 - 1) = 1 := by nlinarith
    rw [this, Real.one_rpow]
  have hlt : b < a := Real.rpow_lt_rpow hm (by linarith) (by norm_num)
  have ha2 : a ^ 2 = (3 + 2 * √2) ^ (1 / 3 : ℝ) := by
    rw [show (3 + 2 * √2) = (√2 + 1) ^ 2 by nlinarith, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul hp, ← Real.rpow_mul hp]
    norm_num
  have hb2 : b ^ 2 = (3 - 2 * √2) ^ (1 / 3 : ℝ) := by
    rw [show (3 - 2 * √2) = (√2 - 1) ^ 2 by nlinarith, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul hm, ← Real.rpow_mul hm]
    norm_num
  refine ⟨by linarith, ?_, ?_⟩
  · have : 4 * ((a - b) / 2) ^ 3 + 3 * ((a - b) / 2) =
        (a ^ 3 - b ^ 3) / 2 - 3 / 2 * (a * b) * (a - b) + 3 / 2 * (a - b) := by ring
    rw [this, ha3, hb3, hab]
    ring
  · rw [← ha2, ← hb2]
    nlinarith [hab]

/-- The Challenge's value `1 + 4Y² + arctan Y` is the library's `M`. -/
theorem value_eq {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) :
    1 + 4 * Y' ^ 2 + Real.arctan Y' = M := by
  rw [eq_Y hY]
  rfl

/-- **Romik's value.** The area `1 + 4Y² + arctan Y` of Romik's ambidextrous sofa is
`∛(3 + 2√2) + ∛(3 - 2√2) - 1 + arctan (½ (∛(√2 + 1) - ∛(√2 - 1))) = 1.64495…`, the closed form in
Romik's paper. -/
theorem value_eq_romik {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) :
    1 + 4 * Y' ^ 2 + Real.arctan Y' =
      (3 + 2 * √2) ^ (1 / 3 : ℝ) + (3 - 2 * √2) ^ (1 / 3 : ℝ) - 1 +
        Real.arctan (((√2 + 1) ^ (1 / 3 : ℝ) - (√2 - 1) ^ (1 / 3 : ℝ)) / 2) := by
  obtain ⟨hpos, hcubic, hsq⟩ := cardano
  have h : ((√2 + 1) ^ (1 / 3 : ℝ) - (√2 - 1) ^ (1 / 3 : ℝ)) / 2 = Y' :=
    (eq_Y ⟨hpos, hcubic⟩).trans (eq_Y hY).symm
  rw [← hsq, h]

/-- The Challenge's support coordinates are the library's `referenceF` and `referenceG`. -/
theorem supportF_eq (t : ℝ) : Ambidextrous.supportF Y t = Reference.referenceF t := rfl

theorem supportG_eq (t : ℝ) : Ambidextrous.supportG Y t = Reference.referenceG t := rfl

/-- The Challenge's hull of Romik's ambidextrous sofa is the library's `referenceHull`. -/
theorem referenceHull_eq : Ambidextrous.referenceHull Y = Reference.referenceHull := rfl

/-- The Challenge's niche is the library's swept niche of the full quarter turn. -/
theorem niche_eq (K : Set Plane) (x : ℝ) :
    Ambidextrous.niche K x = sweptNiche K (Real.pi / 2) x := rfl

/-- The Challenge's Romik ambidextrous sofa is the library's `referenceSofa`. -/
theorem referenceSofa_eq {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) :
    Ambidextrous.referenceSofa Y' = Reference.referenceSofa := by
  rw [eq_Y hY]
  rfl

/-- **MS.3.** Every ambidextrous sofa has area at most `1 + 4Y² + arctan Y`. -/
theorem volume_le {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) (S : Set (ℝ × ℝ))
    (hS : Ambidextrous.IsAmbidextrous S) :
    volume.real S ≤ 1 + 4 * Y' ^ 2 + Real.arctan Y' := by
  rw [value_eq hY]
  exact ((isAmbidextrous_iff S).mp hS).volumeReal_le_M

/-- Romik's ambidextrous sofa is an ambidextrous sofa. -/
theorem isAmbidextrous_referenceSofa {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) :
    Ambidextrous.IsAmbidextrous (Ambidextrous.referenceSofa Y') := by
  rw [referenceSofa_eq hY, isAmbidextrous_iff]
  exact Reference.isAmbidextrous_referenceSofa

/-- **MS.15.** Romik's ambidextrous sofa has area `1 + 4Y² + arctan Y`. -/
theorem volume_referenceSofa {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) :
    volume.real (Ambidextrous.referenceSofa Y') = 1 + 4 * Y' ^ 2 + Real.arctan Y' := by
  rw [referenceSofa_eq hY, value_eq hY]
  exact Reference.volumeReal_referenceSofa

/-- Every image of Romik's ambidextrous sofa by a rotation followed by a translation is an
ambidextrous sofa. -/
theorem isAmbidextrous_image_referenceSofa {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1)
    (θ : ℝ) (v : ℝ × ℝ) :
    Ambidextrous.IsAmbidextrous ((fun p => Ambidextrous.rotate θ p + v) ''
      Ambidextrous.referenceSofa Y') := by
  rw [referenceSofa_eq hY, image_rotate_add, isAmbidextrous_iff]
  exact Reference.isAmbidextrous_rigidImage_referenceSofa θ v

/-- **MS.14.** The convex hull of Romik's ambidextrous sofa is the hull of the Challenge. -/
theorem convexHull_referenceSofa {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) :
    convexHull ℝ (Ambidextrous.referenceSofa Y') = Ambidextrous.referenceHull Y' := by
  rw [referenceSofa_eq hY, eq_Y hY, referenceHull_eq]
  exact Reference.actualHull_referenceSofa

/-- **The equality case of MS.3.** An ambidextrous sofa has area `1 + 4Y² + arctan Y` if and only
if a rotation about the origin followed by a translation maps Romik's ambidextrous sofa onto it. -/
theorem volume_eq_iff {Y' : ℝ} (hY : 0 < Y' ∧ 4 * Y' ^ 3 + 3 * Y' = 1) (S : Set (ℝ × ℝ))
    (hS : Ambidextrous.IsAmbidextrous S) :
    volume.real S = 1 + 4 * Y' ^ 2 + Real.arctan Y' ↔
      ∃ (θ : ℝ) (v : ℝ × ℝ),
        S = (fun p => Ambidextrous.rotate θ p + v) '' Ambidextrous.referenceSofa Y' := by
  rw [value_eq hY, referenceSofa_eq hY]
  simp only [image_rotate_add]
  exact ((isAmbidextrous_iff S).mp hS).volumeReal_eq_M_iff

end AmbidextrousSofa.Main
