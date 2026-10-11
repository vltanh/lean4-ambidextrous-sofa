module

public import AmbidextrousSofa.Analysis.FiniteGraphGreen
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

/-!
# Chord bounds for the literal finite wing lengths

The source masses partition horizontal length and integrate the selected
spatial slope. Their nonnegative weighted Euclidean vectors therefore
sum to the graph's endpoint displacement. The triangle inequality gives
the chord bound, without differentiating a limiting roof or identifying
a weak source measure with graph arclength. Complex numbers supply the
Euclidean norm here; the ambient product norm is not used as length.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace WallExpr

variable {ι : Type*}

def finiteGraphLength [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) : ℝ :=
  ∑ i, e.sourceMass a b l r i * Real.sqrt (1 + (a i) ^ 2)

theorem chord_le_finiteGraphLength [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ)
    (ha : Function.Injective a) {l r : ℝ} (hlr : l ≤ r) :
    Real.sqrt ((r - l) ^ 2 + (e.affineGraph a b r - e.affineGraph a b l) ^ 2) ≤
      e.finiteGraphLength a b l r := by
  have h := norm_sum_le Finset.univ fun i => e.sourceMass a b l r i • (⟨1, a i⟩ : ℂ)
  rw [← e.sum_sourceMass a b hlr, ← e.integral_sourceSlope a b ha,
    e.integral_sourceDensity_eq_sum a b a hlr]
  convert h using 1 <;> simp [finiteGraphLength, Complex.norm_eq_sqrt_sq_add_sq, Complex.re_sum,
    Complex.im_sum, abs_of_nonneg (e.sourceMass_nonneg ..)]

end WallExpr

namespace FinitePolygon

variable {ι : Type*}

theorem finiteWingLength_eq_graphLengths [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (hunit : ∀ i, coordDot (normal i) (normal i) = 1)
    (hpositive : ∀ i, 0 < (normal i).2) :
    finiteWingLength U normal =
      (roofExpr (ι := ι)).finiteGraphLength (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i)))
        (horizontalLeft U) (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
      (roofExpr (ι := ι)).finiteGraphLength (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i)))
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U) := by
  have harc : ∀ i, normalArcFactor normal i = √(1 + wallSlope normal i ^ 2) := by
    rintro (_ | i)
    · simp [normalArcFactor, wallSlope]
    · have h1 := hunit i
      have h2 := hpositive i
      rw [coordDot] at h1
      rw [normalArcFactor, wallSlope, eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
      field_simp
      linarith
  simp only [finiteWingLength, finiteWingMass, harc, WallExpr.finiteGraphLength, add_mul,
    Finset.sum_add_distrib]

theorem wing_chords_le_finiteWingLength [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane)
    (hunit : ∀ i, coordDot (normal i) (normal i) = 1)
    (hpositive : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal) :
    Real.sqrt (((horizontalRight U - horizontalLeft U) / 4) ^ 2 +
      (capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U)) ^ 2) +
    Real.sqrt (((horizontalRight U - horizontalLeft U) / 4) ^ 2 +
      (capRoof U (horizontalRight U) -
        capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) ^ 2) ≤
      finiteWingLength U normal := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hpositive hpoly
  rw [finiteWingLength_eq_graphLengths U normal hunit hpositive]
  set l := horizontalLeft U
  set r := horizontalRight U
  have key {x y : ℝ} (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) (hxy : x ≤ y) :
      √((y - x) ^ 2 + (capRoof U y - capRoof U x) ^ 2) ≤
        (roofExpr (ι := ι)).finiteGraphLength (wallSlope normal)
          (roofIntercept normal (fun i => support U (normal i))) x y := by
    rw [← hroof hx, ← hroof hy]
    exact (roofExpr (ι := ι)).chord_le_finiteGraphLength _ _ hslope hxy
  convert add_le_add (key (x := l) (y := l + (r - l) / 4) _ _ _)
    (key (x := r - (r - l) / 4) (y := r) _ _ _) using 4
  all_goals first | ring1 | exact ⟨by linarith, by linarith⟩ | linarith

end FinitePolygon

/-- Reflect the second vertical displacement before adding the two chord
vectors. This keeps both horizontal lengths and both upward height gains. -/
theorem two_mul_sqrt_half_sum_le_chord_sum (C a b : ℝ) :
    2 * Real.sqrt (C ^ 2 + ((a + b) / 2) ^ 2) ≤
      Real.sqrt (C ^ 2 + a ^ 2) + Real.sqrt (C ^ 2 + b ^ 2) := by
  have h := norm_add_le (⟨C, a⟩ : ℂ) ⟨C, b⟩
  rw [show (⟨C, a⟩ : ℂ) + ⟨C, b⟩ = (2 : ℝ) • ⟨C, (a + b) / 2⟩ by
    apply Complex.ext <;> simp <;> ring] at h
  simpa [Complex.norm_eq_sqrt_sq_add_sq] using h

end AmbidextrousSofa
