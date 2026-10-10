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

theorem norm_complex_pair (x y : ℝ) :
    ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  simp only [Complex.norm_def, Complex.normSq_mk, pow_two]

theorem sqrt_sum_sq_le_sum_weighted_graph_norm {ι : Type*} [Fintype ι]
    (m a : ι → ℝ) (hm : ∀ i, 0 ≤ m i) :
    Real.sqrt ((∑ i, m i) ^ 2 + (∑ i, m i * a i) ^ 2) ≤
      ∑ i, m i * Real.sqrt (1 + (a i) ^ 2) := by
  classical
  have hsum : (∑ i, m i • (⟨1, a i⟩ : ℂ)) =
      (⟨∑ i, m i, ∑ i, m i * a i⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im]
  have hnorm (i : ι) : ‖m i • (⟨1, a i⟩ : ℂ)‖ =
      m i * Real.sqrt (1 + (a i) ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm i), norm_complex_pair]
    norm_num
  simpa only [hsum, norm_complex_pair, hnorm] using
    (norm_sum_le Finset.univ (fun i => m i • (⟨1, a i⟩ : ℂ)))

namespace WallExpr

variable {ι : Type*}

def finiteGraphLength [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) : ℝ :=
  ∑ i, e.sourceMass a b l r i * Real.sqrt (1 + (a i) ^ 2)

theorem chord_le_finiteGraphLength [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ)
    (ha : Function.Injective a) {l r : ℝ} (hlr : l ≤ r) :
    Real.sqrt ((r - l) ^ 2 + (e.affineGraph a b r - e.affineGraph a b l) ^ 2) ≤
      e.finiteGraphLength a b l r := by
  have hslope : (∑ i, e.sourceMass a b l r i * a i) =
      e.affineGraph a b r - e.affineGraph a b l := by
    rw [← e.integral_sourceDensity_eq_sum a b a hlr,
      e.integral_sourceSlope a b ha]
  simpa only [e.sum_sourceMass a b hlr, hslope, finiteGraphLength] using
    sqrt_sum_sq_le_sum_weighted_graph_norm (e.sourceMass a b l r) a
      (e.sourceMass_nonneg a b l r)

end WallExpr

namespace FinitePolygon

variable {ι : Type*}

theorem normalArcFactor_eq_sqrt (normal : ι → Plane)
    (hunit : ∀ i, coordDot (normal i) (normal i) = 1)
    (hpositive : ∀ i, 0 < (normal i).2) (i : Option ι) :
    normalArcFactor normal i = Real.sqrt (1 + (wallSlope normal i) ^ 2) := by
  cases i with
  | none => norm_num [normalArcFactor, wallSlope]
  | some i =>
    have hsq : (normal i).1 ^ 2 + (normal i).2 ^ 2 = 1 := by
      simpa only [coordDot, pow_two] using hunit i
    have heq : 1 + (-(normal i).1 / (normal i).2) ^ 2 =
        (1 / (normal i).2) ^ 2 := by
      field_simp [(hpositive i).ne']
      nlinarith
    change 1 / (normal i).2 = Real.sqrt (1 + (-(normal i).1 / (normal i).2) ^ 2)
    rw [heq, Real.sqrt_sq (one_div_nonneg.mpr (hpositive i).le)]

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
  simp only [finiteWingLength, finiteWingMass, normalArcFactor_eq_sqrt normal hunit hpositive,
    WallExpr.finiteGraphLength, add_mul, Finset.sum_add_distrib]

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
  let l := horizontalLeft U
  let r := horizontalRight U
  let u := l + (r - l) / 4
  let v := r - (r - l) / 4
  have hlu : l ≤ u := by dsimp [u]; linarith
  have hvr : v ≤ r := by dsimp [v]; linarith
  have hu : u ∈ Icc l r := ⟨hlu, by dsimp [u]; linarith⟩
  have hv : v ∈ Icc l r := ⟨by dsimp [v]; linarith, hvr⟩
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hpositive hpoly
  have hleft := (roofExpr (ι := ι)).chord_le_finiteGraphLength (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hslope hlu
  have hright := (roofExpr (ι := ι)).chord_le_finiteGraphLength (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hslope hvr
  have hgraph (x : ℝ) (hx : x ∈ Icc l r) :
      (roofExpr (ι := ι)).affineGraph (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) x = capRoof U x := hroof hx
  rw [hgraph u hu, hgraph l ⟨le_rfl, hlr⟩] at hleft
  rw [hgraph r ⟨hlr, le_rfl⟩, hgraph v hv] at hright
  have hluEq : u - l = (r - l) / 4 := by dsimp [u]; ring
  have hvrEq : r - v = (r - l) / 4 := by dsimp [v]; ring
  rw [hluEq] at hleft
  rw [hvrEq] at hright
  rw [finiteWingLength_eq_graphLengths U normal hunit hpositive]
  exact add_le_add hleft hright

end FinitePolygon

/-- Reflect the second vertical displacement before adding the two chord
vectors. This keeps both horizontal lengths and both upward height gains. -/
theorem two_mul_sqrt_half_sum_le_chord_sum (C a b : ℝ) :
    2 * Real.sqrt (C ^ 2 + ((a + b) / 2) ^ 2) ≤
      Real.sqrt (C ^ 2 + a ^ 2) + Real.sqrt (C ^ 2 + b ^ 2) := by
  have heq : (⟨C, a⟩ : ℂ) + (⟨C, b⟩ : ℂ) =
      (2 : ℝ) • (⟨C, (a + b) / 2⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im] <;> ring
  have h := norm_add_le (⟨C, a⟩ : ℂ) (⟨C, b⟩ : ℂ)
  rw [heq, norm_smul] at h
  simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    norm_complex_pair] using h

end AmbidextrousSofa
