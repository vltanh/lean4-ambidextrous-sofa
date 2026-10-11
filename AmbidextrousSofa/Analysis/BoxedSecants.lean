module

public import AmbidextrousSofa.Analysis.DyadicNeighbors
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Uniform bounds for actual sampled support secants

Both ends of the support difference are evaluated at actual support
maximizers. A nonnegative cosine allows the normal contribution to be
discarded, leaving a tangent coordinate bounded by the containing box.
The estimate is uniform even when the angular mesh tends to zero.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

open MovingSofaOptimality in
theorem IsDownwardCap.abs_support_secant_le_box {U : Set Plane}
    (hU : IsDownwardCap U) {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (t δ : ℝ) (hc : 0 ≤ Real.cos δ) (hs : Real.sin δ ≠ 0) :
    |(support U (unitNormal (t + δ)) - support U (unitNormal t) * Real.cos δ) / Real.sin δ| ≤
      R + 1 := by
  have hv {p : Plane} (hp : p ∈ U) : |Real.sin δ * dot p (vvec t)| ≤ |Real.sin δ| * (R + 1) := by
    have h := abs_dot_uvec_le p (t + Real.pi / 2)
    have hy : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [(hbox hp).2.1], (hbox hp).2.2⟩
    rw [uvec_add_pi_div_two] at h
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [abs_le.mpr (hbox hp).1]) (abs_nonneg _)
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hU.isCompact hU.nonempty t
  obtain ⟨q, hq, hqt⟩ := exists_dot_eq_supp hU.isCompact hU.nonempty (t + δ)
  have hlo := dot_le_supp hU.isCompact hp (t + δ)
  have hqframe := dot_uvec_eq_cos_add_sin q (t + δ) t
  rw [dot_uvec_eq_cos_add_sin _ (t + δ) t, add_sub_cancel_left, hpt] at hlo
  rw [add_sub_cancel_left, hqt] at hqframe
  have hnormal := mul_le_mul_of_nonneg_left (dot_le_supp hU.isCompact hq t) hc
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hs), mul_comm (R + 1)]
  change |supp U (t + δ) - supp U t * Real.cos δ| ≤ _
  exact abs_le.mpr ⟨by linarith [(abs_le.mp (hv hp)).1], by linarith [(abs_le.mp (hv hq)).2]⟩

namespace AngularGrid

theorem abs_firstCornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (t δ : ℝ)
    (hc : 0 ≤ Real.cos δ) (hs : Real.sin δ ≠ 0) :
    |firstCornerSecant U t δ| ≤ 2 * R + 3 := by
  have hsupport : |support U (unitNormal t)| ≤ R + 1 :=
    MovingSofaOptimality.abs_supp_le_box hU.imported_isConvexBody hbox t
  have hsecant := hU.abs_support_secant_le_box hbox (t + Real.pi / 2) δ hc hs
  simp only [add_right_comm t (Real.pi / 2) δ, ← companionNormal_eq_unitNormal] at hsecant
  rw [firstCornerSecant, abs_le] at *
  constructor <;> linarith [hsupport.1, hsupport.2, hsecant.1, hsecant.2]

theorem abs_secondCornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (t δ : ℝ)
    (hc : 0 ≤ Real.cos δ) (hs : Real.sin δ ≠ 0) :
    |secondCornerSecant U t δ| ≤ 2 * R + 3 := by
  have hsupport : |support U (unitNormal (t + Real.pi / 2))| ≤ R + 1 :=
    MovingSofaOptimality.abs_supp_le_box hU.imported_isConvexBody hbox (t + Real.pi / 2)
  rw [← companionNormal_eq_unitNormal] at hsupport
  have hsecant := hU.abs_support_secant_le_box hbox t (-δ) (by rwa [Real.cos_neg])
    (by rwa [Real.sin_neg, neg_ne_zero])
  simp only [Real.cos_neg, Real.sin_neg, div_neg, abs_neg, ← sub_eq_add_neg] at hsecant
  rw [secondCornerSecant, abs_le] at *
  constructor <;> linarith [hsupport.1, hsupport.2, hsecant.1, hsecant.2]

theorem abs_cornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (j : SourceIndex (dyadic n)) : |cornerSecant U n j| ≤ 2 * R + 3 := by
  rcases j with t | t
  exacts [abs_firstCornerSecant_le_box hU hbox t.val (mesh n) (mesh_cos_pos n).le
    (mesh_sin_pos n).ne', abs_secondCornerSecant_le_box hU hbox t.val (mesh n)
    (mesh_cos_pos n).le (mesh_sin_pos n).ne']

theorem tan_le_two_mul {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Real.tan δ ≤ 2 * δ := by
  have hcos : 1 / 2 ≤ Real.cos δ := Real.cos_pi_div_three ▸ Real.cos_le_cos_of_nonneg_of_le_pi
    hδ.1 (by linarith [Real.pi_pos]) (by linarith [hδ.2, Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
  linarith [Real.sin_le hδ.1, mul_le_mul_of_nonneg_left hcos hδ.1]

theorem finiteCurvatureDensity_le_coarse {q δ B : ℝ} (hB : 0 ≤ B) (hq : |q| ≤ B)
    (hδ : δ ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    finiteCurvatureDensity q δ ≤ (2 * B + 4) * δ := by
  have hh : Real.tan (δ / 2) ≤ δ := by
    linarith [tan_le_two_mul (δ := δ / 2) ⟨by linarith [hδ.1], by linarith [hδ.2, Real.pi_pos]⟩]
  have hA : Real.tan δ * (|q| + Real.tan (δ / 2)) ≤ 2 * δ * (B + 1) :=
    (mul_le_mul_of_nonneg_left (add_le_add hq (hh.trans (hδ.2.trans (by
      linarith [Real.pi_le_four])))) (Real.tan_nonneg_of_nonneg_of_le_pi_div_two hδ.1
      (by linarith [hδ.2, Real.pi_pos]))).trans
      (mul_le_mul_of_nonneg_right (tan_le_two_mul hδ) (by linarith))
  exact max_le (by linarith [hδ.1]) (by linarith [mul_nonneg hB hδ.1, hδ.1])

theorem finiteCurvatureDensity_corner_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (j : SourceIndex (dyadic n)) :
    finiteCurvatureDensity (cornerSecant U n j) (mesh n) ≤ (4 * R + 10) * mesh n :=
  (finiteCurvatureDensity_le_coarse (by linarith : 0 ≤ 2 * R + 3)
    (abs_cornerSecant_le_box hU hbox n j) ⟨(mesh_pos n).le, mesh_le_pi_div_four n⟩).trans_eq
    (by ring)

theorem IsSelectedPolygon.curvature_atom_coarse {target U : Set Plane}
    {a b coefficient R : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (j : SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      (4 * R + 10) * mesh level + middleOuterMass U (dyadic level) j +
        selectionDefect target U level coefficient j := by
  linarith [hU.curvature_atom_refined hcoefficient j,
    finiteCurvatureDensity_corner_le_box hU.isCap hR hbox level j]

end AngularGrid

end AmbidextrousSofa
