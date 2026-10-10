import AmbidextrousSofa.Analysis.DyadicNeighbors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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

theorem abs_dot_companion_le_box {U : Set Plane} {R : ℝ}
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) {p : Plane} (hp : p ∈ U) (t : ℝ) :
    |Imported.dot p (Imported.vvec t)| ≤ R + 1 := by
  have hx := abs_le.mpr (hbox hp).1
  have hy : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [(hbox hp).2.1], (hbox hp).2.2⟩
  have h := Imported.abs_dot_uvec_le p (t + Real.pi / 2)
  have heq : Imported.uvec (t + Real.pi / 2) = Imported.vvec t :=
    (companionNormal_eq_unitNormal t).symm
  rw [heq] at h
  linarith

theorem IsDownwardCap.abs_support_rotated_difference_le_box {U : Set Plane}
    (hU : IsDownwardCap U) {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (t δ : ℝ) (hc : 0 ≤ Real.cos δ) :
    |support U (unitNormal (t + δ)) - support U (unitNormal t) * Real.cos δ| ≤
      |Real.sin δ| * (R + 1) := by
  obtain ⟨p, hp, hpt⟩ := Imported.exists_dot_eq_supp hU.isCompact hU.nonempty t
  obtain ⟨q, hq, hqt⟩ := Imported.exists_dot_eq_supp hU.isCompact hU.nonempty (t + δ)
  have hlo := Imported.dot_le_supp hU.isCompact hp (t + δ)
  rw [Imported.dot_uvec_eq_cos_add_sin _ (t + δ) t,
    show t + δ - t = δ by ring, hpt] at hlo
  have hqframe := Imported.dot_uvec_eq_cos_add_sin q (t + δ) t
  rw [show t + δ - t = δ by ring, hqt] at hqframe
  have hnormal := mul_le_mul_of_nonneg_left (Imported.dot_le_supp hU.isCompact hq t) hc
  have hpbound : |Real.sin δ * Imported.dot p (Imported.vvec t)| ≤ |Real.sin δ| * (R + 1) := by
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left
      (abs_dot_companion_le_box hbox hp t) (abs_nonneg (Real.sin δ))
  have hqbound : |Real.sin δ * Imported.dot q (Imported.vvec t)| ≤ |Real.sin δ| * (R + 1) := by
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left
      (abs_dot_companion_le_box hbox hq t) (abs_nonneg (Real.sin δ))
  change |Imported.supp U (t + δ) - Imported.supp U t * Real.cos δ| ≤ _
  apply abs_le.mpr
  constructor
  · linarith [(abs_le.mp hpbound).1]
  · linarith [(abs_le.mp hqbound).2]

theorem IsDownwardCap.abs_support_secant_le_box {U : Set Plane}
    (hU : IsDownwardCap U) {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (t δ : ℝ) (hc : 0 ≤ Real.cos δ) (hs : Real.sin δ ≠ 0) :
    |(support U (unitNormal (t + δ)) - support U (unitNormal t) * Real.cos δ) / Real.sin δ| ≤
      R + 1 := by
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hs)]
  simpa only [mul_comm (R + 1) |Real.sin δ|] using
    hU.abs_support_rotated_difference_le_box hbox t δ hc

namespace AngularGrid

theorem abs_firstCornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (t δ : ℝ)
    (hc : 0 ≤ Real.cos δ) (hs : Real.sin δ ≠ 0) :
    |firstCornerSecant U t δ| ≤ 2 * R + 3 := by
  have hsupport := Imported.abs_supp_le_box hU.imported_isConvexBody hbox t
  have hsecant := hU.abs_support_secant_le_box hbox (t + Real.pi / 2) δ hc hs
  rw [show t + Real.pi / 2 + δ = (t + δ) + Real.pi / 2 by ring] at hsecant
  simp only [← companionNormal_eq_unitNormal] at hsecant
  change |support U (unitNormal t)| ≤ R + 1 at hsupport
  unfold firstCornerSecant
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hsupport).1, (abs_le.mp hsupport).2,
    (abs_le.mp hsecant).1, (abs_le.mp hsecant).2]

theorem abs_secondCornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (t δ : ℝ)
    (hc : 0 ≤ Real.cos δ) (hs : Real.sin δ ≠ 0) :
    |secondCornerSecant U t δ| ≤ 2 * R + 3 := by
  have hsupport := Imported.abs_supp_le_box hU.imported_isConvexBody hbox (t + Real.pi / 2)
  change |support U (unitNormal (t + Real.pi / 2))| ≤ R + 1 at hsupport
  rw [← companionNormal_eq_unitNormal] at hsupport
  have hsecant := hU.abs_support_secant_le_box hbox t (-δ)
    (by simpa only [Real.cos_neg] using hc) (by simpa only [Real.sin_neg, neg_ne_zero] using hs)
  simp only [Real.cos_neg, Real.sin_neg, div_neg, abs_neg,
    show t + -δ = t - δ by ring] at hsecant
  unfold secondCornerSecant
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hsupport).1, (abs_le.mp hsupport).2,
    (abs_le.mp hsecant).1, (abs_le.mp hsecant).2]

theorem abs_cornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (j : SourceIndex (dyadic n)) : |cornerSecant U n j| ≤ 2 * R + 3 := by
  cases j with
  | inl t => exact abs_firstCornerSecant_le_box hU hbox t.val (mesh n)
      (mesh_cos_pos n).le (mesh_sin_pos n).ne'
  | inr t => exact abs_secondCornerSecant_le_box hU hbox t.val (mesh n)
      (mesh_cos_pos n).le (mesh_sin_pos n).ne'

theorem tan_le_two_mul {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Real.tan δ ≤ 2 * δ := by
  have hc : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδ.1, Real.pi_pos], by linarith [hδ.2, Real.pi_pos]⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hδ.1
    (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi)
    (by linarith [hδ.2, Real.pi_pos] : δ ≤ Real.pi / 3)
  rw [Real.cos_pi_div_three] at hcos
  have hmul := mul_le_mul_of_nonneg_left hcos hδ.1
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hc]
  nlinarith [Real.sin_le hδ.1]

theorem finiteCurvatureDensity_le_coarse {q δ B : ℝ} (hB : 0 ≤ B) (hq : |q| ≤ B)
    (hδ : δ ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    finiteCurvatureDensity q δ ≤ (2 * B + 4) * δ := by
  have hhalf : δ / 2 ∈ Icc (0 : ℝ) (Real.pi / 4) := by
    constructor <;> linarith [hδ.1, hδ.2, Real.pi_pos]
  have ht0 := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hδ.1
    (by linarith [hδ.2, Real.pi_pos])
  have ht := tan_le_two_mul hδ
  have hh : Real.tan (δ / 2) ≤ δ := by
    nlinarith [tan_le_two_mul hhalf]
  have hh1 : Real.tan (δ / 2) ≤ 1 := by
    have h := Real.strictMonoOn_tan.monotoneOn
      (show δ / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [hhalf.1, Real.pi_pos], by linarith [hhalf.2, Real.pi_pos]⟩)
      (show Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hhalf.2
    simpa only [Real.tan_pi_div_four] using h
  have hA : Real.tan δ * (|q| + Real.tan (δ / 2)) ≤ 2 * δ * (B + 1) := by
    calc
      Real.tan δ * (|q| + Real.tan (δ / 2)) ≤ Real.tan δ * (B + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hq hh1) ht0
      _ ≤ 2 * δ * (B + 1) := mul_le_mul_of_nonneg_right ht (by linarith)
  unfold finiteCurvatureDensity
  apply max_le
  · nlinarith
  · nlinarith [mul_nonneg hB hδ.1]

theorem finiteCurvatureDensity_corner_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (j : SourceIndex (dyadic n)) :
    finiteCurvatureDensity (cornerSecant U n j) (mesh n) ≤ (4 * R + 10) * mesh n := by
  have h := finiteCurvatureDensity_le_coarse (by linarith : 0 ≤ 2 * R + 3)
    (abs_cornerSecant_le_box hU hbox n j) ⟨(mesh_pos n).le, mesh_le_pi_div_four n⟩
  nlinarith

theorem IsSelectedPolygon.curvature_atom_coarse {target U : Set Plane}
    {a b coefficient R : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (j : SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      (4 * R + 10) * mesh level + middleOuterMass U (dyadic level) j +
        selectionDefect target U level coefficient j := by
  have h := hU.curvature_atom_refined hcoefficient j
  have hbound := finiteCurvatureDensity_corner_le_box hU.isCap hR hbox level j
  linarith

end AngularGrid

end AmbidextrousSofa
