import AmbidextrousSofa.Analysis.TiltedCapExclusion
import AmbidextrousSofa.Analysis.CanonicalTiltParameters
import AmbidextrousSofa.Analysis.FullCapRecovery

/-!
# Full-cap rigidity for each prescribed maximum

The actual positive-tilt exclusion forces a centered affine middle to
have nonpositive slope. Applying it to the horizontal reflection forces
the slope to vanish. Translation gives the same statement for a
prescribed uncentered cap. Its literal middle-chord and height
canonicalization is therefore horizontal, and the proved inverse
canonicalization recovers the original set as a reference translate.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.centered_affine_middle_slope_nonpos
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : m ≤ 0 := by
  by_contra hnot
  exact hU.false_of_positive_tilt hl hr hheight (lt_of_not_ge hnot) haffine

theorem IsFullCapMaximizer.centered_affine_middle_slope_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : m = 0 := by
  have hm : m ≤ 0 := hU.centered_affine_middle_slope_nonpos hl hr hheight haffine
  have hV := hU.horizontalMirror
  have hVl : horizontalLeft (horizontalMirror U) = -2 * C := by
    rw [horizontalLeft_horizontalMirror hU.isCap, hr]
    ring
  have hVr : horizontalRight (horizontalMirror U) = 2 * C := by
    rw [horizontalRight_horizontalMirror hU.isCap, hl]
    ring
  have hVheight : capHeight (horizontalMirror U) = 1 := by
    rw [capHeight_horizontalMirror, hheight]
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have hVmid : middleHalfInterval (horizontalLeft (horizontalMirror U))
      (horizontalRight (horizontalMirror U)) = Icc (-C) C := by
    rw [middleHalfInterval, hVl, hVr]
    congr 1 <;> ring
  have hVaffine : ∀ x ∈ middleHalfInterval
      (horizontalLeft (horizontalMirror U)) (horizontalRight (horizontalMirror U)),
      capRoof (horizontalMirror U) x = (-m) * x + c := by
    intro x hx
    rw [hVmid] at hx
    have hxU : -x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
      rw [hmid]
      constructor <;> linarith only [hx.1, hx.2]
    rw [capRoof_horizontalMirror, haffine (-x) hxU]
    ring
  have hneg : -m ≤ 0 :=
    hV.centered_affine_middle_slope_nonpos hVl hVr hVheight hVaffine
  exact le_antisymm hm (by linarith only [hneg])

/-- The slope belongs to the prescribed affine middle of this actual
maximum; no replacement of the original cap is needed here. -/
theorem IsFullCapMaximizer.affine_middle_slope_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : m = 0 := by
  let a := -(horizontalLeft U + horizontalRight U) / 2
  let C := capWidth U / 4
  have hV := hU.centeredCap
  have hl : horizontalLeft (centeredCap U) = -2 * C := by
    rw [horizontalLeft_centeredCap hU.isCap]
    dsimp only [C]
    ring
  have hr : horizontalRight (centeredCap U) = 2 * C := by
    rw [horizontalRight_centeredCap hU.isCap]
    dsimp only [C]
    ring
  have hVheight : capHeight (centeredCap U) = 1 := by
    rw [capHeight_centeredCap hU.isCap, hheight]
  have hVaffine : ∀ x ∈ middleHalfInterval (horizontalLeft (centeredCap U))
      (horizontalRight (centeredCap U)), capRoof (centeredCap U) x = m * x + (c - m * a) :=
    hU.isCap.affine_middle_horizontalTranslate haffine a
  exact hV.centered_affine_middle_slope_eq_zero hl hr hVheight hVaffine

theorem IsFullCapMaximizer.affine_middle_eq_one
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1 := by
  have hm : m = 0 := hU.affine_middle_slope_eq_zero hheight haffine
  have hright := hU.middle_right_eq_one_of_affine_nonneg hheight (by rw [hm]) haffine
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hb : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ∈
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
    change horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ∧
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
    exact ⟨by linarith only [hlr], le_rfl⟩
  rw [haffine _ hb, hm, zero_mul, zero_add] at hright
  intro x hx
  rw [haffine x hx, hm, zero_mul, zero_add, hright]

theorem IsFullCapMaximizer.fullCanonicalCap_middle_eq_one
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    ∀ x ∈ middleHalfInterval (horizontalLeft (fullCanonicalCap U))
      (horizontalRight (fullCanonicalCap U)), capRoof (fullCanonicalCap U) x = 1 := by
  have hwidth : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  have hdata := hU.isCap.fullCanonicalCap_data hwidth
  obtain ⟨m, c, haffine⟩ := hdata.2.2.2
  exact hU.fullCanonicalCap.affine_middle_eq_one hdata.2.2.1 haffine

/-- Classification of every original full maximum, before middle or
height replacement. The translation is the only remaining freedom. -/
theorem IsFullCapMaximizer.eq_reference_translate
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    ∃ b : ℝ, U = horizontalTranslate Reference.referenceCap b :=
  hU.eq_reference_translate_of_fullCanonicalCap_horizontal hU.fullCanonicalCap_middle_eq_one

theorem IsFullCapMaximizer.capScore_eq_half_M
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    capScore U (Real.pi / 2) = M / 2 := by
  obtain ⟨b, hb⟩ := hU.eq_reference_translate
  rw [hb, capScore_horizontalTranslate Reference.isDownwardCap_referenceCap,
    Reference.capScore_referenceCap]

end AmbidextrousSofa
