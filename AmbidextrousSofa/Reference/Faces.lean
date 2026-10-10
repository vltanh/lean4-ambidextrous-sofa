module

public import AmbidextrousSofa.Reference.Niche
public import AmbidextrousSofa.Reference.Momenta
public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# Projection, top face, and confinement of the reference niche

The realized endpoint supports give the exact horizontal projection. The two
upper boundary arcs give the endpoints of the middle top face. A tangent
unit-disk comparison follows from the proved curvature bound and confines the
actual niche to that middle face interval.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

def topLeft : ℝ := 1 - 2 * A

def topRight : ℝ := 1 - 2 / 3 * A

def topInterval : Set ℝ := Icc topLeft topRight

theorem topLeft_lt_topRight : topLeft < topRight := by
  unfold topLeft topRight
  linarith [A_pos]

theorem horizontalRight_referenceHull : horizontalRight referenceHull = 1 := by
  have h := angleSupport_referenceHull_eq_f
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) from ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  simpa only [angleSupport, unitNormal, Real.cos_zero, Real.sin_zero,
    support_horizontal_right, referenceF_zero] using h

theorem horizontalLeft_referenceHull : horizontalLeft referenceHull = 1 - 8 / 3 * A := by
  have h := angleSupport_referenceHull_eq_g
    (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩)
  rw [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring] at h
  simp only [angleSupport, unitNormal, Real.cos_pi, Real.sin_pi,
    referenceG_pi_div_two] at h
  rw [support_horizontal_left isCompact_referenceHull referenceHull_nonempty] at h
  linarith

theorem horizontalProjection_referenceHull :
    horizontalProjection referenceHull = Icc (1 - 8 / 3 * A) 1 := by
  rw [horizontalProjection_eq_Icc referenceHull_nonempty isCompact_referenceHull
    convex_referenceHull, horizontalLeft_referenceHull, horizontalRight_referenceHull]

theorem horizontalLeft_referenceCap : horizontalLeft referenceCap = 1 - 8 / 3 * A := by
  unfold horizontalLeft
  rw [horizontalProjection_referenceCap]
  exact horizontalLeft_referenceHull

theorem horizontalRight_referenceCap : horizontalRight referenceCap = 1 := by
  unfold horizontalRight
  rw [horizontalProjection_referenceCap]
  exact horizontalRight_referenceHull

theorem capWidth_referenceCap : capWidth referenceCap = 8 / 3 * A := by
  unfold capWidth
  rw [horizontalLeft_referenceCap, horizontalRight_referenceCap]
  ring

theorem middleHalfInterval_referenceCap :
    middleHalfInterval (horizontalLeft referenceCap) (horizontalRight referenceCap) = topInterval := by
  rw [horizontalLeft_referenceCap, horizontalRight_referenceCap]
  unfold middleHalfInterval topInterval topLeft topRight
  congr 1 <;> ring

theorem topLeft_mem_referenceHull : (topLeft, 1) ∈ referenceHull := by
  have h := gBoundary_mem_referenceHull
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) from ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  simpa only [gBoundary_zero, topLeft] using h

theorem topRight_mem_referenceHull : (topRight, 1) ∈ referenceHull := by
  have h := fBoundary_mem_referenceHull
    (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩)
  simpa only [fBoundary_pi_div_two, topRight] using h

/-- The whole top segment consists of actual points of the reference hull. -/
theorem topFace_mem_referenceHull {x : ℝ} (hx : x ∈ topInterval) : (x, 1) ∈ referenceHull := by
  have hden : 0 < topRight - topLeft := sub_pos.mpr topLeft_lt_topRight
  let b : ℝ := (x - topLeft) / (topRight - topLeft)
  have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr hx.1) hden.le
  have hb1 : b ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith [hx.2]
  have h := convex_referenceHull topLeft_mem_referenceHull topRight_mem_referenceHull
    (sub_nonneg.mpr hb1) hb0 (show 1 - b + b = 1 by ring)
  have hpoint : (1 - b) • (topLeft, (1 : ℝ)) + b • (topRight, (1 : ℝ)) = (x, 1) := by
    apply Prod.ext
    · change (1 - b) * topLeft + b * topRight = x
      dsimp [b]
      field_simp [ne_of_gt hden]
      <;> ring
    · change (1 - b) * 1 + b * 1 = 1
      ring
  rwa [hpoint] at h

theorem capRoof_referenceCap_eq_one {x : ℝ} (hx : x ∈ topInterval) :
    capRoof referenceCap x = 1 := by
  apply le_antisymm (capRoof_le_one isDownwardCap_referenceCap.isCompact
    isDownwardCap_referenceCap.inStrip x)
  exact le_capRoof isDownwardCap_referenceCap.isCompact
    (referenceHull_subset_referenceCap (topFace_mem_referenceHull hx))

theorem referenceF_le_topRight_disk {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t ≤ 1 + topRight * Real.cos t := by
  let H : ℝ → ℝ := fun x => 1 + topRight * Real.cos x - referenceF x
  let HD : ℝ → ℝ := fun x => -topRight * Real.sin x - referenceFD x
  let HDD : ℝ → ℝ := fun x => -topRight * Real.cos x - referenceFSecond x
  have hH : Continuous H := by
    have hf := continuous_referenceF
    dsimp [H]
    fun_prop
  have hHD : Continuous HD := by
    have hf := continuous_referenceFD
    dsimp [HD]
    fun_prop
  have hderiv : ∀ x, HasDerivWithinAt H (HD x) (Ioi x) x := by
    intro x
    apply (((hasDerivAt_const x 1).add ((Real.hasDerivAt_cos x).const_mul topRight)).sub
      (hasDerivAt_referenceF x)).hasDerivWithinAt.congr_deriv
    dsimp [HD]
    ring
  have hsecond : ∀ x, HasDerivWithinAt HD (HDD x) (Ioi x) x := by
    intro x
    apply (((Real.hasDerivAt_sin x).const_mul (-topRight)).hasDerivWithinAt.sub
      (hasDerivWithinAt_referenceFD_right x)).congr_deriv
    dsimp [HDD]
    ring
  have hcurv : ∀ x ∈ Icc (0 : ℝ) (Real.pi / 2), 0 ≤ H x + HDD x := by
    intro x hx
    have hbound := referenceF_right_curvature_le_one hx
    dsimp [H, HDD]
    linarith
  have hzero : H (Real.pi / 2) = 0 := by simp [H, referenceF_pi_div_two]
  have hDzero : HD (Real.pi / 2) = 0 := by
    simp [HD, referenceFD, not_le.mpr beta_lt_pi_div_two,
      not_le.mpr lateSwitch_lt_pi_div_two, fLateD_pi_div_two, topRight] <;> ring
  have h := supportProjection_le_self hH hHD hderiv hsecond hcurv
    (show Real.pi / 2 - 0 ≤ Real.pi by linarith [Real.pi_pos])
    (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩) ht
  simp only [supportProjection, hzero, hDzero, zero_mul, zero_add] at h
  dsimp [H] at h
  linarith

theorem referenceG_le_topLeft_disk {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceG t ≤ 1 - topLeft * Real.sin t := by
  let H : ℝ → ℝ := fun x => 1 - topLeft * Real.sin x - referenceG x
  let HD : ℝ → ℝ := fun x => -topLeft * Real.cos x - referenceGD x
  let HDD : ℝ → ℝ := fun x => topLeft * Real.sin x - referenceGSecond x
  have hH : Continuous H := by
    have hg := continuous_referenceG
    dsimp [H]
    fun_prop
  have hHD : Continuous HD := by
    have hg := continuous_referenceGD
    dsimp [HD]
    fun_prop
  have hderiv : ∀ x, HasDerivWithinAt H (HD x) (Ioi x) x := by
    intro x
    apply (((hasDerivAt_const x 1).sub ((Real.hasDerivAt_sin x).const_mul topLeft)).sub
      (hasDerivAt_referenceG x)).hasDerivWithinAt.congr_deriv
    dsimp [HD]
    ring
  have hsecond : ∀ x, HasDerivWithinAt HD (HDD x) (Ioi x) x := by
    intro x
    apply (((Real.hasDerivAt_cos x).const_mul (-topLeft)).hasDerivWithinAt.sub
      (hasDerivWithinAt_referenceGD_right x)).congr_deriv
    dsimp [HDD]
    ring
  have hcurv : ∀ x ∈ Icc (0 : ℝ) (Real.pi / 2), 0 ≤ H x + HDD x := by
    intro x hx
    have hbound := referenceG_right_curvature_le_one hx
    dsimp [H, HDD]
    linarith
  have hzero : H 0 = 0 := by simp [H, referenceG_zero]
  have hDzero : HD 0 = 0 := by
    simp [HD, referenceGD, beta_pos.le, gEarlyD_zero, topLeft] <;> ring
  have h := supportProjection_le_self hH hHD hderiv hsecond hcurv
    (show Real.pi / 2 - 0 ≤ Real.pi by linarith [Real.pi_pos])
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) from ⟨le_rfl, by linarith [Real.pi_pos]⟩) ht
  simp only [supportProjection, hzero, hDzero, zero_mul, zero_add] at h
  dsimp [H] at h
  linarith

theorem referenceNiche_eq_zero_of_topRight_le {x : ℝ} (hx : topRight ≤ x) :
    referenceNiche x = 0 := by
  apply le_antisymm _ (referenceNiche_nonneg x)
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by norm_num)
  intro t ht
  calc
    cornerWall referenceHull t x ≤ firstWall referenceHull t x := min_le_left _ _
    _ ≤ 0 := by
      rw [firstWall_referenceHull ⟨ht.1.le, ht.2.le⟩]
      apply div_nonpos_of_nonpos_of_nonneg
      · have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).le
        have hmul := mul_le_mul_of_nonneg_right hx hc
        have hbound := referenceF_le_topRight_disk ⟨ht.1.le, ht.2.le⟩
        linarith
      · exact (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).le

theorem referenceNiche_eq_zero_of_le_topLeft {x : ℝ} (hx : x ≤ topLeft) : referenceNiche x = 0 := by
  apply le_antisymm _ (referenceNiche_nonneg x)
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by norm_num)
  intro t ht
  calc
    cornerWall referenceHull t x ≤ secondWall referenceHull t x := min_le_right _ _
    _ ≤ 0 := by
      rw [secondWall_referenceHull ⟨ht.1.le, ht.2.le⟩]
      apply div_nonpos_of_nonpos_of_nonneg
      · have hs := (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).le
        have hmul := mul_le_mul_of_nonneg_right hx hs
        have hbound := referenceG_le_topLeft_disk ⟨ht.1.le, ht.2.le⟩
        linarith
      · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).le

theorem referenceNiche_eq_zero_outside {x : ℝ} (hx : x ∉ topInterval) : referenceNiche x = 0 := by
  by_cases hl : x ≤ topLeft
  · exact referenceNiche_eq_zero_of_le_topLeft hl
  · have hr : topRight ≤ x := by
      by_contra hr
      exact hx ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩
    exact referenceNiche_eq_zero_of_topRight_le hr

/-- First-arc points lie on the right flank, including the right face endpoint. -/
theorem topRight_le_fBoundary_fst {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : topRight ≤ (fBoundary t).1 := by
  have h := supportProjection_le_of_ge continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right
    (fun x hx => referenceF_right_curvature_nonneg ⟨ht.1.trans hx.1, hx.2⟩)
    ht.2 ht.1 (show Real.pi / 2 - 0 ≤ Real.pi by linarith [Real.pi_pos])
  have hdot : coordDot (fBoundary (Real.pi / 2)) (unitNormal 0) ≤
      coordDot (fBoundary t) (unitNormal 0) := by
    simpa only [coordDot_fBoundary] using h
  simpa only [fBoundary_pi_div_two, coordDot, unitNormal, Real.cos_zero,
    Real.sin_zero, mul_one, mul_zero, add_zero, topRight] using hdot

/-- Companion-arc points lie on the left flank. -/
theorem gBoundary_fst_le_topLeft {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : (gBoundary t).1 ≤ topLeft := by
  have h := supportProjection_le_of_ge continuous_referenceG continuous_referenceGD
    (fun x => (hasDerivAt_referenceG x).hasDerivWithinAt)
    hasDerivWithinAt_referenceGD_right
    (fun x hx => referenceG_right_curvature_nonneg ⟨hx.1, hx.2.trans ht.2⟩)
    ht.1 (show 0 - Real.pi / 2 ≤ (0 : ℝ) by linarith [Real.pi_pos])
    (show t - (0 - Real.pi / 2) ≤ Real.pi by linarith [ht.2])
  have hdot : coordDot (gBoundary t) (unitNormal 0) ≤ coordDot (gBoundary 0) (unitNormal 0) := by
    simpa only [coordDot_gBoundary] using h
  simpa only [gBoundary_zero, coordDot, unitNormal, Real.cos_zero,
    Real.sin_zero, mul_one, mul_zero, add_zero, topLeft] using hdot

theorem referenceNiche_fBoundary {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceNiche (fBoundary t).1 = 0 :=
  referenceNiche_eq_zero_of_topRight_le (topRight_le_fBoundary_fst ht)

theorem referenceNiche_gBoundary {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceNiche (gBoundary t).1 = 0 :=
  referenceNiche_eq_zero_of_le_topLeft (gBoundary_fst_le_topLeft ht)

end AmbidextrousSofa.Reference
