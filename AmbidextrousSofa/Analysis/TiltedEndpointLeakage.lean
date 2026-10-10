import AmbidextrousSofa.Analysis.HorizontalEndpointKernel
import AmbidextrousSofa.Analysis.WallVisibility
import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

/-!
# Endpoint leakage after actual first-wing excess has stopped

The support kernel is based at the literal right endpoint of the top
face. Before `arccos C`, the first wall at the middle endpoint increases:
the actual support point has abscissa at most `2C`. Afterwards the kernel
is nonpositive when the actual curvature density is at most one. This
proves the endpoint estimate without selecting an attained active angle.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.firstWall_eq_density_kernel_at
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hsub : Ioo t (Real.pi / 2) ⊆ S)
    (htop : Imported.vminus U (Real.pi / 2) = (b, 1)) (x : ℝ) :
    firstWall U t x = (b - x) * Real.cos t / Real.sin t +
      (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) / Real.sin t := by
  have hkernel := hU.firstWall_eq_horizontal_density_kernel hρ hρ0 hρK heq ht hsub htop
  have hspace : firstWall U t x = (b - x) * Real.cos t / Real.sin t + firstWall U t b := by
    unfold firstWall
    ring
  rw [hspace, hkernel]

theorem IsDownwardCap.hasDerivAt_firstWall_of_open_first_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x)
      ((x - (firstTangency U t).1) / Real.sin t ^ 2) t := by
  apply hU.hasDerivAt_firstWall_angle_of_density hρ hρ0 hρK heq
    (a := t / 2) (b := (t + Real.pi / 2) / 2)
  · intro s hs
    apply hsub
    constructor <;> linarith only [ht.1, ht.2, hs.1, hs.2]
  · constructor <;> linarith only [ht.1, ht.2]
  · exact (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith only [ht.2, Real.pi_pos])).ne'

theorem IsDownwardCap.firstWall_le_at_arccos_of_first_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (hright : horizontalRight U = 2 * C) (hC0 : 0 < C) (hC1 : C < 1)
    (ht0 : 0 < t) (htA : t ≤ Real.arccos C) :
    firstWall U t C ≤ firstWall U (Real.arccos C) C := by
  have hAL : Real.arccos C < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hC0
  have hcosA : Real.cos (Real.arccos C) = C :=
    Real.cos_arccos (by linarith only [hC0]) hC1.le
  apply endpoint_le_of_hasDerivAt_nonneg htA
    (fun s hs => hU.hasDerivAt_firstWall_of_open_first_density hρ hρ0 hρK heq hsub
      ⟨ht0.trans_le hs.1, hs.2.trans_lt hAL⟩ C)
  intro s hs
  apply div_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  have hcos : C ≤ Real.cos s := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (ht0.le.trans hs.1.le)
      (Real.arccos_le_pi C) hs.2.le
    rwa [hcosA] at h
  have hpoint := hU.fst_mem_Icc (Imported.vplus_mem_edge hU.imported_isConvexBody s).1
  rw [hright] at hpoint
  rw [firstTangency_eq_vplus_sub_unitNormal]
  change (Imported.vplus U s).1 - Real.cos s ≤ C
  linarith only [hpoint.2, hcos]

theorem sine_kernel_integral_nonpos_of_unit_tail
    {ρ : ℝ → ℝ} {K t A : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hAt : A ≤ t)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo A (Real.pi / 2)), ρ s ≤ 1) :
    (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) ≤ 0 := by
  have hi : IntervalIntegrable (fun s => Real.sin (s - t) * (ρ s - 1))
      volume t (Real.pi / 2) :=
    ((intervalIntegrable_bounded_real_density hρ hρ0 hρK _ _).sub
      intervalIntegrable_const).continuousOn_mul
        ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousOn)
  have hbound := intervalIntegral.integral_mono_ae_restrict ht.2.le hi
    (intervalIntegrable_const (c := (0 : ℝ))) (show ∀ᵐ s ∂volume.restrict
      (Icc t (Real.pi / 2)), Real.sin (s - t) * (ρ s - 1) ≤ (0 : ℝ) from by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo,
          ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hAt le_rfl) hunit]
          with s hs hu
        exact mul_nonpos_of_nonneg_of_nonpos
          (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hs.1.le)
            (by linarith only [ht.1, hs.2, Real.pi_pos])) (sub_nonpos.mpr hu))
  simpa only [intervalIntegral.integral_zero] using hbound

theorem cotangent_le_at_arccos {C t : ℝ}
    (hC0 : 0 < C) (hC1 : C < 1)
    (ht0 : Real.arccos C ≤ t) (htL : t < Real.pi / 2) :
    Real.cos t / Real.sin t ≤ C / Real.sqrt (1 - C ^ 2) := by
  have hA0 : 0 < Real.arccos C := Real.arccos_pos.mpr hC1
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (hA0.trans_le ht0)
    (by linarith only [htL, Real.pi_pos])
  have hrad : 0 < 1 - C ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hC1) (show 0 < 1 + C by linarith only [hC0])]
  have hroot : 0 < Real.sqrt (1 - C ^ 2) := Real.sqrt_pos.mpr hrad
  have hcos : Real.cos t ≤ C := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hA0.le
      (by linarith only [htL, Real.pi_pos]) ht0
    rwa [Real.cos_arccos (by linarith only [hC0]) hC1.le] at h
  have hsin : Real.sqrt (1 - C ^ 2) ≤ Real.sin t := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ Real.arccos C by linarith only [hA0, Real.pi_pos]) htL.le ht0
    rwa [Real.sin_arccos] at h
  apply (div_le_div_iff₀ hs hroot).mpr
  exact (mul_le_mul_of_nonneg_right hcos hroot.le).trans
    (mul_le_mul_of_nonneg_left hsin hC0.le)

/-- The bound is for the actual swept niche at the middle endpoint.
Every early first wall is compared with the wall at `arccos C`; no
attained-angle or source-occupation hypothesis is added. -/
theorem IsDownwardCap.middle_niche_le_top_overhang_of_unit_tail
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (hright : horizontalRight U = 2 * C) (hC0 : 0 < C) (hC1 : C < 1)
    (hCb : C ≤ b) (htop : Imported.vminus U (Real.pi / 2) = (b, 1))
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (Real.arccos C) (Real.pi / 2)), ρ s ≤ 1) :
    sweptNiche U (Real.pi / 2) C ≤ (b - C) * C / Real.sqrt (1 - C ^ 2) := by
  have hA0 : 0 < Real.arccos C := Real.arccos_pos.mpr hC1
  have hAL : Real.arccos C < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hC0
  have hT0 : 0 ≤ b - C := sub_nonneg.mpr hCb
  have hlate (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hAt : Real.arccos C ≤ t) :
      firstWall U t C ≤ (b - C) * C / Real.sqrt (1 - C ^ 2) := by
    have hkernel := hU.firstWall_eq_density_kernel_at hρ hρ0 hρK heq ht
      ((Ioo_subset_Ioo ht.1.le le_rfl).trans hsub) htop C
    have hnonpos := sine_kernel_integral_nonpos_of_unit_tail hρ hρ0 hρK ht hAt hunit
    have hs : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith only [ht.2, Real.pi_pos])).le
    have hdiv := div_nonpos_of_nonpos_of_nonneg hnonpos hs
    have hcot := mul_le_mul_of_nonneg_left (cotangent_le_at_arccos hC0 hC1 hAt ht.2) hT0
    rw [hkernel]
    simpa only [mul_div_assoc] using (add_le_of_nonpos_right hdiv).trans hcot
  apply sweptNiche_le_of_forall (by linarith only [Real.pi_pos])
    (div_nonneg (mul_nonneg hT0 hC0.le) (Real.sqrt_nonneg _))
  intro t ht
  apply (min_le_left (firstWall U t C) (secondWall U t C)).trans
  by_cases hAt : Real.arccos C ≤ t
  · exact hlate t ht hAt
  · exact (hU.firstWall_le_at_arccos_of_first_density hρ hρ0 hρK heq hsub hright hC0 hC1
      ht.1 (le_of_not_ge hAt)).trans (hlate (Real.arccos C) ⟨hA0, hAL⟩ le_rfl)

theorem IsDownwardCap.middle_niche_le_top_overhang_of_late_unit
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (hright : horizontalRight U = 2 * C) (hC0 : 0 < C) (hC1 : C ≤ 37 / 50)
    (hCb : C ≤ b) (htop : Imported.vminus U (Real.pi / 2) = (b, 1))
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (11 / 15 : ℝ) (Real.pi / 2)), ρ s ≤ 1) :
    sweptNiche U (Real.pi / 2) C ≤ (b - C) * C / Real.sqrt (1 - C ^ 2) :=
  hU.middle_niche_le_top_overhang_of_unit_tail hρ hρ0 hρK heq hsub hright hC0
    (by linarith only [hC1]) hCb htop
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo
      (Analysis.eleven_fifteenths_lt_arccos_of_le (by linarith only [hC0]) hC1).le le_rfl) hunit)

end AmbidextrousSofa
