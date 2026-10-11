module

public import AmbidextrousSofa.Analysis.HorizontalEndpointKernel
public import AmbidextrousSofa.Analysis.WallVisibility
public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

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
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1)) (x : ℝ) :
    firstWall U t x = (b - x) * Real.cos t / Real.sin t +
      (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) / Real.sin t := by
  rw [← hU.firstWall_eq_horizontal_density_kernel hρ hρ0 hρK heq ht hsub htop]
  unfold firstWall
  ring

theorem IsDownwardCap.hasDerivAt_firstWall_of_open_first_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x)
      ((x - (firstTangency U t).1) / Real.sin t ^ 2) t :=
  hU.hasDerivAt_firstWall_angle_of_density hρ hρ0 hρK heq (a := t / 2) (b := (t + Real.pi / 2) / 2)
    (fun s hs => hsub ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
    (sin_cos_pos_of_mem_quarter ht).1.ne' x

theorem cotangent_le_at_arccos {C t x : ℝ} (hx : 0 ≤ x)
    (hC0 : 0 < C) (hC1 : C < 1)
    (ht0 : Real.arccos C ≤ t) (htL : t < Real.pi / 2) :
    x * Real.cos t / Real.sin t ≤ x * C / Real.sqrt (1 - C ^ 2) := by
  have hA0 : 0 < Real.arccos C := Real.arccos_pos.mpr hC1
  have hs : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (hA0.trans_le ht0) (by linarith [Real.pi_pos])
  have hroot : 0 < Real.sqrt (1 - C ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hcos : Real.cos t ≤ C := by
    simpa [Real.cos_arccos (by linarith : (-1 : ℝ) ≤ C) hC1.le] using
      Real.cos_le_cos_of_nonneg_of_le_pi hA0.le (by linarith [Real.pi_pos]) ht0
  have hsin : Real.sqrt (1 - C ^ 2) ≤ Real.sin t := by
    simpa [Real.sin_arccos] using Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) htL.le ht0
  rw [div_le_div_iff₀ hs hroot, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hcos hsin hroot.le hC0.le) hx

/-- The bound is for the actual swept niche at the middle endpoint, once the first-wing
curvature is at most one after `11/15 < arccos C`. Every early first wall is compared with the
wall at `arccos C`; no attained-angle or source-occupation hypothesis is added. -/
theorem IsDownwardCap.middle_niche_le_top_overhang_of_late_unit
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (hright : horizontalRight U = 2 * C) (hC0 : 0 < C) (hC1 : C ≤ 37 / 50)
    (hCb : C ≤ b) (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1))
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (11 / 15 : ℝ) (Real.pi / 2)), ρ s ≤ 1) :
    sweptNiche U (Real.pi / 2) C ≤ (b - C) * C / Real.sqrt (1 - C ^ 2) := by
  replace hunit := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo
    (Analysis.eleven_fifteenths_lt_arccos_of_le (by linarith only [hC0]) hC1).le le_rfl) hunit
  replace hC1 : C < 1 := by linarith only [hC1]
  have hA0 : 0 < Real.arccos C := Real.arccos_pos.mpr hC1
  have hAL : Real.arccos C < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hC0
  have hT0 : 0 ≤ b - C := sub_nonneg.mpr hCb
  -- After `arccos C` the sine kernel of `ρ - 1` is nonpositive.
  have hlate (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hAt : Real.arccos C ≤ t) :
      firstWall U t C ≤ (b - C) * C / Real.sqrt (1 - C ^ 2) := by
    have hint := intervalIntegral.integral_nonneg_of_ae_restrict (μ := volume) ht.2.le
      (f := fun s => -(Real.sin (s - t) * (ρ s - 1))) (by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo,
          ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hAt le_rfl) hunit] with s hs hu
        exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hs.1]) (by linarith [ht.1, hs.2])) (by linarith)))
    rw [intervalIntegral.integral_neg] at hint
    rw [hU.firstWall_eq_density_kernel_at hρ hρ0 hρK heq ht
      ((Ioo_subset_Ioo ht.1.le le_rfl).trans hsub) htop C]
    exact add_le_of_le_of_nonpos (cotangent_le_at_arccos hT0 hC0 hC1 hAt ht.2)
      (div_nonpos_of_nonpos_of_nonneg (by linarith)
        (sin_cos_pos_of_mem_quarter ht).1.le)
  refine sweptNiche_le_of_forall (by positivity)
    (div_nonneg (mul_nonneg hT0 hC0.le) (Real.sqrt_nonneg _)) fun t ht => ?_
  refine (min_le_left (firstWall U t C) (secondWall U t C)).trans ?_
  rcases le_or_gt (Real.arccos C) t with hAt | hAt
  · exact hlate t ht hAt
  -- Before `arccos C` the first wall at `C` increases, since the actual support point has
  -- abscissa at most `2 * C`.
  refine le_trans ?_ (hlate _ ⟨hA0, hAL⟩ le_rfl)
  refine endpoint_le_of_hasDerivAt_nonneg hAt.le (fun s hs =>
    hU.hasDerivAt_firstWall_of_open_first_density hρ hρ0 hρK heq hsub
      ⟨ht.1.trans_le hs.1, hs.2.trans_lt hAL⟩ C) fun s hs =>
    div_nonneg (sub_nonneg.2 ?_) (sq_nonneg _)
  have hcos : C ≤ Real.cos s := by
    simpa [Real.cos_arccos (by linarith : (-1 : ℝ) ≤ C) hC1.le] using
      Real.cos_le_cos_of_nonneg_of_le_pi (ht.1.le.trans hs.1.le) (Real.arccos_le_pi C) hs.2.le
  have hpoint := (hU.fst_mem_Icc (MovingSofaOptimality.vplus_mem_edge
    hU.imported_isConvexBody s).1).2
  rw [firstTangency_eq_vplus_sub_unitNormal]
  change (MovingSofaOptimality.vplus U s).1 - Real.cos s ≤ C
  linarith

end AmbidextrousSofa
