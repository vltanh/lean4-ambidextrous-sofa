module

public import AmbidextrousSofa.Analysis.TiltedEndpointLeakage
public import AmbidextrousSofa.Analysis.HorizontalLeakageIntegral
public import AmbidextrousSofa.Analysis.TerminalCompanionMoment
public import AmbidextrousSofa.Analysis.OneTurnArea

@[expose] public section

/-!
# The excess moment and the actual outer niche area

The sine-weighted positive curvature excess bounds the displacement of
every first inner wall beyond the literal top endpoint. Thus the actual
niche vanishes after that endpoint plus the excess moment. Convexity on
the right wing then bounds its area by a triangle. The last result
integrates the compact quadratic excess envelope with exact rational
constants; it makes no assumption about an active wall being attained.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def firstExcessMoment (ρ : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(Real.pi / 2), max (ρ s - 1) 0 * Real.sin s

theorem firstExcessMoment_integrable {ρ : ℝ → ℝ} {K a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K) :
    IntervalIntegrable (fun s => max (ρ s - 1) 0 * Real.sin s) volume a b :=
  (intervalIntegrable_terminal_positive_excess
    (intervalIntegrable_bounded_real_density hρ hρ0 hρK a b)).mul_continuousOn
      Real.continuous_sin.continuousOn

theorem IsDownwardCap.firstWall_nonpos_after_excess_moment
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hx : b + firstExcessMoment ρ ≤ x) :
    firstWall U t x ≤ 0 := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos])
  -- The density kernel is at most `cos t` times the excess moment.
  have hkernel : (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) ≤
      Real.cos t * firstExcessMoment ρ := by
    rw [firstExcessMoment, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.integral_mono_on ht.2.le ?_
      ((firstExcessMoment_integrable hρ hρ0 hρK).const_mul _) fun s hst => ?_).trans
      (intervalIntegral.integral_mono_interval ht.1.le ht.2.le le_rfl
        (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs' => ?_)
        ((firstExcessMoment_integrable hρ hρ0 hρK).const_mul _))
    · exact ((intervalIntegrable_bounded_real_density hρ hρ0 hρK _ _).sub
        intervalIntegrable_const).continuousOn_mul (by fun_prop)
    · have hcs := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, hst.1, Real.pi_pos], hst.2⟩
      have hst' := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.2 hst.1)
        (by linarith [hst.2, ht.1, Real.pi_pos])
      rw [Real.sin_sub] at hst' ⊢
      nlinarith [mul_le_mul_of_nonneg_left (le_max_left (ρ s - 1) 0) hst',
        mul_nonneg (mul_nonneg hcs hs) (le_max_right (ρ s - 1) 0)]
    · exact mul_nonneg hc (mul_nonneg (le_max_right _ _)
        (Real.sin_nonneg_of_nonneg_of_le_pi hs'.1.le (by linarith [hs'.2, Real.pi_pos])))
  rw [hU.firstWall_eq_density_kernel_at hρ hρ0 hρK heq ht
    ((Ioo_subset_Ioo ht.1.le le_rfl).trans hsub) htop x, ← add_div]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hs

/-- A nonnegative convex tail which has already vanished at `X` is
bounded by the triangle from `(a, f a)` to `(X, 0)`, even if the requested
integration endpoint lies on either side of `X`. -/
theorem ConvexOn.integral_tail_le_triangle {f : ℝ → ℝ} {a b X : ℝ}
    (hf : ConvexOn ℝ (Ici a) f) (hc : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (hab : a ≤ b) (haX : a ≤ X) (hz : ∀ x, X ≤ x → f x = 0) :
    (∫ x in a..b, f x) ≤ (X - a) * f a / 2 := by
  have htr : (∫ x in a..X, f x) ≤ (X - a) * f a / 2 := by
    rcases haX.eq_or_lt with rfl | hlt
    · simp
    simpa [hz X le_rfl] using ConvexOn.integral_le_trapezoid
      (hf.subset (fun _ hx => hx.1) (convex_Icc a X)) hlt (hc.intervalIntegrable a X)
  have h0 : (∫ x in X..max b X, f x) = 0 := intervalIntegral.integral_zero_ae <| .of_forall
    fun x hx => hz x (by rw [uIoc_of_le (le_max_right b X)] at hx; exact hx.1.le)
  calc (∫ x in a..b, f x) ≤ ∫ x in a..max b X, f x :=
        intervalIntegral.integral_mono_interval le_rfl hab (le_max_left b X)
          (.of_forall hn) (hc.intervalIntegrable _ _)
    _ = ∫ x in a..X, f x := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a X)
          (hc.intervalIntegrable X _), h0, add_zero]
    _ ≤ (X - a) * f a / 2 := htr

theorem IsDownwardCap.right_niche_integral_le_excess_triangle
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1))
    (hC0 : 0 ≤ C) (hCb : C ≤ b)
    (hcorner : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), (attachedCorner U t).1 ≤ C) :
    (∫ x in C..(2 * C), sweptNiche U (Real.pi / 2) x) ≤
      (b - C + firstExcessMoment ρ) * sweptNiche U (Real.pi / 2) C / 2 := by
  have hM : 0 ≤ firstExcessMoment ρ := intervalIntegral.integral_nonneg (by positivity)
    fun s hs => mul_nonneg (le_max_right _ _)
      (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos]))
  refine (ConvexOn.integral_tail_le_triangle (hU.convexOn_sweptNiche_right_of_corners hcorner)
    hU.continuous_sweptNiche_pi_div_two (sweptNiche_nonneg U _) (by linarith) (by linarith)
    fun x hx => le_antisymm (sweptNiche_le_of_forall (by positivity) le_rfl fun t ht =>
      (min_le_left _ _).trans (hU.firstWall_nonpos_after_excess_moment hρ hρ0 hρK heq hsub
        htop ht hx)) (sweptNiche_nonneg _ _ _)).trans_eq (by ring)

/-- Integrate the excess envelope directly, retaining its exact moment. -/
theorem firstExcessMoment_le_short_envelope_moment
    {ρ : ℝ → ℝ} {K A h : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) (hend : A + h ≤ 11 / 15)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ s - 1 ≤ horizontalLeakageEnvelope A h s) :
    firstExcessMoment ρ ≤ tiltedLeakageMomentBound := by
  have hM : Integrable fun s => 11 / 15 * horizontalLeakageEnvelope A h s :=
    ((integrable_indicator_iff measurableSet_Icc).2 (Continuous.integrableOn_Icc
      (by unfold horizontalLeakageQuadratic; fun_prop))).const_mul _
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      max (ρ s - 1) 0 * Real.sin s ≤ 11 / 15 * horizontalLeakageEnvelope A h s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hbound] with s hs hρs
    have he := horizontalLeakageEnvelope_nonneg A h s
    refine (mul_le_mul_of_nonneg_right (max_le hρs he) (Real.sin_nonneg_of_nonneg_of_le_pi
      hs.1.le (by linarith [hs.2, Real.pi_pos]))).trans ?_
    by_cases hmem : s ∈ Icc A (A + h)
    · nlinarith [mul_le_mul_of_nonneg_left ((Real.sin_le hs.1.le).trans (hmem.2.trans hend)) he]
    · simp [horizontalLeakageEnvelope, indicator_of_notMem hmem]
  calc firstExcessMoment ρ = ∫ s in Ioo 0 (Real.pi / 2), max (ρ s - 1) 0 * Real.sin s := by
        rw [firstExcessMoment, intervalIntegral.integral_of_le (by positivity),
          integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ s in Ioo 0 (Real.pi / 2), 11 / 15 * horizontalLeakageEnvelope A h s :=
        integral_mono_ae ((firstExcessMoment_integrable (a := 0) (b := Real.pi / 2) hρ hρ0
          hρK).1.mono_set Ioo_subset_Ioc_self) hM.integrableOn hpoint
    _ ≤ ∫ s, 11 / 15 * horizontalLeakageEnvelope A h s := setIntegral_le_integral hM
        (.of_forall fun s => mul_nonneg (by norm_num) (horizontalLeakageEnvelope_nonneg A h s))
    _ = 11 / 15 * horizontalLeakageA0 h := by
        unfold horizontalLeakageEnvelope
        rw [integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_comp_sub_right (horizontalLeakageQuadratic h), sub_self,
          add_sub_cancel_left, integral_horizontalLeakageQuadratic]
    _ ≤ 11 / 15 * horizontalLeakageA0 (1 / 3) := by gcongr; exact horizontalLeakageA0_mono hh hh1
    _ = tiltedLeakageMomentBound := rfl

end AmbidextrousSofa
