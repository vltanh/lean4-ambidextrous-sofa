module

public import AmbidextrousSofa.Analysis.TerminalAngleDerivative
public import AmbidextrousSofa.Analysis.JointCapMaximum
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Integrated terminal-angle variation

The actual supporting-face endpoint lies in the cap's compact projection.
Together with the positive sine on the terminal-angle interval, this gives
a uniform bound on the pointwise right derivative. The one-sided mean
value inequality then bounds the difference quotients of the whole
partial barrier, including changes in its historical supremum.

Dominated convergence yields the derivative of its spatial integral and
of the actual cap score. At a joint maximum the resulting terminal moment
is nonnegative. Its explicit decomposition retains the positive first
moment on the full historical tie set.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem half_le_sin_terminalAngle {a : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a ≤ Real.pi / 2) :
    (1 / 2 : ℝ) ≤ Real.sin a := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ Real.pi / 6 by linarith [Real.pi_pos]) haL
    (show Real.pi / 6 ≤ a by linarith [Real.pi_pos])
  simpa only [Real.sin_pi_div_six] using h

theorem IsDownwardCap.abs_terminalFirstRightAbscissa_le {U : Set Plane}
    (hU : IsDownwardCap U) (a : ℝ) :
    |terminalFirstRightAbscissa U a| ≤ |horizontalLeft U| + |horizontalRight U| + 1 := by
  have hp : MovingSofaOptimality.vplus U a ∈ U :=
    (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody a).1
  have hx : (MovingSofaOptimality.vplus U a).1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
    rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact ⟨MovingSofaOptimality.vplus U a, hp, rfl⟩
  have habs := abs_le_endpoint_sum_of_mem_Icc hx
  unfold terminalFirstRightAbscissa
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (MovingSofaOptimality.vplus U a).1,
    le_abs_self (MovingSofaOptimality.vplus U a).1, Real.neg_one_le_cos a, Real.cos_le_one a]

theorem IsDownwardCap.norm_terminalFirstRightDerivative_le {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a ≤ Real.pi / 2) (x : ℝ) :
    ‖(x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2‖ ≤
      4 * (|x| + |horizontalLeft U| + |horizontalRight U| + 1) := by
  have hs := half_le_sin_terminalAngle ha0 haL
  have hspos : 0 < Real.sin a := by linarith
  have hsquare : (1 / 4 : ℝ) ≤ Real.sin a ^ 2 := by nlinarith
  have hB := hU.abs_terminalFirstRightAbscissa_le a
  have hnum : |x - terminalFirstRightAbscissa U a| ≤
      |x| + |horizontalLeft U| + |horizontalRight U| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le x, le_abs_self x,
      neg_abs_le (terminalFirstRightAbscissa U a),
      le_abs_self (terminalFirstRightAbscissa U a)]
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ (sq_pos_of_pos hspos)).mpr
  have hscale := mul_nonneg
    (show 0 ≤ |x| + |horizontalLeft U| + |horizontalRight U| + 1 by positivity)
    (sub_nonneg.mpr hsquare)
  nlinarith

theorem IsDownwardCap.norm_terminalBarrierRightDerivative_le {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) (x : ℝ) :
    ‖terminalBarrierRightDerivative U a x‖ ≤
      4 * (|x| + |horizontalLeft U| + |horizontalRight U| + 1) := by
  have hD := hU.norm_terminalFirstRightDerivative_le ha0 haL.le x
  unfold terminalBarrierRightDerivative
  split_ifs
  · exact hD
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hD)
    · positivity
  · simp only [norm_zero]
    positivity

theorem IsDownwardCap.continuousOn_partialBarrier_terminalAngle {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    ContinuousOn (fun a : ℝ => partialBarrier U a x)
      (Icc (Real.pi / 4) (Real.pi / 2)) := by
  have hcont : Continuous (fun a : TerminalAngle => partialBarrier U a x) :=
    continuous_partialCapBarrier.comp
      (show Continuous (fun a : TerminalAngle => ((hU.toCompactCap, a), x)) by fun_prop)
  exact continuousOn_iff_continuous_restrict.mpr hcont

/-- The mean value bound uses the right derivative at every angle before
the terminal endpoint. It therefore applies even when the historical
contact set changes inside the angular interval. -/
theorem IsDownwardCap.norm_partialBarrier_sub_le_terminalAngle {U : Set Plane}
    (hU : IsDownwardCap U) {a b : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (hab : a ≤ b) (hbL : b ≤ Real.pi / 2) (x : ℝ) :
    ‖partialBarrier U b x - partialBarrier U a x‖ ≤
      4 * (|x| + |horizontalLeft U| + |horizontalRight U| + 1) * (b - a) := by
  apply norm_image_sub_le_of_norm_deriv_right_le_segment
    ((hU.continuousOn_partialBarrier_terminalAngle x).mono
      (Icc_subset_Icc ha0 hbL))
    (fun t ht => (hU.partialBarrier_right_deriv (ha0.trans ht.1)
      (ht.2.trans_le hbL) x).Ici_of_Ioi)
    (fun t ht => hU.norm_terminalBarrierRightDerivative_le (ha0.trans ht.1)
      (ht.2.trans_le hbL) x) b ⟨hab, le_rfl⟩

theorem IsDownwardCap.norm_terminalBarrier_quotient_le_Icc {U : Set Plane}
    (hU : IsDownwardCap U) {a b l r x : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (hab : a < b) (hbL : b ≤ Real.pi / 2) (hx : x ∈ Icc l r) :
    ‖(partialBarrier U b x - partialBarrier U a x) / (b - a)‖ ≤
      4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1) := by
  have h := hU.norm_partialBarrier_sub_le_terminalAngle ha0 hab.le hbL x
  have hC : 4 * (|x| + |horizontalLeft U| + |horizontalRight U| + 1) ≤
      4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1) := by
    linarith [abs_le_endpoint_sum_of_mem_Icc hx]
  rw [norm_div, Real.norm_eq_abs (b - a), abs_of_pos (sub_pos.mpr hab)]
  exact (div_le_iff₀ (sub_pos.mpr hab)).mpr
    (h.trans (mul_le_mul_of_nonneg_right hC (sub_pos.mpr hab).le))

theorem IsDownwardCap.integrableOn_terminalBarrierRightDerivative_Icc
    {U : Set Plane} (hU : IsDownwardCap U) {a : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2) (l r : ℝ) :
    IntegrableOn (terminalBarrierRightDerivative U a) (Icc l r) := by
  let C := 4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1)
  have hConst : IntegrableOn (fun _ : ℝ => C) (Icc l r) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply Integrable.mono' hConst
    (hU.measurable_terminalBarrierRightDerivative ha0 haL).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have h := hU.norm_terminalBarrierRightDerivative_le ha0 haL x
  dsimp [C]
  linarith [abs_le_endpoint_sum_of_mem_Icc hx]

/-- Differentiation under the actual spatial integral, on an arbitrary
compact interval. The domination is derived from the supporting geometry,
not supplied as a hypothesis. -/
theorem IsDownwardCap.integral_partialBarrier_right_deriv {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) (l r : ℝ) :
    HasDerivWithinAt (fun b => ∫ x in Icc l r, partialBarrier U b x)
      (∫ x in Icc l r, terminalBarrierRightDerivative U a x) (Ioi a) a := by
  let F : ℝ → ℝ → ℝ := fun b x =>
    (partialBarrier U b x - partialBarrier U a x) / (b - a)
  let C := 4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1)
  have ha : 0 < a := by linarith [Real.pi_pos]
  have hFmeas : ∀ᶠ b in 𝓝[>] a,
      AEStronglyMeasurable (F b) (volume.restrict (Icc l r)) := by
    filter_upwards [Ioo_mem_nhdsGT haL] with b hb
    exact (((measurable_partialBarrier hU.isCompact (ha.trans hb.1) hb.2.le).sub
      (measurable_partialBarrier hU.isCompact ha haL.le)).div_const (b - a)).aestronglyMeasurable
  have hbound : ∀ᶠ b in 𝓝[>] a,
      ∀ᵐ x ∂volume.restrict (Icc l r), ‖F b x‖ ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT haL] with b hb
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hU.norm_terminalBarrier_quotient_le_Icc ha0 hb.1 hb.2.le hx
  have hConst : Integrable (fun _ : ℝ => C) (volume.restrict (Icc l r)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hlim : ∀ᵐ x ∂volume.restrict (Icc l r),
      Tendsto (fun b => F b x) (𝓝[>] a) (𝓝 (terminalBarrierRightDerivative U a x)) :=
    Eventually.of_forall (fun x => hasDerivWithinAt_right_iff_tendsto_quotient.mp
      (hU.partialBarrier_right_deriv ha0 haL x))
  have hIntegral := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => C) hFmeas hbound hConst hlim
  apply hasDerivWithinAt_right_iff_tendsto_quotient.mpr
  apply hIntegral.congr'
  filter_upwards [Ioo_mem_nhdsGT haL] with b hb
  dsimp only [F]
  rw [integral_div, integral_sub
    (integrableOn_partialBarrier_Icc hU.isCompact (ha.trans hb.1) hb.2.le l r)
    (integrableOn_partialBarrier_Icc hU.isCompact ha haL.le l r)]

theorem IsDownwardCap.capScore_right_deriv_terminalAngle {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) :
    HasDerivWithinAt (capScore U)
      (-(∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        terminalBarrierRightDerivative U a x)) (Ioi a) a := by
  have h := (hU.integral_partialBarrier_right_deriv ha0 haL
    (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)).const_sub
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x)
  change HasDerivWithinAt (fun b =>
    (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
      middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
    ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), partialBarrier U b x)
    (-(∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      terminalBarrierRightDerivative U a x)) (Ioi a) a at h
  apply h.congr_of_eventuallyEq
  · exact Eventually.of_forall (fun b => capScore_eq_integrals U b)
  · exact capScore_eq_integrals U a

/-- A genuine joint maximizer cannot have positive right derivative of
its score at a proper terminal angle. -/
theorem IsJointCapMaximizer.terminal_variation_integral_nonneg
    {U : Set Plane} {a : ℝ} (hU : IsJointCapMaximizer U a)
    (haL : a < Real.pi / 2) :
    0 ≤ ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      terminalBarrierRightDerivative U a x := by
  have hlim := hasDerivWithinAt_right_iff_tendsto_quotient.mp
    (hU.isCap.capScore_right_deriv_terminalAngle hU.angle_mem.1 haL)
  have hnonpos : -(∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      terminalBarrierRightDerivative U a x) ≤ 0 := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT haL] with b hb
    have hscore := hU.score_le hU.isCap
      ⟨hU.angle_mem.1.trans hb.1.le, hb.2.le⟩
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hscore) (sub_pos.mpr hb.1).le
  linarith

/-- Strict activity of the terminal first wall over the old swept family. -/
def terminalStrictRegion (U : Set Plane) (a : ℝ) : Set ℝ :=
  {x | sweptNiche U a x < firstWall U a x}

/-- The full historical tie set, without any null-set convention. -/
def terminalHistoricalTie (U : Set Plane) (a : ℝ) : Set ℝ :=
  {x | firstWall U a x = sweptNiche U a x}

theorem IsDownwardCap.measurableSet_terminalStrictRegion {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a ≤ Real.pi / 2) : MeasurableSet (terminalStrictRegion U a) :=
  measurableSet_lt (measurable_sweptNiche hU.isCompact
    (by linarith [Real.pi_pos]) haL) (continuous_firstWall U a).measurable

theorem IsDownwardCap.measurableSet_terminalHistoricalTie {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a ≤ Real.pi / 2) : MeasurableSet (terminalHistoricalTie U a) :=
  measurableSet_eq_fun (continuous_firstWall U a).measurable
    (measurable_sweptNiche hU.isCompact (by linarith [Real.pi_pos]) haL)

theorem terminalBarrierRightDerivative_eq_moment_indicators
    (U : Set Plane) (a x : ℝ) :
    terminalBarrierRightDerivative U a x =
      ((terminalStrictRegion U a).indicator
          (fun y => y - terminalFirstRightAbscissa U a) x +
        (terminalHistoricalTie U a).indicator
          (fun y => max (y - terminalFirstRightAbscissa U a) 0) x) / Real.sin a ^ 2 := by
  by_cases hstrict : sweptNiche U a x < firstWall U a x
  · have htie : firstWall U a x ≠ sweptNiche U a x := ne_of_gt hstrict
    simp [terminalBarrierRightDerivative, terminalStrictRegion, terminalHistoricalTie,
      hstrict, htie]
  · by_cases htie : firstWall U a x = sweptNiche U a x
    · simp only [terminalBarrierRightDerivative, if_neg hstrict, if_pos htie,
        terminalStrictRegion, terminalHistoricalTie, mem_setOf_eq, indicator_of_notMem hstrict,
        indicator_of_mem htie, zero_add]
      simpa only [zero_div] using
        max_div_div_right (sq_nonneg (Real.sin a)) (x - terminalFirstRightAbscissa U a) 0
    · simp [terminalBarrierRightDerivative, terminalStrictRegion, terminalHistoricalTie,
        hstrict, htie]

/-- The derivative integral is the strict-region first moment plus the
positive historical-tie moment, divided by the squared terminal sine. -/
theorem IsDownwardCap.integral_terminalBarrierRightDerivative_eq_moments
    {U : Set Plane} (hU : IsDownwardCap U) {a : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a ≤ Real.pi / 2) (l r : ℝ) :
    (∫ x in Icc l r, terminalBarrierRightDerivative U a x) =
      ((∫ x in Icc l r ∩ terminalStrictRegion U a, x - terminalFirstRightAbscissa U a) +
        ∫ x in Icc l r ∩ terminalHistoricalTie U a,
          max (x - terminalFirstRightAbscissa U a) 0) / Real.sin a ^ 2 := by
  have hE := hU.measurableSet_terminalStrictRegion ha0 haL
  have hH := hU.measurableSet_terminalHistoricalTie ha0 haL
  have hlin : IntegrableOn (fun x : ℝ => x - terminalFirstRightAbscissa U a) (Icc l r) :=
    (show Continuous (fun x : ℝ => x - terminalFirstRightAbscissa U a) by fun_prop)
      .continuousOn.integrableOn_Icc
  have hpos : IntegrableOn (fun x : ℝ => max (x - terminalFirstRightAbscissa U a) 0)
      (Icc l r) :=
    (show Continuous (fun x : ℝ => max (x - terminalFirstRightAbscissa U a) 0) by fun_prop)
      .continuousOn.integrableOn_Icc
  simp_rw [terminalBarrierRightDerivative_eq_moment_indicators]
  rw [integral_div, integral_add (hlin.indicator hE) (hpos.indicator hH),
    setIntegral_indicator hE, setIntegral_indicator hH]

/-- The terminal-angle necessary condition, in the exact two-moment form.
The historical-tie term is present even when that set has positive measure. -/
theorem IsJointCapMaximizer.terminal_variation_moments_nonneg
    {U : Set Plane} {a : ℝ} (hU : IsJointCapMaximizer U a)
    (haL : a < Real.pi / 2) :
    0 ≤ (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        terminalStrictRegion U a, x - terminalFirstRightAbscissa U a) +
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        terminalHistoricalTie U a, max (x - terminalFirstRightAbscissa U a) 0 := by
  have h := hU.terminal_variation_integral_nonneg haL
  rw [middleHalfInterval,
    hU.isCap.integral_terminalBarrierRightDerivative_eq_moments
      hU.angle_mem.1 haL.le] at h
  have hs : 0 < Real.sin a := by
    linarith [half_le_sin_terminalAngle hU.angle_mem.1 haL.le]
  simpa only [zero_mul] using (le_div_iff₀ (sq_pos_of_pos hs)).mp h

end AmbidextrousSofa
