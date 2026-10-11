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

Dominated convergence yields the derivative of its spatial integral. At a
joint maximum the resulting terminal moment is nonnegative.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.norm_terminalBarrierRightDerivative_le {U : Set Plane}
    (hU : IsDownwardCap U) {a l r x : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) (hx : x ∈ Icc l r) :
    ‖terminalBarrierRightDerivative U a x‖ ≤
      4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1) := by
  have hs : 1 / 2 ≤ Real.sin a := by
    simpa using Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6)
      (by linarith [Real.pi_pos]) haL.le (by linarith [Real.pi_pos])
  have hp : (MovingSofaOptimality.vplus U a).1 ∈ Icc (horizontalLeft U) (horizontalRight U) :=
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex ▸
      ⟨_, (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody a).1, rfl⟩
  obtain ⟨h1, h1'⟩ := abs_le.mp (abs_le_endpoint_sum_of_mem_Icc hx)
  obtain ⟨h2, h2'⟩ := abs_le.mp (abs_le_endpoint_sum_of_mem_Icc hp)
  have hD : |(x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2| ≤
      4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1) := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (Real.sin a)), div_le_iff₀ (by positivity), abs_le,
      terminalFirstRightAbscissa]
    have := mul_le_mul_of_nonneg_left (show 1 / 4 ≤ Real.sin a ^ 2 by nlinarith)
      (by positivity : 0 ≤ |l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1)
    constructor <;> linarith [Real.neg_one_le_cos a, Real.cos_le_one a]
  rw [terminalBarrierRightDerivative, Real.norm_eq_abs]
  split_ifs
  · exact hD
  · exact abs_max_le_max_abs_abs.trans (max_le hD (by simp; positivity))
  · simp; positivity

/-- The mean value bound uses the right derivative at every angle before
the terminal endpoint. It therefore applies even when the historical
contact set changes inside the angular interval. -/
theorem IsDownwardCap.norm_partialBarrier_sub_le_terminalAngle {U : Set Plane}
    (hU : IsDownwardCap U) {a b l r x : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (hab : a ≤ b) (hbL : b ≤ Real.pi / 2) (hx : x ∈ Icc l r) :
    ‖partialBarrier U b x - partialBarrier U a x‖ ≤
      4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1) * (b - a) := by
  have hcont : Continuous (fun t : TerminalAngle => partialBarrier U t x) := by
    simpa only [Function.comp_def, IsDownwardCap.toCompactCap_carrier] using
      continuous_partialCapBarrier.comp
        (show Continuous (fun t : TerminalAngle => ((hU.toCompactCap, t), x)) by fun_prop)
  exact norm_image_sub_le_of_norm_deriv_right_le_segment
    ((continuousOn_iff_continuous_domRestrict.mpr hcont).mono (Icc_subset_Icc ha0 hbL))
    (fun t ht => (hU.partialBarrier_right_deriv (ha0.trans ht.1)
      (ht.2.trans_le hbL) x).Ici_of_Ioi)
    (fun t ht => hU.norm_terminalBarrierRightDerivative_le (ha0.trans ht.1)
      (ht.2.trans_le hbL) hx) b ⟨hab, le_rfl⟩

theorem IsDownwardCap.integrableOn_terminalBarrierRightDerivative_Icc
    {U : Set Plane} (hU : IsDownwardCap U) {a : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2) (l r : ℝ) :
    IntegrableOn (terminalBarrierRightDerivative U a) (Icc l r) :=
  (integrable_const _).mono'
    (hU.measurable_terminalBarrierRightDerivative ha0 haL).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Icc).mono fun _ hx =>
      hU.norm_terminalBarrierRightDerivative_le ha0 haL hx)

/-- Differentiation under the actual spatial integral, on an arbitrary
compact interval. The domination is derived from the supporting geometry,
not supplied as a hypothesis. -/
theorem IsDownwardCap.integral_partialBarrier_right_deriv {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) (l r : ℝ) :
    HasDerivWithinAt (fun b => ∫ x in Icc l r, partialBarrier U b x)
      (∫ x in Icc l r, terminalBarrierRightDerivative U a x) (Ioi a) a := by
  have ha : 0 < a := by linarith [Real.pi_pos]
  rw [hasDerivWithinAt_right_iff_tendsto_quotient]
  refine (tendsto_integral_filter_of_dominated_convergence
    (fun _ => 4 * (|l| + |r| + |horizontalLeft U| + |horizontalRight U| + 1)) ?_ ?_
    (integrable_const _) (ae_of_all _ fun x => hasDerivWithinAt_right_iff_tendsto_quotient.mp
      (hU.partialBarrier_right_deriv ha0 haL x))).congr' ?_ <;>
    filter_upwards [Ioo_mem_nhdsGT haL] with b hb
  · exact (((measurable_partialBarrier hU.isCompact (ha.trans hb.1) hb.2.le).sub
      (measurable_partialBarrier hU.isCompact ha haL.le)).div_const _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_div, Real.norm_of_nonneg (sub_pos.2 hb.1).le, div_le_iff₀ (sub_pos.2 hb.1)]
    exact hU.norm_partialBarrier_sub_le_terminalAngle ha0 hb.1.le hb.2.le hx
  · rw [integral_div, integral_sub
      (integrableOn_partialBarrier_Icc hU.isCompact (ha.trans hb.1) hb.2.le l r)
      (integrableOn_partialBarrier_Icc hU.isCompact ha haL.le l r)]

/-- A genuine joint maximizer cannot have positive right derivative of
its score at a proper terminal angle. -/
theorem IsJointCapMaximizer.terminal_variation_integral_nonneg
    {U : Set Plane} {a : ℝ} (hU : IsJointCapMaximizer U a)
    (haL : a < Real.pi / 2) :
    0 ≤ ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      terminalBarrierRightDerivative U a x := by
  rw [middleHalfInterval]
  refine ge_of_tendsto (hasDerivWithinAt_right_iff_tendsto_quotient.mp
    (hU.isCap.integral_partialBarrier_right_deriv hU.angle_mem.1 haL _ _)) ?_
  filter_upwards [Ioo_mem_nhdsGT haL] with b hb
  have h := hU.score_le hU.isCap ⟨hU.angle_mem.1.trans hb.1.le, hb.2.le⟩
  rw [capScore_eq_integrals, capScore_eq_integrals, middleHalfInterval] at h
  exact div_nonneg (by linarith) (sub_pos.mpr hb.1).le

/-- Strict activity of the terminal first wall over the old swept family. -/
def terminalStrictRegion (U : Set Plane) (a : ℝ) : Set ℝ :=
  {x | sweptNiche U a x < firstWall U a x}

end AmbidextrousSofa
