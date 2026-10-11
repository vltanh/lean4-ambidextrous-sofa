module

public import AmbidextrousSofa.Analysis.TerminalSupportTails

@[expose] public section

/-!
# Same-cap completion of the negative-tilt alternatives

The exact missing first supports of a negative affine middle use its two
actual endpoints. Their first walls are dominated by the old terminal
wall or by zero whenever the middle normal has already been visited, or
the lower middle endpoint is at most the terminal sine.

This compares the full and partial scalar objectives on the same cap:
completion of a joint maximizer produces another joint maximizer at the
full angle, without presupposing the global full-cap value bound.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The first wall of a fixed support point decreases past `a` whenever
its horizontal distance is at least `cos a`. This direct circle identity
also covers the endpoint `t = π/2`. -/
theorem fixedPoint_firstWall_le_initial {H z a t : ℝ}
    (ha0 : 0 < a) (hat : a ≤ t) (htL : t ≤ Real.pi / 2)
    (hz : Real.cos a ≤ z) :
    H + (z * Real.cos t - 1) / Real.sin t ≤
      H + (z * Real.cos a - 1) / Real.sin a := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hst : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (ha0.trans_le hat) (by linarith [Real.pi_pos])
  have hcross := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hat) (by linarith [Real.pi_pos])
  have hdot := Real.cos_le_one (t - a)
  rw [Real.sin_sub] at hcross
  rw [Real.cos_sub] at hdot
  rw [add_le_add_iff_left, div_le_div_iff₀ hst hsa]
  linarith [mul_nonneg (sub_nonneg.mpr hz) hcross, mul_nonneg hsa.le (sub_nonneg.mpr hdot),
    congrArg (· * Real.sin t) (Real.sin_sq_add_cos_sq a)]

theorem fixedPoint_firstWall_le_max_initial_of_low_height {H z a t : ℝ}
    (ha0 : 0 < a) (hat : a ≤ t) (htL : t ≤ Real.pi / 2)
    (hH : H ≤ Real.sin a) :
    H + (z * Real.cos t - 1) / Real.sin t ≤
      max 0 (H + (z * Real.cos a - 1) / Real.sin a) := by
  rcases le_total (Real.cos a) z with hz | hz
  · exact (fixedPoint_firstWall_le_initial ha0 hat htL hz).trans (le_max_right _ _)
  have hst : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (ha0.trans_le hat) (by linarith [Real.pi_pos])
  have hcos := Real.cos_le_one (t - a)
  rw [Real.cos_sub] at hcos
  have := (div_le_iff₀ hst).mpr (show z * Real.cos t - 1 ≤ -H * Real.sin t by
    linarith [mul_le_mul_of_nonneg_right hH hst.le, mul_le_mul_of_nonneg_right hz
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], htL⟩)])
  exact le_max_of_le_left (by linarith)

theorem firstWall_eq_fixedPoint_of_support {U : Set Plane} {b H t : ℝ}
    (hs : Real.sin t ≠ 0)
    (hsupport : angleSupport U t = b * Real.cos t + H * Real.sin t) (x : ℝ) :
    firstWall U t x = H + ((b - x) * Real.cos t - 1) / Real.sin t := by
  rw [firstWall, show support U (unitNormal t) = _ from hsupport]
  field_simp
  ring

/-- The missing first wall at every unvisited angle is controlled by
the actual old terminal wall and floor in either completion branch. -/
theorem IsJointCapMaximizer.full_niche_le_partial_of_negative_completion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α)
    {x : ℝ} (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) :
    sweptNiche U (Real.pi / 2) x ≤ partialBarrier U α x := by
  refine sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (partialBarrier_nonneg U α x)
    fun t ht => ?_
  rcases lt_or_ge t α with htα | htα
  · exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact hαL.le x)
      ⟨ht.1, htα⟩).trans (le_max_left _ _)
  refine (min_le_left _ _).trans ((?_ : firstWall U t x ≤ max 0 (firstWall U α x)).trans
    (max_le (partialBarrier_nonneg U α x) (le_max_right _ _)))
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (hU.angle_pos.trans_le htα)
    (by linarith [ht.2, Real.pi_pos])
  have hsupport := hU.first_tail_support_negative hαL hheight hm haffine ⟨htα, ht.2.le⟩
  by_cases htm : t < affineNormalAngle m
  · have hαm : α < affineNormalAngle m := htα.trans_lt htm
    rw [ite_eq_left htm] at hsupport
    rw [firstWall_eq_fixedPoint_of_support hst.ne' hsupport, firstWall_eq_fixedPoint_of_support
      (Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith [Real.pi_pos])).ne'
      (hU.first_tail_support_before_middle hm haffine hαm ⟨le_rfl, hαm.le⟩)]
    exact fixedPoint_firstWall_le_max_initial_of_low_height hU.angle_pos htα ht.2.le
      (hcomplete.resolve_left hαm.not_ge)
  · rw [ite_eq_right htm] at hsupport
    refine le_max_of_le_left ((firstWall_le_iff hst).mpr ?_)
    change angleSupport U t - 1 ≤ x * Real.cos t + 0 * Real.sin t
    rw [hsupport]
    have hxleft : horizontalLeft U + capWidth U / 4 ≤ x := hx.1
    linarith [Real.sin_le_one t, mul_nonneg (sub_nonneg.mpr hxleft)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hU.angle_pos, Real.pi_pos], ht.2.le⟩)]

theorem IsJointCapMaximizer.full_jointMaximizer_of_negative_completion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α) :
    IsJointCapMaximizer U (Real.pi / 2) := by
  -- Completion is an inequality of actual cap objectives on the same
  -- unchanged set, obtained by integrating the pointwise missing-wall bound.
  refine hU.of_score_le hU.isCap ⟨by linarith [Real.pi_pos], le_rfl⟩ ?_
  rw [capScore_eq_integrals, hU.isCap.capScore_pi_div_two]
  refine sub_le_sub_left (integral_mono_ae
    (integrableOn_sweptNiche_Icc hU.isCap.isCompact (by linarith [Real.pi_pos]) le_rfl _ _)
    (integrableOn_partialBarrier_Icc hU.isCap.isCompact hU.angle_pos hαL.le _ _) ?_) _
  filter_upwards [ae_restrict_mem (measurableSet_middleHalfInterval _ _)] with x hx
  exact hU.full_niche_le_partial_of_negative_completion hαL hheight hm haffine hcomplete hx

end AmbidextrousSofa
