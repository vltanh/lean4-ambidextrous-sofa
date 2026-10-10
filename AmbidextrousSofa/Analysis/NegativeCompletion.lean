module

public import AmbidextrousSofa.Analysis.TerminalSupportTails

@[expose] public section

/-!
# Same-cap completion of the negative-tilt alternatives

The exact missing first supports of a negative affine middle use its two
actual endpoints. Their first walls are dominated by the old terminal
wall or by zero whenever the middle normal has already been visited, or
the lower middle endpoint is at most the terminal sine.

This compares the full and partial scalar objectives on the same cap.
For a joint maximizer selected with largest terminal angle, completion
would produce another joint maximizer at the full angle. Thus the two
remaining strict negative-tilt conditions follow directly from the actual
selection property, without presupposing the global full-cap value bound.
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
  have haL : a ≤ Real.pi / 2 := hat.trans htL
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0
    (by linarith [Real.pi_pos])
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (ha0.trans_le hat)
    (by linarith [Real.pi_pos])
  have hcross : 0 ≤ Real.sin t * Real.cos a - Real.cos t * Real.sin a := by
    simpa only [Real.sin_sub] using Real.sin_nonneg_of_nonneg_of_le_pi
      (sub_nonneg.mpr hat) (show t - a ≤ Real.pi by linarith [Real.pi_pos])
  have hdot : Real.cos a * Real.cos t + Real.sin a * Real.sin t ≤ 1 := by
    have h := Real.cos_le_one (t - a)
    rw [Real.cos_sub] at h
    nlinarith only [h]
  have h1 := mul_nonneg (sub_nonneg.mpr hz) hcross
  have h2 := mul_nonneg hsa.le (sub_nonneg.mpr hdot)
  have hcircle := congrArg (fun v : ℝ => v * Real.sin t) (Real.sin_sq_add_cos_sq a)
  apply add_le_add_right
  apply (div_le_div_iff₀ hst hsa).mpr
  nlinarith only [h1, h2, hcircle]

theorem fixedPoint_firstWall_nonpos_of_low_height {H z a t : ℝ}
    (ha0 : 0 < a) (hat : a ≤ t) (htL : t ≤ Real.pi / 2)
    (hH : H ≤ Real.sin a) (hz : z ≤ Real.cos a) :
    H + (z * Real.cos t - 1) / Real.sin t ≤ 0 := by
  have ht0 : 0 < t := ha0.trans_le hat
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0
    (by linarith [Real.pi_pos])
  have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], htL⟩
  have hcos := Real.cos_le_one (t - a)
  rw [Real.cos_sub] at hcos
  have hzprod := mul_le_mul_of_nonneg_right hz hct
  have hHprod := mul_le_mul_of_nonneg_right hH hst.le
  have hquot : (z * Real.cos t - 1) / Real.sin t ≤ -H := by
    apply (div_le_iff₀ hst).mpr
    nlinarith only [hcos, hzprod, hHprod]
  linarith

theorem fixedPoint_firstWall_le_max_initial_of_low_height {H z a t : ℝ}
    (ha0 : 0 < a) (hat : a ≤ t) (htL : t ≤ Real.pi / 2)
    (hH : H ≤ Real.sin a) :
    H + (z * Real.cos t - 1) / Real.sin t ≤
      max 0 (H + (z * Real.cos a - 1) / Real.sin a) := by
  rcases le_total (Real.cos a) z with hz | hz
  · exact (fixedPoint_firstWall_le_initial ha0 hat htL hz).trans (le_max_right _ _)
  · exact (fixedPoint_firstWall_nonpos_of_low_height ha0 hat htL hH hz).trans
      (le_max_left _ _)

theorem firstWall_eq_fixedPoint_of_support {U : Set Plane} {b H t : ℝ}
    (hs : Real.sin t ≠ 0)
    (hsupport : angleSupport U t = b * Real.cos t + H * Real.sin t) (x : ℝ) :
    firstWall U t x = H + ((b - x) * Real.cos t - 1) / Real.sin t := by
  change (angleSupport U t - 1 - x * Real.cos t) / Real.sin t = _
  rw [hsupport]
  field_simp [hs] <;> ring

/-- The missing first wall at every unvisited angle is controlled by
the actual old terminal wall and floor in either completion branch. -/
theorem IsJointCapMaximizer.missing_firstWall_le_max_terminal_of_negative_completion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α)
    {t x : ℝ} (ht : t ∈ Icc α (Real.pi / 2))
    (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) :
    firstWall U t x ≤ max 0 (firstWall U α x) := by
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (hU.angle_pos.trans_le ht.1) (by linarith [ht.2, Real.pi_pos])
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  have hsupport := hU.first_tail_support_negative hαL hheight hm haffine ht
  by_cases htm : t < affineNormalAngle m
  · rw [if_pos htm] at hsupport
    have hH : capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α := by
      rcases hcomplete with ha | hH
      · exfalso
        linarith [ht.1]
      · exact hH
    have hαm : α < affineNormalAngle m := ht.1.trans_lt htm
    have hsupportα := hU.first_tail_support_before_middle hm haffine hαm
      (show α ∈ Icc α (affineNormalAngle m) from ⟨le_rfl, hαm.le⟩)
    rw [firstWall_eq_fixedPoint_of_support hst.ne' hsupport,
      firstWall_eq_fixedPoint_of_support hsa.ne' hsupportα]
    exact fixedPoint_firstWall_le_max_initial_of_low_height hU.angle_pos ht.1 ht.2 hH
  · rw [if_neg htm] at hsupport
    have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1, hU.angle_pos, Real.pi_pos], ht.2⟩
    have hxleft : horizontalLeft U + capWidth U / 4 ≤ x := hx.1
    have hzero : firstWall U t x ≤ 0 := by
      apply (firstWall_le_iff hst).mpr
      change angleSupport U t - 1 ≤ x * Real.cos t + 0 * Real.sin t
      rw [hsupport]
      nlinarith [Real.sin_le_one t, mul_nonneg (sub_nonneg.mpr hxleft) hct]
    exact hzero.trans (le_max_left _ _)

theorem IsJointCapMaximizer.full_niche_le_partial_of_negative_completion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α)
    {x : ℝ} (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) :
    sweptNiche U (Real.pi / 2) x ≤ partialBarrier U α x := by
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (partialBarrier_nonneg U α x)
  intro t ht
  by_cases htα : t < α
  · exact (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove hU.isCap.isCompact hαL.le x) ⟨ht.1, htα⟩).trans
      (le_max_left _ _)
  · calc
      cornerWall U t x ≤ firstWall U t x := min_le_left _ _
      _ ≤ max 0 (firstWall U α x) :=
        hU.missing_firstWall_le_max_terminal_of_negative_completion hαL hheight hm haffine
          hcomplete ⟨le_of_not_gt htα, ht.2.le⟩ hx
      _ ≤ partialBarrier U α x := max_le (partialBarrier_nonneg U α x) (le_max_right _ _)

/-- Completion is an inequality of actual cap objectives on the same
unchanged set, obtained by integrating the pointwise missing-wall bound. -/
theorem IsJointCapMaximizer.capScore_le_full_of_negative_completion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α) :
    capScore U α ≤ capScore U (Real.pi / 2) := by
  let J := middleHalfInterval (horizontalLeft U) (horizontalRight U)
  have hFull : IntegrableOn (sweptNiche U (Real.pi / 2)) J :=
    integrableOn_sweptNiche_Icc hU.isCap.isCompact (by linarith [Real.pi_pos]) le_rfl _ _
  have hPartial : IntegrableOn (partialBarrier U α) J :=
    integrableOn_partialBarrier_Icc hU.isCap.isCompact hU.angle_pos hαL.le _ _
  have hIntegral : (∫ x in J, sweptNiche U (Real.pi / 2) x) ≤
      ∫ x in J, partialBarrier U α x := by
    apply integral_mono_ae hFull hPartial
    filter_upwards [ae_restrict_mem (measurableSet_middleHalfInterval _ _)] with x hx
    exact hU.full_niche_le_partial_of_negative_completion hαL hheight hm haffine hcomplete hx
  rw [capScore_eq_integrals, hU.isCap.capScore_pi_div_two]
  exact sub_le_sub_left hIntegral _

theorem IsJointCapMaximizer.full_jointMaximizer_of_negative_completion
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α) :
    IsJointCapMaximizer U (Real.pi / 2) :=
  hU.of_score_le hU.isCap ⟨by linarith [Real.pi_pos], le_rfl⟩
    (hU.capScore_le_full_of_negative_completion hαL hheight hm haffine hcomplete)

/-- A largest-angle joint maximizer in the remaining negative-tilt branch
has not yet visited its middle normal and has lower middle height strictly
above the terminal sine. Both conclusions follow from proved same-cap
completion, not from a presumed terminal differential law. -/
theorem IsJointCapMaximizer.negative_remaining_tail_geometry
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    α < affineNormalAngle m ∧
      Real.sin α < capRoof U (horizontalRight U - capWidth U / 4) := by
  have hnot : ¬(affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α) := by
    intro hcomplete
    have hfull := hU.full_jointMaximizer_of_negative_completion hαL hheight hm haffine hcomplete
    exact (not_le_of_gt hαL) (hLargest U (Real.pi / 2) hfull)
  constructor
  · exact lt_of_not_ge (fun h => hnot (Or.inl h))
  · exact lt_of_not_ge (fun h => hnot (Or.inr h))

end AmbidextrousSofa
