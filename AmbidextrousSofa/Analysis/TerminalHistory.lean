module

public import AmbidextrousSofa.Analysis.TerminalFacet
public import AmbidextrousSofa.Analysis.TerminalAngleIntegral
public import AmbidextrousSofa.Analysis.CornerConfinement
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# The actual terminal facet and strict historical shadow

The left derivative of the first wall uses the lower/right endpoint of
the terminal face. Between the terminal corner and that shifted endpoint,
an earlier first wall is strictly higher, while continuity keeps the
companion wall higher as well. Thus the actual old two-wall history has
a strict gap there. No choice of source occupation on a tie is required.

For an overlong terminal face whose corner lies before its shifted upper
endpoint, every terminal contact lies strictly to the left of that upper
endpoint. The proved right-angle variation, including its entire tie
term, then makes the outgoing wall redundant on the whole middle window.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def terminalFirstLeftAbscissa (U : Set Plane) (α : ℝ) : ℝ :=
  (MovingSofaOptimality.vminus U α).1 - Real.cos α

theorem terminalFirstLeftAbscissa_eq_right_add_width (U : Set Plane) (α : ℝ) :
    terminalFirstLeftAbscissa U α =
      terminalFirstRightAbscissa U α + terminalFaceWidth U α := by
  unfold terminalFirstLeftAbscissa terminalFirstRightAbscissa terminalFaceWidth
  ring

theorem IsDownwardCap.secondWall_continuousAt_angle {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hc : Real.cos α ≠ 0) (x : ℝ) :
    ContinuousAt (fun t => secondWall U t x) α :=
  ((((continuous_support hU.isCompact).comp continuous_companionNormal).continuousAt.sub
    continuousAt_const).add (continuousAt_const.mul Real.continuous_sin.continuousAt)).div
    Real.continuous_cos.continuousAt hc

/-- A strict terminal companion gap and the negative left derivative
produce a genuine earlier two-wall competitor. -/
theorem IsDownwardCap.firstWall_lt_history_between_corner_and_left_endpoint
    {U : Set Plane} (hU : IsDownwardCap U) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hx0 : (attachedCorner U α).1 < x)
    (hx1 : x < terminalFirstLeftAbscissa U α) :
    firstWall U α x < sweptNiche U α x := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα0 hαL
  -- The left derivative of the first wall is negative at `x`.
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
    (firstWall_hasDerivWithinAt (x := x) hs.ne' (MovingSofaOptimality.dot_vminus_uvec U α)
      (hU.angleSupport_left_deriv α)).Iio_of_Iic
  have hfirst : ∀ᶠ t in 𝓝[<] α, firstWall U α x < firstWall U t x := by
    filter_upwards [hslope.eventually_lt_const (div_neg_of_neg_of_pos (sub_neg.mpr hx1)
      (by positivity)), Ioo_mem_nhdsLT hα0] with t ht hta
    rw [slope_def_field] at ht
    linarith [div_mul_cancel₀ (firstWall U t x - firstWall U α x) (sub_ne_zero.mpr hta.2.ne),
      mul_pos_of_neg_of_neg ht (sub_neg.mpr hta.2)]
  have hsecond : ∀ᶠ t in 𝓝[<] α, firstWall U α x < secondWall U t x :=
    ((hU.secondWall_continuousAt_angle hc.ne' x).tendsto.mono_left
      nhdsWithin_le_nhds).eventually_const_lt
      (not_le.mp ((secondWall_le_firstWall_iff hs hc).not.mpr hx0.not_ge))
  obtain ⟨t, ht, hft, hst⟩ := (Eventually.and (Ioo_mem_nhdsLT hα0) (hfirst.and hsecond)).exists
  exact (lt_min hft hst).trans_le
    (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact hαL.le x) ht)

theorem IsDownwardCap.terminalBarrier_derivative_sign_of_overlong_facet
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α) (x : ℝ) :
    terminalBarrierRightDerivative U α x ≤ 0 ∧
      (sweptNiche U α x < firstWall U α x → terminalBarrierRightDerivative U α x < 0) := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα0 hαL
  -- Every terminal contact, ties included, lies before the corner: beyond it the history is
  -- strictly higher up to the shifted left endpoint, and the outgoing wall is negative after it.
  have hcontact (hx : sweptNiche U α x ≤ firstWall U α x) :
      (x - terminalFirstRightAbscissa U α) / Real.sin α ^ 2 < 0 := by
    refine div_neg_of_neg_of_pos (sub_neg.mpr (lt_of_le_of_lt ?_ hcorner)) (by positivity)
    by_contra h
    rcases lt_or_ge x (terminalFirstLeftAbscissa U α) with hleft | hleft
    · exact (hU.firstWall_lt_history_between_corner_and_left_endpoint hα0 hαL (not_le.mp h)
        hleft).not_ge hx
    have hzero : terminalTailZero U α < x := by
      rw [terminalFirstLeftAbscissa_eq_right_add_width] at hleft
      unfold terminalTailReserve at hfacet
      unfold terminalTailZero terminalFirstRightAbscissa terminalTailPoint at *
      linarith
    have hneg : firstWall U α x < 0 := by
      rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
      exact mul_neg_of_pos_of_neg (div_pos hc hs) (sub_neg.mpr hzero)
    linarith [sweptNiche_nonneg U α x]
  unfold terminalBarrierRightDerivative
  split_ifs with hstrict htie
  · exact ⟨(hcontact hstrict.le).le, fun _ => hcontact hstrict.le⟩
  · exact ⟨max_le (hcontact htie.symm.le).le le_rfl, fun h => absurd h hstrict⟩
  · exact ⟨le_rfl, fun h => absurd h hstrict⟩

theorem IsDownwardCap.continuous_sweptNiche_terminalAngle {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    Continuous (sweptNiche U α) :=
  (continuous_partialCapSweptNiche.comp
    (.prodMk_right (hU.toCompactCap, (⟨α, hα⟩ : TerminalAngle))) :)

/-- The integral right-angle condition forces the outgoing wall to be
redundant everywhere on the middle window. Continuity upgrades the exact
almost-everywhere consequence; the tie set has not been discarded. -/
theorem IsJointCapMaximizer.firstWall_le_history_of_overlong_facet
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α)
    {x : ℝ} (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) :
    firstWall U α x ≤ sweptNiche U α x := by
  have hsign := hU.isCap.terminalBarrier_derivative_sign_of_overlong_facet hU.angle_pos hαL
    hcorner hfacet
  have hzero : (fun x => -terminalBarrierRightDerivative U α x) =ᵐ[volume.restrict
      (middleHalfInterval (horizontalLeft U) (horizontalRight U))] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.mpr (hsign x).1)
      (hU.isCap.integrableOn_terminalBarrierRightDerivative_Icc hU.angle_mem.1 hαL _ _).neg).mp ?_
    rw [integral_neg, neg_eq_zero]
    exact (integral_nonpos fun x => (hsign x).1).antisymm
      (hU.terminal_variation_integral_nonneg hαL)
  have hbar : partialBarrier U α =ᵐ[volume.restrict
      (middleHalfInterval (horizontalLeft U) (horizontalRight U))] sweptNiche U α := by
    filter_upwards [hzero] with x hx
    exact max_eq_left (not_lt.mp fun h => by simp at hx; linarith [(hsign x).2 h])
  have hends : horizontalLeft U + capWidth U / 4 < horizontalRight U - capWidth U / 4 := by
    linarith [hU.width_bounds.1, one_lt_M,
      show capWidth U = horizontalRight U - horizontalLeft U from rfl]
  rw [← Measure.eqOn_Icc_of_ae_eq volume hends.ne hbar
    (hU.isCap.continuous_partialBarrier hU.angle_mem).continuousOn
    (hU.isCap.continuous_sweptNiche_terminalAngle hU.angle_mem).continuousOn hx]
  exact le_max_right _ _

end AmbidextrousSofa
