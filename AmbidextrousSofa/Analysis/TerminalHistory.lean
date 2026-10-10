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

theorem terminalFirstLeftAbscissa_eq_frame (U : Set Plane) (α : ℝ) :
    terminalFirstLeftAbscissa U α =
      (angleSupport U α - 1) * Real.cos α -
        coordDot (MovingSofaOptimality.vminus U α) (MovingSofaOptimality.vvec α) * Real.sin α := by
  have hframe := MovingSofaOptimality.eq_dot_uvec_smul_add (MovingSofaOptimality.vminus U α) α
  rw [MovingSofaOptimality.dot_vminus_uvec] at hframe
  have h := congrArg Prod.fst hframe
  change (MovingSofaOptimality.vminus U α).1 = angleSupport U α * Real.cos α +
    coordDot (MovingSofaOptimality.vminus U α) (MovingSofaOptimality.vvec α) * (-Real.sin α) at h
  unfold terminalFirstLeftAbscissa
  linarith

theorem IsDownwardCap.firstWall_left_deriv {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : Real.sin α ≠ 0) (x : ℝ) :
    HasDerivWithinAt (fun t => firstWall U t x)
      ((x - terminalFirstLeftAbscissa U α) / Real.sin α ^ 2) (Iic α) α := by
  have hn := ((hU.angleSupport_left_deriv α).sub_const 1).sub
    (((Real.hasDerivAt_cos α).const_mul x).hasDerivWithinAt)
  have h := hn.div (Real.hasDerivAt_sin α).hasDerivWithinAt hs
  change HasDerivWithinAt (fun t => firstWall U t x)
    (((coordDot (MovingSofaOptimality.vminus U α) (MovingSofaOptimality.vvec α) - x * (-Real.sin α)) *
      Real.sin α - (angleSupport U α - 1 - x * Real.cos α) * Real.cos α) /
      Real.sin α ^ 2) (Iic α) α at h
  apply h.congr_deriv
  rw [terminalFirstLeftAbscissa_eq_frame]
  congr 1
  have hcircle := congrArg (fun z : ℝ => x * z) (Real.sin_sq_add_cos_sq α)
  nlinarith only [hcircle]

theorem hasDerivWithinAt_left_iff_tendsto_quotient {f : ℝ → ℝ} {d a : ℝ} :
    HasDerivWithinAt f d (Iio a) a ↔
      Tendsto (fun b => (f b - f a) / (b - a)) (𝓝[<] a) (𝓝 d) := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp), slope_fun_def_field]

theorem IsDownwardCap.secondWall_continuousAt_angle {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hc : Real.cos α ≠ 0) (x : ℝ) :
    ContinuousAt (fun t => secondWall U t x) α := by
  exact (((((continuous_support hU.isCompact).comp continuous_companionNormal).continuousAt.sub
    continuousAt_const).add (continuousAt_const.mul Real.continuous_sin.continuousAt)).div
    Real.continuous_cos.continuousAt hc)

/-- A strict terminal companion gap and the negative left derivative
produce a genuine earlier two-wall competitor. Support continuity alone
suffices for the companion wall; no terminal-atom hypothesis is used. -/
theorem IsDownwardCap.firstWall_lt_history_between_corner_and_left_endpoint
    {U : Set Plane} (hU : IsDownwardCap U) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hx0 : (attachedCorner U α).1 < x)
    (hx1 : x < terminalFirstLeftAbscissa U α) :
    firstWall U α x < sweptNiche U α x := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hcomp : firstWall U α x < secondWall U α x := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hx0) ((secondWall_le_firstWall_iff hs hc).mp h)
  have hderiv := (hU.firstWall_left_deriv hs.ne' x).Iio_of_Iic
  have hratio := hasDerivWithinAt_left_iff_tendsto_quotient.mp hderiv
  have hneg : (x - terminalFirstLeftAbscissa U α) / Real.sin α ^ 2 < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr hx1) (sq_pos_of_pos hs)
  have hfirst : ∀ᶠ t in 𝓝[<] α, firstWall U α x < firstWall U t x := by
    filter_upwards [Filter.Tendsto.eventually_lt_const hneg hratio,
      Ioo_mem_nhdsLT hα0] with t ht hta
    have hprod := mul_pos_of_neg_of_neg ht (sub_neg.mpr hta.2)
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hta.2.ne)] at hprod
    linarith
  have hsecond : ∀ᶠ t in 𝓝[<] α, firstWall U α x < secondWall U t x :=
    Filter.Tendsto.eventually_const_lt hcomp
      ((hU.secondWall_continuousAt_angle hc.ne' x).tendsto.mono_left nhdsWithin_le_nhds)
  have hex : ∀ᶠ t in 𝓝[<] α,
      t ∈ Ioo 0 α ∧ firstWall U α x < cornerWall U t x := by
    filter_upwards [Ioo_mem_nhdsLT hα0, hfirst, hsecond] with t ht hft hst
    exact ⟨ht, lt_min hft hst⟩
  obtain ⟨t, ht, hwall⟩ := hex.exists
  exact hwall.trans_le (cornerWall_le_sweptNiche
    (sweptWallValues_bddAbove hU.isCompact hαL.le x) ht)

theorem firstWall_neg_of_terminalTailZero_lt (U : Set Plane) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hx : terminalTailZero U α < x) :
    firstWall U α x < 0 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
  exact mul_neg_of_pos_of_neg (div_pos hc hs) (sub_neg.mpr hx)

/-- Every terminal contact of an overlong face is confined before the
actual terminal corner. This includes the entire historical tie set. -/
theorem IsDownwardCap.terminal_contact_le_corner_of_overlong_facet
    {U : Set Plane} (hU : IsDownwardCap U) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α)
    (hx : sweptNiche U α x ≤ firstWall U α x) :
    x ≤ (attachedCorner U α).1 := by
  have hzero : terminalTailZero U α < terminalFirstLeftAbscissa U α := by
    rw [terminalFirstLeftAbscissa_eq_right_add_width]
    unfold terminalTailZero terminalTailReserve terminalFirstRightAbscissa at *
    dsimp only [terminalTailPoint] at *
    linarith
  by_contra h
  have hcorner : (attachedCorner U α).1 < x := lt_of_not_ge h
  by_cases hleft : x < terminalFirstLeftAbscissa U α
  · exact (not_le_of_gt (hU.firstWall_lt_history_between_corner_and_left_endpoint
      hα0 hαL hcorner hleft)) hx
  · have hnegative := firstWall_neg_of_terminalTailZero_lt U hα0 hαL
      (hzero.trans_le (le_of_not_gt hleft))
    linarith [sweptNiche_nonneg U α x]

theorem IsDownwardCap.terminalBarrier_derivative_sign_of_overlong_facet
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α) (x : ℝ) :
    terminalBarrierRightDerivative U α x ≤ 0 ∧
      (sweptNiche U α x < firstWall U α x → terminalBarrierRightDerivative U α x < 0) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hcontact : sweptNiche U α x ≤ firstWall U α x →
      (x - terminalFirstRightAbscissa U α) / Real.sin α ^ 2 < 0 := by
    intro hx
    exact div_neg_of_neg_of_pos
      (sub_neg.mpr ((hU.terminal_contact_le_corner_of_overlong_facet
        hα0 hαL hfacet hx).trans_lt hcorner)) (sq_pos_of_pos hs)
  by_cases hstrict : sweptNiche U α x < firstWall U α x
  · simp only [terminalBarrierRightDerivative, if_pos hstrict]
    exact ⟨(hcontact hstrict.le).le, fun _ => hcontact hstrict.le⟩
  · by_cases htie : firstWall U α x = sweptNiche U α x
    · simp only [terminalBarrierRightDerivative, if_neg hstrict, if_pos htie,
        max_eq_right (hcontact htie.symm.le).le]
      exact ⟨le_rfl, fun h => (hstrict h).elim⟩
    · simp only [terminalBarrierRightDerivative, if_neg hstrict, if_neg htie]
      exact ⟨le_rfl, fun h => (hstrict h).elim⟩

theorem IsDownwardCap.continuous_sweptNiche_terminalAngle {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    Continuous (sweptNiche U α) := by
  have hpath : Continuous (fun x : ℝ => ((hU.toCompactCap, (⟨α, hα⟩ : TerminalAngle)), x)) :=
    continuous_const.prodMk continuous_id
  have h := continuous_partialCapSweptNiche.comp hpath
  exact h

/-- The integral right-angle condition forces the outgoing wall to be
redundant everywhere on the middle window. Continuity upgrades the exact
almost-everywhere consequence; the tie set has not been discarded. -/
theorem IsJointCapMaximizer.partialBarrier_eq_history_of_overlong_facet
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α) :
    EqOn (partialBarrier U α) (sweptNiche U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) := by
  let J := middleHalfInterval (horizontalLeft U) (horizontalRight U)
  have hsign : ∀ x, terminalBarrierRightDerivative U α x ≤ 0 :=
    fun x => (hU.isCap.terminalBarrier_derivative_sign_of_overlong_facet
      hU.angle_pos hαL hcorner hfacet x).1
  have hDi : IntegrableOn (terminalBarrierRightDerivative U α) J :=
    hU.isCap.integrableOn_terminalBarrierRightDerivative_Icc hU.angle_mem.1 hαL _ _
  have hint : (∫ x in J, terminalBarrierRightDerivative U α x) = 0 := by
    apply le_antisymm
    · exact integral_nonpos_of_ae (Eventually.of_forall hsign)
    · exact hU.terminal_variation_integral_nonneg hαL
  have hnegint : (∫ x in J, -terminalBarrierRightDerivative U α x) = 0 := by
    rw [integral_neg, hint, neg_zero]
  have hdzero : (fun x => -terminalBarrierRightDerivative U α x) =ᵐ[volume.restrict J] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun x => neg_nonneg.mpr (hsign x))) hDi.neg).mp hnegint
  have hbar : (partialBarrier U α) =ᵐ[volume.restrict J] sweptNiche U α := by
    filter_upwards [hdzero] with x hx
    apply max_eq_left
    apply le_of_not_gt
    intro hstrict
    have hnegative := (hU.isCap.terminalBarrier_derivative_sign_of_overlong_facet
      hU.angle_pos hαL hcorner hfacet x).2 hstrict
    change -terminalBarrierRightDerivative U α x = 0 at hx
    linarith
  have hwidth : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hends : horizontalLeft U + capWidth U / 4 < horizontalRight U - capWidth U / 4 := by
    unfold capWidth at *
    linarith
  exact Measure.eqOn_Icc_of_ae_eq volume hends.ne hbar
    (hU.isCap.continuous_partialBarrier hU.angle_mem).continuousOn
    (hU.isCap.continuous_sweptNiche_terminalAngle hU.angle_mem).continuousOn

theorem IsJointCapMaximizer.firstWall_le_history_of_overlong_facet
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α)
    {x : ℝ} (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) :
    firstWall U α x ≤ sweptNiche U α x := by
  rw [← hU.partialBarrier_eq_history_of_overlong_facet hαL hcorner hfacet hx]
  exact le_max_right _ _

end AmbidextrousSofa
