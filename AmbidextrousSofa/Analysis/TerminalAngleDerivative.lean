module

public import AmbidextrousSofa.Analysis.PartialCapContinuity
public import AmbidextrousSofa.Analysis.SupportCurvature
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# The actual right terminal-angle derivative, with historical ties

The right support derivative is the tangent coordinate of the actual
upper endpoint of the terminal supporting face. It determines the right
derivative of the whole first wall. Adding newly visited angles changes
the swept family, so a historical tie must keep the positive part of that
derivative. The proof bounds every newly visited two-wall corner by its
first wall and retains all older angles in the supremum.

This file proves the pointwise derivative for every abscissa. Integration
and the corresponding necessary inequality at a joint maximum are separate
steps; no contact chart or terminal occupation measure is presumed here.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The horizontal coordinate of the actual upper terminal-face endpoint
after translating that point inward by its unit normal. -/
def terminalFirstRightAbscissa (U : Set Plane) (α : ℝ) : ℝ :=
  (MovingSofaOptimality.vplus U α).1 - Real.cos α

theorem IsDownwardCap.firstWall_right_deriv {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : Real.sin α ≠ 0) (x : ℝ) :
    HasDerivWithinAt (fun t => firstWall U t x)
      ((x - terminalFirstRightAbscissa U α) / Real.sin α ^ 2) (Ici α) α := by
  have h := congrArg Prod.fst (MovingSofaOptimality.vplus_eq_frame U α)
  change (MovingSofaOptimality.vplus U α).1 = angleSupport U α * Real.cos α +
    coordDot (MovingSofaOptimality.vplus U α) (MovingSofaOptimality.vvec α) * (-Real.sin α) at h
  refine ((((hU.angleSupport_right_deriv α).sub_const 1).sub
    ((Real.hasDerivAt_cos α).const_mul x).hasDerivWithinAt).div
      (Real.hasDerivAt_sin α).hasDerivWithinAt hs).congr_deriv ?_
  simp only [Pi.sub_apply, terminalFirstRightAbscissa]
  congr 1
  linear_combination x * Real.sin_sq_add_cos_sq α + h

theorem hasDerivWithinAt_right_iff_tendsto_quotient {f : ℝ → ℝ} {d a : ℝ} :
    HasDerivWithinAt f d (Ioi a) a ↔
      Tendsto (fun b => (f b - f a) / (b - a)) (𝓝[>] a) (𝓝 d) := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp), slope_fun_def_field]

theorem sweptNiche_mono_terminalAngle {U : Set Plane} (hU : IsCompact U)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) (x : ℝ) :
    sweptNiche U a x ≤ sweptNiche U b x :=
  sweptNiche_le_of_forall ha (sweptNiche_nonneg U b x) fun _ ht =>
    cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU hb x) ⟨ht.1, ht.2.trans_le hab⟩

/-- All old angles are controlled by the old history, and every new
corner is controlled by its first wall. This is an inequality for the
entire visited family, including its endpoint limit. -/
theorem partialBarrier_le_of_firstWall_bound_after {U : Set Plane} (hU : IsCompact U)
    {a b x D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2)
    (hOld : sweptNiche U a x ≤ D)
    (hNew : ∀ t ∈ Icc a b, firstWall U t x ≤ D) :
    partialBarrier U b x ≤ D := by
  refine max_le (sweptNiche_le_of_forall (ha.trans_le hab) ((sweptNiche_nonneg U a x).trans hOld)
    fun t ht => ?_) (hNew b ⟨hab, le_rfl⟩)
  rcases lt_or_ge t a with hta | hta
  · exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU (hab.trans hb) x)
      ⟨ht.1, hta⟩).trans hOld
  · exact (min_le_left _ _).trans (hNew t ⟨hta, ht.2.le⟩)

theorem IsDownwardCap.partialBarrier_right_deriv_of_terminal_strict
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2)
    (hstrict : sweptNiche U a x < firstWall U a x) :
    HasDerivWithinAt (fun b => partialBarrier U b x)
      ((x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) (Ioi a) a := by
  have hderiv := (hU.firstWall_right_deriv (α := a) (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne' x).Ioi_of_Ici
  have hcont : Continuous (fun b : TerminalAngle => sweptNiche U b x) := by
    simpa only [Function.comp_def, IsDownwardCap.toCompactCap_carrier] using
      continuous_partialCapSweptNiche.comp
        (show Continuous (fun b : TerminalAngle => ((hU.toCompactCap, b), x)) by fun_prop)
  have hOn : ContinuousOn (fun b => sweptNiche U b x) (Icc (Real.pi / 4) (Real.pi / 2)) :=
    continuousOn_iff_continuous_domRestrict.mpr hcont
  have hright := (hOn a ⟨ha0, haL.le⟩).mono_of_mem_nhdsWithin (s := Ioi a)
    (mem_of_superset (Ioo_mem_nhdsGT haL) fun b hb => ⟨ha0.trans hb.1.le, hb.2.le⟩)
  refine hderiv.congr_of_eventuallyEq ?_ (max_eq_right hstrict.le)
  filter_upwards [hright.tendsto.eventually_lt hderiv.continuousWithinAt.tendsto hstrict]
    with b hb
  exact max_eq_right hb.le

theorem IsDownwardCap.partialBarrier_right_deriv_of_history_strict
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2)
    (hstrict : firstWall U a x < sweptNiche U a x) :
    HasDerivWithinAt (fun b => partialBarrier U b x) 0 (Ioi a) a := by
  have ha : 0 < a := by linarith [Real.pi_pos]
  obtain ⟨c, hc, hlocal⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp
    ((hU.firstWall_right_deriv (Real.sin_pos_of_pos_of_lt_pi ha (by linarith)).ne'
      x).continuousWithinAt.tendsto.eventually_lt_const hstrict)
  refine (hasDerivWithinAt_const a (Ioi a) (sweptNiche U a x)).congr_of_eventuallyEq ?_
    (max_eq_left hstrict.le)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hc haL)] with b hb
  have hbL : b ≤ Real.pi / 2 := (hb.2.trans_le (min_le_right _ _)).le
  exact le_antisymm (partialBarrier_le_of_firstWall_bound_after hU.isCompact ha hb.1.le hbL le_rfl
    fun t ht => le_of_lt (hlocal ⟨ht.1, ht.2.trans_lt (hb.2.trans_le (min_le_left _ _))⟩))
    ((sweptNiche_mono_terminalAngle hU.isCompact ha hb.1.le hbL x).trans (le_max_left _ _))

/-- On a historical tie, the old maximum supplies the fixed lower
competitor. Uniform first-order bounds for the first wall control every
newly visited angle, including angles varying with the perturbation. -/
theorem IsDownwardCap.partialBarrier_right_deriv_of_tie
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2)
    (htie : firstWall U a x = sweptNiche U a x) :
    HasDerivWithinAt (fun b => partialBarrier U b x)
      (max ((x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) 0) (Ioi a) a := by
  set D := (x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2
  have ha : 0 < a := by linarith [Real.pi_pos]
  have hratio := hasDerivWithinAt_right_iff_tendsto_quotient.mp
    (hU.firstWall_right_deriv (Real.sin_pos_of_pos_of_lt_pi ha (by linarith)).ne' x).Ioi_of_Ici
  have hbase : partialBarrier U a x = firstWall U a x := by rw [partialBarrier, ← htie, max_self]
  refine hasDerivWithinAt_right_iff_tendsto_quotient.mpr
    (tendsto_order.mpr ⟨fun r hr => ?_, fun r hr => ?_⟩)
  · -- The terminal wall and the old history both bound the barrier from below.
    filter_upwards [(hratio.max tendsto_const_nhds).eventually_const_lt hr,
      Ioo_mem_nhdsGT haL] with b hb hba
    have hhist : firstWall U a x ≤ partialBarrier U b x := by
      rw [htie]
      exact (sweptNiche_mono_terminalAngle hU.isCompact ha hba.1.le hba.2.le x).trans
        (le_max_left _ _)
    have hwall : firstWall U b x ≤ partialBarrier U b x := le_max_right _ _
    rw [hbase]
    exact hb.trans_le (max_le (div_le_div_of_nonneg_right (by linarith) (sub_pos.2 hba.1).le)
      (div_nonneg (sub_nonneg.2 hhist) (sub_pos.2 hba.1).le))
  · -- Above, every newly visited first wall stays below a line of slope `k < r`.
    set k := (max D 0 + r) / 2 with hk
    have hk0 : 0 < k := by linarith [le_max_right D 0]
    obtain ⟨c, hc, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
      (hratio.eventually_lt_const (show D < k by linarith [le_max_left D 0]))
    filter_upwards [Ioo_mem_nhdsGT (lt_min hc haL)] with b hb
    have hba : 0 < b - a := sub_pos.mpr hb.1
    have hbound := partialBarrier_le_of_firstWall_bound_after (D := firstWall U a x + k * (b - a))
      hU.isCompact ha hb.1.le (hb.2.trans_le (min_le_right _ _)).le
      (by rw [← htie]; nlinarith) fun t ht => by
        rcases ht.1.eq_or_lt with rfl | hat
        · nlinarith
        · have := (div_lt_iff₀ (sub_pos.mpr hat)).mp
            (hlocal ⟨hat, ht.2.trans_lt (hb.2.trans_le (min_le_left _ _))⟩)
          nlinarith [ht.2]
    rw [hbase]
    exact ((div_le_iff₀ hba).mpr (show _ ≤ k * (b - a) by linarith)).trans_lt
      (show k < r by linarith)

/-- The exact pointwise derivative uses the positive part on the entire
historical tie set, without assigning that set zero measure. -/
def terminalBarrierRightDerivative (U : Set Plane) (a x : ℝ) : ℝ :=
  if sweptNiche U a x < firstWall U a x then
    (x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2
  else if firstWall U a x = sweptNiche U a x then
    max ((x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) 0
  else 0

theorem IsDownwardCap.partialBarrier_right_deriv {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) (x : ℝ) :
    HasDerivWithinAt (fun b => partialBarrier U b x)
      (terminalBarrierRightDerivative U a x) (Ioi a) a := by
  unfold terminalBarrierRightDerivative
  split_ifs with hstrict htie
  · exact hU.partialBarrier_right_deriv_of_terminal_strict ha0 haL hstrict
  · exact hU.partialBarrier_right_deriv_of_tie ha0 haL htie
  · exact hU.partialBarrier_right_deriv_of_history_strict ha0 haL
      (lt_of_le_of_ne (not_lt.1 hstrict) htie)

theorem IsDownwardCap.measurable_terminalBarrierRightDerivative {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) : Measurable (terminalBarrierRightDerivative U a) := by
  have hn := measurable_sweptNiche hU.isCompact (by linarith [Real.pi_pos]) haL.le
  have hR := (continuous_firstWall U a).measurable
  have hD : Measurable (fun x : ℝ =>
      (x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) := by fun_prop
  exact Measurable.ite (measurableSet_lt hn hR) hD
    (Measurable.ite (measurableSet_eq_fun hR hn) (hD.max measurable_const) measurable_const)

end AmbidextrousSofa
