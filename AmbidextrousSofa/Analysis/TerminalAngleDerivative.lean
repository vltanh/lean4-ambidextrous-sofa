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

theorem terminalFirstRightAbscissa_eq_frame (U : Set Plane) (α : ℝ) :
    terminalFirstRightAbscissa U α =
      (angleSupport U α - 1) * Real.cos α -
        coordDot (MovingSofaOptimality.vplus U α) (MovingSofaOptimality.vvec α) * Real.sin α := by
  have h := congrArg Prod.fst (MovingSofaOptimality.vplus_eq_frame U α)
  change (MovingSofaOptimality.vplus U α).1 = angleSupport U α * Real.cos α +
    coordDot (MovingSofaOptimality.vplus U α) (MovingSofaOptimality.vvec α) * (-Real.sin α) at h
  unfold terminalFirstRightAbscissa
  linarith

theorem IsDownwardCap.firstWall_right_deriv {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : Real.sin α ≠ 0) (x : ℝ) :
    HasDerivWithinAt (fun t => firstWall U t x)
      ((x - terminalFirstRightAbscissa U α) / Real.sin α ^ 2) (Ici α) α := by
  have hn := ((hU.angleSupport_right_deriv α).sub_const 1).sub
    (((Real.hasDerivAt_cos α).const_mul x).hasDerivWithinAt)
  have h := hn.div (Real.hasDerivAt_sin α).hasDerivWithinAt hs
  change HasDerivWithinAt (fun t => firstWall U t x)
    (((coordDot (MovingSofaOptimality.vplus U α) (MovingSofaOptimality.vvec α) - x * (-Real.sin α)) *
      Real.sin α - (angleSupport U α - 1 - x * Real.cos α) * Real.cos α) /
      Real.sin α ^ 2) (Ici α) α at h
  apply h.congr_deriv
  rw [terminalFirstRightAbscissa_eq_frame]
  congr 1
  have hcircle := congrArg (fun z : ℝ => x * z) (Real.sin_sq_add_cos_sq α)
  nlinarith only [hcircle]

theorem hasDerivWithinAt_right_iff_tendsto_quotient {f : ℝ → ℝ} {d a : ℝ} :
    HasDerivWithinAt f d (Ioi a) a ↔
      Tendsto (fun b => (f b - f a) / (b - a)) (𝓝[>] a) (𝓝 d) := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp), slope_fun_def_field]

theorem sweptNiche_mono_terminalAngle {U : Set Plane} (hU : IsCompact U)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) (x : ℝ) :
    sweptNiche U a x ≤ sweptNiche U b x := by
  apply sweptNiche_le_of_forall ha (sweptNiche_nonneg U b x)
  intro t ht
  exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU hb x)
    ⟨ht.1, ht.2.trans_le hab⟩

theorem old_history_and_first_le_partialBarrier {U : Set Plane} (hU : IsCompact U)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) (x : ℝ) :
    max (sweptNiche U a x) (firstWall U b x) ≤ partialBarrier U b x :=
  max_le_max (sweptNiche_mono_terminalAngle hU ha hab hb x) le_rfl

/-- All old angles are controlled by the old history, and every new
corner is controlled by its first wall. This is an inequality for the
entire visited family, including its endpoint limit. -/
theorem partialBarrier_le_of_firstWall_bound_after {U : Set Plane} (hU : IsCompact U)
    {a b x D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2)
    (hOld : sweptNiche U a x ≤ D)
    (hNew : ∀ t ∈ Icc a b, firstWall U t x ≤ D) :
    partialBarrier U b x ≤ D := by
  refine max_le ?_ (hNew b ⟨hab, le_rfl⟩)
  apply sweptNiche_le_of_forall (ha.trans_le hab)
    ((sweptNiche_nonneg U a x).trans hOld)
  intro t ht
  by_cases hta : t < a
  · exact (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove hU (hab.trans hb) x) ⟨ht.1, hta⟩).trans hOld
  · exact (min_le_left _ _).trans (hNew t ⟨le_of_not_gt hta, ht.2.le⟩)

theorem IsDownwardCap.sweptNiche_right_continuous {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) (x : ℝ) :
    ContinuousWithinAt (fun b => sweptNiche U b x) (Ioi a) a := by
  have hcont : Continuous (fun b : TerminalAngle => sweptNiche U b x) := by
    have h := continuous_partialCapSweptNiche.comp
      (show Continuous (fun b : TerminalAngle => ((hU.toCompactCap, b), x)) by fun_prop)
    simpa only [Function.comp_def, IsDownwardCap.toCompactCap_carrier] using h
  have hOn : ContinuousOn (fun b : ℝ => sweptNiche U b x)
      (Icc (Real.pi / 4) (Real.pi / 2)) :=
    continuousOn_iff_continuous_domRestrict.mpr hcont
  apply (hOn a ⟨ha0, haL.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [Ioo_mem_nhdsGT haL] with b hb
  exact ⟨ha0.trans hb.1.le, hb.2.le⟩

theorem IsDownwardCap.partialBarrier_right_deriv_of_terminal_strict
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2)
    (hstrict : sweptNiche U a x < firstWall U a x) :
    HasDerivWithinAt (fun b => partialBarrier U b x)
      ((x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) (Ioi a) a := by
  have hs : Real.sin a ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne'
  have hderiv := (hU.firstWall_right_deriv hs x).Ioi_of_Ici
  have hevent := (hU.sweptNiche_right_continuous ha0 haL x).tendsto.eventually_lt
    hderiv.continuousWithinAt.tendsto hstrict
  apply hderiv.congr_of_eventuallyEq
  · filter_upwards [hevent] with b hb
    exact max_eq_right hb.le
  · exact max_eq_right hstrict.le

theorem IsDownwardCap.partialBarrier_right_deriv_of_history_strict
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2)
    (hstrict : firstWall U a x < sweptNiche U a x) :
    HasDerivWithinAt (fun b => partialBarrier U b x) 0 (Ioi a) a := by
  have ha : 0 < a := by linarith [Real.pi_pos]
  have hs : Real.sin a ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ha
    (by linarith [Real.pi_pos])).ne'
  have hcont := (hU.firstWall_right_deriv hs x).Ioi_of_Ici.continuousWithinAt
  have hgap : ∀ᶠ b in 𝓝[>] a, firstWall U b x < sweptNiche U a x :=
    Filter.Tendsto.eventually_lt_const hstrict hcont.tendsto
  obtain ⟨c, hc, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgap
  have hevent : (fun b => partialBarrier U b x) =ᶠ[𝓝[>] a]
      (fun _ => sweptNiche U a x) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hc haL)] with b hb
    have hbc : b < c := hb.2.trans_le (min_le_left _ _)
    have hbL : b ≤ Real.pi / 2 := (hb.2.trans_le (min_le_right _ _)).le
    apply le_antisymm
    · apply partialBarrier_le_of_firstWall_bound_after hU.isCompact ha hb.1.le hbL le_rfl
      intro t ht
      by_cases hta : t = a
      · simpa only [hta] using hstrict.le
      · exact (hlocal ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2.trans_lt hbc⟩).le
    · exact (sweptNiche_mono_terminalAngle hU.isCompact ha hb.1.le hbL x).trans
        (le_max_left _ _)
  apply (hasDerivWithinAt_const a (Ioi a) (sweptNiche U a x)).congr_of_eventuallyEq hevent
  exact max_eq_left hstrict.le

/-- On a historical tie, the old maximum supplies the fixed lower
competitor. Uniform first-order bounds for the first wall control every
newly visited angle, including angles varying with the perturbation. -/
theorem IsDownwardCap.partialBarrier_right_deriv_of_tie
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (ha0 : Real.pi / 4 ≤ a) (haL : a < Real.pi / 2)
    (htie : firstWall U a x = sweptNiche U a x) :
    HasDerivWithinAt (fun b => partialBarrier U b x)
      (max ((x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) 0) (Ioi a) a := by
  let D := (x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2
  have ha : 0 < a := by linarith [Real.pi_pos]
  have hs : Real.sin a ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ha
    (by linarith [Real.pi_pos])).ne'
  have hderiv : HasDerivWithinAt (fun b => firstWall U b x) D (Ioi a) a :=
    (hU.firstWall_right_deriv hs x).Ioi_of_Ici
  have hratio := hasDerivWithinAt_right_iff_tendsto_quotient.mp hderiv
  have hbase : partialBarrier U a x = firstWall U a x := by
    rw [partialBarrier, ← htie, max_self]
  have hlower : ∀ b ∈ Ioo a (Real.pi / 2),
      max ((firstWall U b x - firstWall U a x) / (b - a)) 0 ≤
        (partialBarrier U b x - partialBarrier U a x) / (b - a) := by
    intro b hb
    have hba : 0 < b - a := sub_pos.mpr hb.1
    have hterminal : firstWall U b x ≤ partialBarrier U b x := le_max_right _ _
    have hhistory : firstWall U a x ≤ partialBarrier U b x := by
      rw [htie]
      exact (sweptNiche_mono_terminalAngle hU.isCompact ha hb.1.le hb.2.le x).trans
        (le_max_left _ _)
    rw [hbase]
    exact max_le (div_le_div_of_nonneg_right (by linarith) hba.le)
      (div_nonneg (sub_nonneg.mpr hhistory) hba.le)
  apply hasDerivWithinAt_right_iff_tendsto_quotient.mpr
  apply tendsto_order.mpr
  constructor
  · intro r hr
    have hlowerLimit : Tendsto
        (fun b => max ((firstWall U b x - firstWall U a x) / (b - a)) 0)
        (𝓝[>] a) (𝓝 (max D 0)) := hratio.max tendsto_const_nhds
    filter_upwards [Filter.Tendsto.eventually_const_lt hr hlowerLimit,
      Ioo_mem_nhdsGT haL] with b hb hba
    exact hb.trans_le (hlower b hba)
  · intro r hr
    let k := (max D 0 + r) / 2
    have hk0 : 0 < k := by dsimp [k]; linarith [le_max_right D 0]
    have hDk : D < k := by dsimp [k]; linarith [le_max_left D 0]
    have hkr : k < r := by dsimp [k]; linarith
    have hsmall : ∀ᶠ t in 𝓝[>] a,
        (firstWall U t x - firstWall U a x) / (t - a) < k :=
      Filter.Tendsto.eventually_lt_const hDk hratio
    obtain ⟨c, hc, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
    filter_upwards [Ioo_mem_nhdsGT (lt_min hc haL)] with b hb
    have hbc : b < c := hb.2.trans_le (min_le_left _ _)
    have hbL : b ≤ Real.pi / 2 := (hb.2.trans_le (min_le_right _ _)).le
    have hba : 0 < b - a := sub_pos.mpr hb.1
    have hwall : ∀ t ∈ Icc a b,
        firstWall U t x ≤ firstWall U a x + k * (b - a) := by
      intro t ht
      by_cases hta : t = a
      · rw [hta]
        linarith [mul_nonneg hk0.le hba.le]
      · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
        have hlocal' := hlocal ⟨hat, ht.2.trans_lt hbc⟩
        have hfirst := (div_lt_iff₀ (sub_pos.mpr hat)).mp hlocal'
        have hscale := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hk0.le
        linarith
    have hbound : partialBarrier U b x ≤ firstWall U a x + k * (b - a) :=
      partialBarrier_le_of_firstWall_bound_after hU.isCompact ha hb.1.le hbL
        (by rw [← htie]; linarith [mul_nonneg hk0.le hba.le]) hwall
    have hquotient : (partialBarrier U b x - partialBarrier U a x) / (b - a) ≤ k := by
      apply (div_le_iff₀ hba).mpr
      rw [hbase]
      linarith
    exact hquotient.trans_lt hkr

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
  by_cases hstrict : sweptNiche U a x < firstWall U a x
  · rw [terminalBarrierRightDerivative, if_pos hstrict]
    exact hU.partialBarrier_right_deriv_of_terminal_strict ha0 haL hstrict
  · by_cases htie : firstWall U a x = sweptNiche U a x
    · rw [terminalBarrierRightDerivative, if_neg hstrict, if_pos htie]
      exact hU.partialBarrier_right_deriv_of_tie ha0 haL htie
    · rw [terminalBarrierRightDerivative, if_neg hstrict, if_neg htie]
      exact hU.partialBarrier_right_deriv_of_history_strict ha0 haL
        (lt_of_le_of_ne (le_of_not_gt hstrict) htie)

theorem IsDownwardCap.measurable_terminalBarrierRightDerivative {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha0 : Real.pi / 4 ≤ a)
    (haL : a < Real.pi / 2) : Measurable (terminalBarrierRightDerivative U a) := by
  have ha : 0 < a := by linarith [Real.pi_pos]
  have hn := measurable_sweptNiche hU.isCompact ha haL.le
  have hR := (continuous_firstWall U a).measurable
  have hD : Measurable (fun x : ℝ =>
      (x - terminalFirstRightAbscissa U a) / Real.sin a ^ 2) := by fun_prop
  exact Measurable.ite (measurableSet_lt hn hR) hD
    (Measurable.ite (measurableSet_eq_fun hR hn) (hD.max measurable_const) measurable_const)

end AmbidextrousSofa
