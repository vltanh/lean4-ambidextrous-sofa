module

public import AmbidextrousSofa.Analysis.TiltedSupportControls
public import AmbidextrousSofa.Analysis.CompanionFloorShadow
public import AmbidextrousSofa.Analysis.TiltedInitialEnergy
public import AmbidextrousSofa.Measure.SupportAreaAC

@[expose] public section

/-!
# The actual initial circle and its first stopping point

The literal tilted pair has no companion source when its first momentum
is positive and its companion tangency is below the floor. Together with
the actual same-sign first-source law this determines the zero-source
circle up to the first sign or floor exit. The exit is constructed from
the first zero of a continuous minimum. Its companion momentum remains
positive, so the circle stops at the first momentum zero or the explicit
floor angle. No contact chart or supplied initial phase is used in the
final theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "D" => secondTangentPoint (F).g (F).gD
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD

/-- Coordinate calculus for both actual tangent loci, retaining the
closed endpoint representatives of the two supporting faces. -/
theorem fullTiltedSupportQuarterPair_tangent_calculus :
    AbsolutelyContinuousOnInterval (fun t => (B t).1) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (fun t => (B t).2) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (fun t => (D t).1) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (fun t => (D t).2) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        HasDerivAt (fun s => (B s).1) ((1 - ρ t) * Real.sin t) t ∧
        HasDerivAt (fun s => (B s).2) ((ρ t - 1) * Real.cos t) t ∧
        HasDerivAt (fun s => (D s).1)
          ((1 - leftCompanionWingDensity m ρ (t + Real.pi / 2)) * Real.cos t) t ∧
        HasDerivAt (fun s => (D s).2)
          ((1 - leftCompanionWingDensity m ρ (t + Real.pi / 2)) * Real.sin t) t := by
  obtain ⟨hf, hg, hfD, hgD⟩ :=
    fullTiltedSupportQuarterPair_absolutelyContinuous hU hm haffine hρ hρ0 hρK heq
  have h1 := Analysis.absolutelyContinuousOnInterval_const_real 1 0 (Real.pi / 2)
  obtain ⟨hBx, hBy⟩ := absolutelyContinuousOnInterval_supportPoint (hf.sub h1) hfD
  obtain ⟨hDx, hDy⟩ := absolutelyContinuousOnInterval_companionSupportPoint (hg.sub h1) hgD
  refine ⟨hBx, hBy, hDx, hDy, ?_⟩
  filter_upwards [fullTiltedSupportQuarterPair_ae_derivatives hU hm haffine hρ hρ0 hρK heq]
    with t ⟨hf, hg, hfD, hgD⟩
  exact ⟨(hasDerivAt_supportPoint_fst (hf.sub_const 1) hfD).congr_deriv (by ring),
    (hasDerivAt_supportPoint_snd (hf.sub_const 1) hfD).congr_deriv (by ring),
    (hasDerivAt_companionSupportPoint_fst (hg.sub_const 1) hgD).congr_deriv (by ring),
    (hasDerivAt_companionSupportPoint_snd (hg.sub_const 1) hgD).congr_deriv (by ring)⟩

/-- The cut indicator already vanishes before the middle normal. After
that angle the actual finite-source exclusion applies to the identical
original companion tangency. -/
theorem fullTiltedSupportQuarterPair_companion_zero_below_floor :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      0 < p t → (D t).2 < 0 → leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
  have hzero := (ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mp
    (hU.ae_companion_density_zero_of_positive_first_below_floor haffine hρ hρ0 hρK heq)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hzero]
    with t ht hz hp hD
  by_cases hpost : Real.arctan m < t
  · have hmatch := fullTiltedSupportQuarterPair_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le
    have hpoint := (fullTiltedSupportQuarterPair_other_points_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le).1
    rw [leftCompanionWingDensity_shift_eq_after ht.1 hpost]
    exact hz (mem_regularCornerDomain_of_after_nonneg_affine hm ht hpost)
      (by linarith only [hp, hmatch.2.2.1]) (hpoint ▸ hD)
  · refine leftCompanionWingDensity_eq_zero (le_trans ?_ (le_max_right _ _))
    unfold affineNormalAngle
    linarith only [le_of_not_gt hpost]

theorem fullTiltedSupportQuarterPair_initial_values {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hlow : capRoof U (-C) = 1 - h) :
    p 0 = capRoof U (horizontalRight U) + h ∧ q 0 = 3 * C - 1 ∧
      (D 0).2 = -h ∧ (D (Real.pi / 2)).2 = capRoof U (horizontalLeft U) := by
  obtain ⟨hf0, hg0, -, -, hfD0, hgD0, -, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  have hj : horizontalLeft U + capWidth U / 4 = -C := by unfold capWidth; rw [hl, hr]; ring
  rw [hj, hlow] at hg0
  rw [hj] at hgD0
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [supportP, supportQ, secondTangentPoint, companionSupportPoint_coordinates, hf0,
      hg0, hfD0, hgD0, hgDL, hr, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
      Real.sin_pi_div_two] <;> ring

/-- On any actual initial interval which still has positive momenta
and a companion tangency below the floor, the measured source equations
uniquely determine both momenta and the companion height. -/
theorem fullTiltedSupportQuarterPair_initial_circle_on {C h τ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hτ : τ ∈ Icc 0 (Real.pi / 2))
    (hphase : ∀ t ∈ Ioo 0 τ, 0 < p t ∧ 0 < q t ∧ (D t).2 < 0) :
    (∀ᵐ t ∂volume.restrict (Ioo 0 τ),
      ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0) ∧
      EqOn p (Analysis.initialFloorCircleP (3 * C) (capRoof U (horizontalRight U) - 1 + h))
        (Icc 0 τ) ∧
      EqOn q (Analysis.initialFloorCircleQ (3 * C) (capRoof U (horizontalRight U) - 1 + h))
        (Icc 0 τ) ∧ EqOn (fun t => (D t).2) (fun t => 1 - h - Real.cos t) (Icc 0 τ) := by
  have hsub : Ioo (0 : ℝ) τ ⊆ Ioo 0 (Real.pi / 2) := Ioo_subset_Ioo le_rfl hτ.2
  have hzero : ∀ᵐ t ∂volume.restrict (Ioo 0 τ),
      ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset hsub
        (hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight haffine hhigh
          hρ hρ0 hρK hκ heq),
      ae_restrict_of_ae_restrict_of_subset hsub
        (fullTiltedSupportQuarterPair_companion_zero_below_floor hU hm haffine hρ hρ0 hρK heq)]
      with t ht hs hv
    have hsign := hphase t ht
    exact ⟨(hs.2.2.1 hsign.1 hsign.2.1).1, hv hsign.1 hsign.2.2⟩
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hsubcc : uIcc (0 : ℝ) τ ⊆ uIcc 0 (Real.pi / 2) := uIcc_subset_uIcc_left (Icc_subset_uIcc hτ)
  have hode0 : ∀ᵐ t ∂volume.restrict (Icc 0 τ),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (p t - 1) t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hode, hzero] with t hd hz
    exact ⟨hd.1.congr_deriv (by rw [hz.1]; ring), hd.2.congr_deriv (by rw [hz.2]; ring)⟩
  obtain ⟨hp0, hq0, hD0, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  have hcircle := Analysis.eqOn_initialFloorCircle_of_zero_source hτ.1
    (hpAC.mono hsubcc) (hqAC.mono hsubcc) hode0
    (show p 0 = 1 + (capRoof U (horizontalRight U) - 1 + h) by linarith only [hp0]) hq0
  obtain ⟨-, -, -, hDy, hTD⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  obtain ⟨k, hk⟩ := ((hDy.mono hsubcc).fun_add
    Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval).const_of_ae_hasDerivAt_zero <| by
      rw [uIcc_of_le hτ.1]
      refine (ae_restrict_iff' measurableSet_Icc).1 ?_
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hTD, hzero] with t hd hz
      exact (hd.2.2.2.add (Real.hasDerivAt_cos t)).congr_deriv (by rw [hz.2]; ring)
  have hk0 := hk 0 (by simp)
  rw [hD0, Real.cos_zero] at hk0
  refine ⟨hzero, hcircle.1, hcircle.2, fun t ht => ?_⟩
  linarith only [hk t (by rwa [uIcc_of_le hτ.1]), hk0]

/-- The stopping interval is constructed from the actual cap. Positive
companion momentum cannot be the first exit: the radius exceeds two in
squared length while the first momentum has only decreased. -/
theorem fullTiltedSupportQuarterPair_exists_initial_stopping_circle {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh : 0 < h) (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s)) :
    ∃ τ ∈ Ioo 0 (Real.pi / 2),
      (∀ t ∈ Ico 0 τ, 0 < p t ∧ 0 < q t ∧ (D t).2 < 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 τ),
        ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0) ∧
      EqOn p (Analysis.initialFloorCircleP (3 * C) (capRoof U (horizontalRight U) - 1 + h))
        (Icc 0 τ) ∧
      EqOn q (Analysis.initialFloorCircleQ (3 * C) (capRoof U (horizontalRight U) - 1 + h))
        (Icc 0 τ) ∧ EqOn (fun t => (D t).2) (fun t => 1 - h - Real.cos t) (Icc 0 τ) ∧
      0 < q τ ∧ (p τ = 0 ∨ τ = Analysis.initialFloorAngle h) := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  obtain ⟨-, -, -, hDy, -⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  obtain ⟨hp0, hq0, hD0, hDL⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  have heR : 0 ≤ capRoof U (horizontalRight U) :=
    capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1) _
  have heL : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1) _
  -- `τ` is the first exit from the phase where `p`, `q` and `-(D t).2` are all positive
  obtain ⟨τ, hτ, hzτ, hzbefore⟩ := exists_first_level_crossing
    (f := fun t => min (p t) (min (q t) (-(D t).2))) hL
    (by simpa only [uIcc_of_le hL.le] using
      hpAC.continuousOn.inf (hqAC.continuousOn.inf hDy.fun_neg.continuousOn))
    (by simp only [hp0, hq0, hD0, neg_neg, lt_min_iff]; exact ⟨by linarith, by linarith, hh⟩)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (by rw [hDL]; linarith)))
  have hphase : ∀ t ∈ Ico (0 : ℝ) τ, 0 < p t ∧ 0 < q t ∧ (D t).2 < 0 := fun t ht => by
    simpa only [lt_min_iff, neg_pos] using hzbefore t ht
  obtain ⟨hpτ, hqτ, hDτ⟩ : 0 ≤ p τ ∧ 0 ≤ q τ ∧ (D τ).2 ≤ 0 := by
    simpa only [le_min_iff, neg_nonneg] using hzτ.symm.le
  obtain ⟨hzero, hpcircle, hqcircle, hDcircle⟩ := fullTiltedSupportQuarterPair_initial_circle_on
    hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC]) hmpos hsmall
    hheight hhigh hlow hκ ⟨hτ.1.le, hτ.2⟩ (fun t ht => hphase t ⟨ht.1.le, ht.2⟩)
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.1.le, le_rfl⟩
  -- `p` decreases on `[0, τ]`, where `q` is positive
  have hpdecrease : p τ ≤ p 0 := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
    (hpAC.mono (uIcc_subset_uIcc_left (Icc_subset_uIcc ⟨hτ.1.le, hτ.2⟩))) hτ.1.le (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo le_rfl hτ.2) hode, hzero] with t ht hd hz
      rw [hd.1.deriv, hz.1]
      linarith only [(hphase t ⟨ht.1.le, ht.2⟩).2.1]) hτmem
  set b := capRoof U (horizontalRight U) - 1 + h
  have hradius := Analysis.initialFloorCircle_radius (3 * C) b τ
  rw [← hpcircle hτmem, ← hqcircle hτmem] at hradius
  have hqpositive : 0 < q τ := by
    refine hqτ.lt_of_ne fun hq => ?_
    rw [← hq] at hradius
    have hsquare : (p τ - 1) ^ 2 ≤ 1 + b ^ 2 := by
      rcases le_total (p τ) 1 with hp1 | hp1
      · nlinarith only [mul_nonneg hpτ (sub_nonneg.mpr hp1), hpτ, sq_nonneg b]
      · nlinarith only [mul_nonneg (show 0 ≤ b - (p τ - 1) by linarith only [hpdecrease, hp0])
          (show 0 ≤ b + (p τ - 1) by linarith only [hpdecrease, hp0, hp1])]
    nlinarith only [hradius, hsquare, mul_pos (show 0 < 3 * C - 3 / 2 by linarith only [hC])
      (show 0 < 3 * C + 3 / 2 by linarith only [hC])]
  have hτL : τ < Real.pi / 2 := by
    refine hτ.2.lt_of_ne fun heqτ => ?_
    have hpL := hpcircle hτmem
    simp only [heqτ, Analysis.initialFloorCircleP, Real.cos_pi_div_two,
      Real.sin_pi_div_two] at hpL hpτ
    linarith only [hpL, hpτ, hC]
  refine ⟨τ, ⟨hτ.1, hτL⟩, hphase, hzero, hpcircle, hqcircle, hDcircle, hqpositive, ?_⟩
  refine or_iff_not_imp_left.2 fun hpzero => ?_
  -- otherwise the companion tangency has reached the floor
  have hDzero : (D τ).2 = 0 := hDτ.antisymm <| not_lt.1 fun hneg =>
    (lt_min (lt_of_le_of_ne hpτ (Ne.symm hpzero)) (lt_min hqpositive (neg_pos.2 hneg))).ne' hzτ
  have hcos : Real.cos τ = 1 - h := by linarith only [hDcircle hτmem, hDzero]
  rw [Analysis.initialFloorAngle, ← hcos, Real.arccos_cos hτ.1.le (by linarith [Real.pi_pos])]

end ActualPair

end AmbidextrousSofa
