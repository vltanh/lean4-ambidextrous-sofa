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
  have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 (Real.pi / 2) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  obtain ⟨hBx, hBy⟩ := absolutelyContinuousOnInterval_supportPoint (hf.sub h1) hfD
  obtain ⟨hDx, hDy⟩ := absolutelyContinuousOnInterval_companionSupportPoint (hg.sub h1) hgD
  refine ⟨hBx, hBy, hDx, hDy, ?_⟩
  filter_upwards [fullTiltedSupportQuarterPair_ae_derivatives hU hm haffine hρ hρ0 hρK heq]
    with t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hasDerivAt_supportPoint_fst (ht.1.sub_const 1) ht.2.2.1).congr_deriv (by ring)
  · exact (hasDerivAt_supportPoint_snd (ht.1.sub_const 1) ht.2.2.1).congr_deriv (by ring)
  · exact (hasDerivAt_companionSupportPoint_fst (ht.2.1.sub_const 1) ht.2.2.2).congr_deriv
      (by ring)
  · exact (hasDerivAt_companionSupportPoint_snd (ht.2.1.sub_const 1) ht.2.2.2).congr_deriv
      (by ring)

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
  · have hreg := mem_regularCornerDomain_of_after_nonneg_affine hm ht hpost
    have hmatch := fullTiltedSupportQuarterPair_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le
    have hpoint := (fullTiltedSupportQuarterPair_other_points_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le).1
    rw [leftCompanionWingDensity_shift_eq_after ht.1 hpost]
    apply hz hreg
    · rw [hmatch.2.2.1] at hp
      linarith only [hp]
    · simpa only [hpoint] using hD
  · apply leftCompanionWingDensity_eq_zero
    apply le_trans _ (le_max_right _ _)
    unfold affineNormalAngle
    linarith only [le_of_not_gt hpost]

theorem fullTiltedSupportQuarterPair_initial_values {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hlow : capRoof U (-C) = 1 - h) :
    p 0 = capRoof U (horizontalRight U) + h ∧ q 0 = 3 * C - 1 ∧
      (D 0).2 = -h ∧ (D (Real.pi / 2)).2 = capRoof U (horizontalLeft U) := by
  obtain ⟨hf0, hg0, _hfL, _hgL, hfD0, hgD0, _hfDL, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  have hj : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  rw [hj, hlow] at hg0
  rw [hj] at hgD0
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [supportP]
    rw [hfD0, hg0]
    ring
  · dsimp only [supportQ]
    rw [hgD0, hf0, hr]
    ring
  · rw [secondTangentPoint, companionSupportPoint_coordinates]
    change ((F).g 0 - 1) * Real.cos 0 - (F).gD 0 * Real.sin 0 = -h
    rw [hg0, Real.cos_zero, Real.sin_zero]
    ring
  · rw [secondTangentPoint, companionSupportPoint_coordinates]
    change ((F).g (Real.pi / 2) - 1) * Real.cos (Real.pi / 2) -
      (F).gD (Real.pi / 2) * Real.sin (Real.pi / 2) = _
    rw [hgDL, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

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
  have hsource := hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall
    hheight haffine hhigh hρ hρ0 hρK hκ heq
  have hzero : ∀ᵐ t ∂volume.restrict (Ioo 0 τ),
      ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hsource,
      ae_restrict_of_ae_restrict_of_subset hsub
        (fullTiltedSupportQuarterPair_companion_zero_below_floor hU hm haffine hρ hρ0 hρK heq)]
      with t ht hs hv
    have hsign := hphase t ht
    exact ⟨(hs.2.2.1 hsign.1 hsign.2.1).1, hv hsign.1 hsign.2.2⟩
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hsubcc : uIcc (0 : ℝ) τ ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le hτ.1, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact Icc_subset_Icc le_rfl hτ.2
  have hode0 : ∀ᵐ t ∂volume.restrict (Icc 0 τ),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (p t - 1) t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hode, hzero] with t hd hz
    constructor
    · exact hd.1.congr_deriv (by rw [hz.1]; ring)
    · exact hd.2.congr_deriv (by rw [hz.2]; ring)
  obtain ⟨hp0, hq0, hD0, _hDL⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  have hcircle := Analysis.eqOn_initialFloorCircle_of_zero_source hτ.1
    (hpAC.mono hsubcc) (hqAC.mono hsubcc) hode0
    (show p 0 = 1 + (capRoof U (horizontalRight U) - 1 + h) by linarith only [hp0]) hq0
  obtain ⟨_hBx, _hBy, _hDx, hDy, hTD⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hcos : AbsolutelyContinuousOnInterval Real.cos 0 τ :=
    Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval
  have hE : AbsolutelyContinuousOnInterval (fun t => (D t).2 + Real.cos t) 0 τ :=
    (hDy.mono hsubcc).add hcos
  have hED : ∀ᵐ t ∂volume.restrict (Icc 0 τ),
      HasDerivAt (fun s => (D s).2 + Real.cos s) 0 t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hTD, hzero] with t hd hz
    exact (hd.2.2.2.add (Real.hasDerivAt_cos t)).congr_deriv (by rw [hz.2]; ring)
  have hED' : ∀ᵐ t ∂volume, t ∈ uIcc 0 τ →
      HasDerivAt (fun s => (D s).2 + Real.cos s) 0 t := by
    rw [uIcc_of_le hτ.1]
    exact (ae_restrict_iff' measurableSet_Icc).mp hED
  obtain ⟨k, hk⟩ := hE.const_of_ae_hasDerivAt_zero hED'
  have hk0 := hk 0 (by simp)
  rw [hD0, Real.cos_zero] at hk0
  refine ⟨hzero, hcircle.1, hcircle.2, ?_⟩
  intro t ht
  have hkt := hk t (by simpa only [uIcc_of_le hτ.1] using ht)
  linarith only [hkt, hk0]

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
  let L : ℝ := Real.pi / 2
  have hL : 0 < L := by dsimp only [L]; positivity
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  obtain ⟨_hBx, _hBy, _hDx, hDy, _hTD⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  obtain ⟨hp0, hq0, hD0, hDL⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  have heR : 0 ≤ capRoof U (horizontalRight U) :=
    capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1) _
  have heL : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1) _
  let z : ℝ → ℝ := fun t => min (p t) (min (q t) (-(D t).2))
  have hzcont : ContinuousOn z (Icc 0 L) := by
    have h := hpAC.continuousOn.inf (hqAC.continuousOn.inf hDy.continuousOn.neg)
    rw [uIcc_of_le hL.le] at h
    exact h
  have hz0 : 0 < z 0 := by
    dsimp only [z]
    rw [hp0, hq0, hD0, neg_neg]
    exact lt_min (by linarith only [heR, hh]) (lt_min (by linarith only [hC]) hh)
  have hzL : z L ≤ 0 := by
    have hle : z L ≤ -(D L).2 := (min_le_right _ _).trans (min_le_right _ _)
    rw [hDL] at hle
    linarith only [hle, heL]
  obtain ⟨τ, hτ, hzτ, hzbefore⟩ := exists_first_level_crossing hL hzcont hz0 hzL
  have hphase : ∀ t ∈ Ico (0 : ℝ) τ, 0 < p t ∧ 0 < q t ∧ (D t).2 < 0 := by
    intro t ht
    have h := lt_min_iff.mp (hzbefore t ht)
    exact ⟨h.1, (lt_min_iff.mp h.2).1, neg_pos.mp (lt_min_iff.mp h.2).2⟩
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.1.le, le_rfl⟩
  have hpτ : 0 ≤ p τ := by
    calc
      0 = z τ := hzτ.symm
      _ ≤ p τ := min_le_left _ _
  have hqτ : 0 ≤ q τ := by
    calc
      0 = z τ := hzτ.symm
      _ ≤ q τ := (min_le_right _ _).trans (min_le_left _ _)
  have hDτ : (D τ).2 ≤ 0 := by
    have hle : 0 ≤ -(D τ).2 := by
      calc
        0 = z τ := hzτ.symm
        _ ≤ -(D τ).2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hle]
  obtain ⟨hzero, hpcircle, hqcircle, hDcircle⟩ := fullTiltedSupportQuarterPair_initial_circle_on
    hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC]) hmpos hsmall
    hheight hhigh hlow hκ ⟨hτ.1.le, hτ.2⟩
    (fun t ht => hphase t ⟨ht.1.le, ht.2⟩)
  have hsub : Ioo (0 : ℝ) τ ⊆ Ioo 0 L := Ioo_subset_Ioo le_rfl hτ.2
  have hpτAC : AbsolutelyContinuousOnInterval p 0 τ := hpAC.mono (by
    rw [uIcc_of_le hτ.1.le, uIcc_of_le hL.le]
    exact Icc_subset_Icc le_rfl hτ.2)
  have hpderiv : ∀ᵐ t ∂volume.restrict (Ioo 0 τ), deriv p t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hode, hzero] with t ht hd hz
    rw [hd.1.deriv, hz.1]
    have hqt := (hphase t ⟨ht.1.le, ht.2⟩).2.1
    linarith only [hqt]
  have hpdecrease : p τ ≤ p 0 :=
    absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos hpτAC hτ.1.le hpderiv hτmem
  let b : ℝ := capRoof U (horizontalRight U) - 1 + h
  have hpinitial : p 0 = 1 + b := by dsimp only [b]; linarith only [hp0]
  have hradius : (p τ - 1) ^ 2 + (q τ + 1) ^ 2 = (3 * C) ^ 2 + b ^ 2 := by
    rw [hpcircle hτmem, hqcircle hτmem]
    exact Analysis.initialFloorCircle_radius (3 * C) b τ
  have hd : 2 < (3 * C) ^ 2 := by
    have hprod := mul_pos (show 0 < 3 * C - 3 / 2 by linarith only [hC])
      (show 0 < 3 * C + 3 / 2 by linarith only [hC])
    nlinarith only [hprod]
  have hqpositive : 0 < q τ := by
    apply lt_of_le_of_ne hqτ
    intro hqzero
    have hqeq : q τ = 0 := hqzero.symm
    have hsquare : (p τ - 1) ^ 2 ≤ 1 + b ^ 2 := by
      by_cases hpone : p τ ≤ 1
      · have hprod := mul_nonneg hpτ (sub_nonneg.mpr hpone)
        nlinarith only [hprod, hpτ, sq_nonneg b]
      · have hpg : 1 < p τ := lt_of_not_ge hpone
        have hb : p τ - 1 ≤ b := by linarith only [hpdecrease, hpinitial]
        have hprod := mul_nonneg (sub_nonneg.mpr hb)
          (show 0 ≤ b + (p τ - 1) by linarith only [hb, hpg])
        nlinarith only [hprod]
    rw [hqeq] at hradius
    nlinarith only [hradius, hsquare, hd]
  have hτL : τ < L := by
    apply lt_of_le_of_ne hτ.2
    intro heqτ
    have hpL := hpcircle hτmem
    simp only [heqτ, L, Analysis.initialFloorCircleP, Real.cos_pi_div_two,
      Real.sin_pi_div_two, mul_zero, mul_one, add_zero] at hpL
    rw [heqτ] at hpτ
    linarith only [hpL, hpτ, hC]
  have hstop : p τ = 0 ∨ τ = Analysis.initialFloorAngle h := by
    by_cases hpzero : p τ = 0
    · exact Or.inl hpzero
    · have hppos : 0 < p τ := lt_of_le_of_ne hpτ (Ne.symm hpzero)
      have hDzero : (D τ).2 = 0 := by
        by_contra hnot
        have hDnegative : (D τ).2 < 0 := lt_of_le_of_ne hDτ hnot
        have hzpositive : 0 < z τ := lt_min hppos (lt_min hqpositive (neg_pos.mpr hDnegative))
        linarith only [hzτ, hzpositive]
      have hcos : Real.cos τ = 1 - h := by
        have hc := hDcircle hτmem
        linarith only [hc, hDzero]
      right
      rw [Analysis.initialFloorAngle, ← hcos, Real.arccos_cos hτ.1.le
        (show τ ≤ Real.pi by dsimp only [L] at hτL; linarith only [hτL, Real.pi_pos])]
  exact ⟨τ, ⟨hτ.1, hτL⟩, hphase, hzero, hpcircle, hqcircle, hDcircle, hqpositive, hstop⟩

end ActualPair

end AmbidextrousSofa
