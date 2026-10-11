module

public import AmbidextrousSofa.Analysis.TiltedReflectedControls
public import AmbidextrousSofa.Analysis.ReflectedExcessScalar
public import AmbidextrousSofa.Analysis.TiltedTopProjection

@[expose] public section

/-!
# Actual early companion unit curvature when the top overhang vanishes

The reflected active arc has initial height equal to the actual left
endpoint roof and initial span equal to three quarter-widths. Its first
excess crossing is constructed from its continuous momenta. The clipped
energy gives the precise reflected radius inequality, and the two exact
endpoint-height ranges stop the excess before `11/15`. Reflection then
gives unit companion curvature on the original initial prefix.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem CornerArcDynamics.ae_first_le_one_after_reflected_deadline
    {p q u v : ℝ → ℝ} {b d e : ℝ}
    (D : CornerArcDynamics p q u v 0 b) (hb : b ≤ Real.pi / 2)
    (hp0 : p 0 = e) (hq0 : q 0 = d - 1)
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 3 / 20 ≤ e) (he1 : e ≤ 3 / 4) (hqb : q b ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (11 / 15 : ℝ) b), u t ≤ 1 := by
  have hsub : Ioo (11 / 15 : ℝ) b ⊆ Ioo 0 b := Ioo_subset_Ioo (by norm_num) le_rfl
  by_cases hqstart : q 0 ≤ 1
  · exact ae_restrict_of_ae_restrict_of_subset hsub
      (D.ae_unit_of_second_le_one (by linarith) hqstart)
  obtain hunit | ⟨A, B, hA, hB, hpA, -, hqA, -, hqbefore, hquad, hout⟩ :=
    D.exists_first_excess_crossings (by linarith) (by linarith) hqb
  · exact ae_restrict_of_ae_restrict_of_subset hsub hunit
  have hAb : A ≤ b := hA.2.le.trans hB.2
  -- The energy at the first zero exceeds the threshold, so it is at most the initial energy.
  have hE := D.energy_le_max_initial ⟨hA.1.le, hAb⟩
  rw [clippedCornerEnergy, clippedCornerEnergy, hpA, hp0, hq0, max_self,
    max_eq_left (by linarith : 0 ≤ e)] at hE
  have hradius : (2 + (q A - 1)) ^ 2 ≤ d ^ 2 - e * (1 - e) := by
    rcases le_max_iff.1 hE with h | h
    · linarith [mul_pos (sub_pos.2 hqA) (by linarith : (0 : ℝ) < q A + 3)]
    · linarith
  rw [hp0, hq0] at hquad
  obtain ⟨-, hell, hend⟩ := Analysis.reflected_excess_stops_early (a := A) hd0 hd1 he0 he1
    (by linarith) hradius (by linarith [Real.pi_lt_four]) (by linarith)
  have henv := D.quadratic_excess_envelope_at_first_crossing hA.1.le hA.2 hB.2 hpA.le hqA.le
    (fun t ht => hqbefore t ⟨(hA.1.trans ht.1).le, ht.2⟩) hout (by linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hsub henv.2] with t ht hbound
  have hnot : t ∉ Icc A (A + Analysis.quadraticExcessLength (q A - 1)) := fun hmem => by
    linarith [ht.1, hmem.2]
  rw [horizontalLeakageEnvelope, indicator_of_notMem hnot] at hbound
  linarith

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_companion_unit_prefix_of_collapsed_top {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (htop : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = C) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2 - 11 / 15)),
      leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 := by
  have hC : 0 < C := by linarith
  have he := hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
    ((centered_quarter_points hl hr).2.2 ▸ haffine) hlow hhigh
  have hvalues := fullTiltedSupportQuarterPair_reflected_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hmpos hheight
  -- Unit curvature before the reflected deadline, zero density after the active arc.
  have hactive := (ae_restrict_iff' measurableSet_Ioo).mp
    ((fullTiltedSupportQuarterPair_reflected_dynamics hU hm haffine hρ hρ0 hρK heq hl hr hC
      hsmall hheight hhigh hκ).ae_first_le_one_after_reflected_deadline (d := 3 * C)
      (fullReflectedActiveEnd_bounds hm).2 hvalues.1 (by rw [hvalues.2, htop]; ring)
      (by linarith) (by linarith) he.1.le he.2.le
      (fullTiltedSupportQuarterPair_reflected_second_at_activeEnd
        hU hm haffine hρ hρ0 hρK heq hl hr hC0 hsmall))
  have hzero := (ae_restrict_iff' measurableSet_Ioo).mp
    (fullTiltedSupportQuarterPair_reflected_zero_after_active
      hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh)
  have hlate : ∀ᵐ r, r ∈ Ioo (11 / 15 : ℝ) (Real.pi / 2) →
      reflectedFirstWingDensity m ρ r ≤ 1 := by
    filter_upwards [hactive, hzero, volume.ae_ne (fullReflectedActiveEnd m)] with r ha hz hne hr
    rcases hne.lt_or_gt with hrb | hbr
    · exact ha ⟨hr.1, hrb⟩
    · exact (hz ⟨hbr, hr.2⟩).1.trans_le zero_le_one
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
    ((volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae hlate)]
    with t ht hu
  simpa only [reflectedFirstWingDensity, sub_sub_cancel] using
    hu ⟨by linarith [ht.2], by linarith [ht.1]⟩

end ActualPair

end AmbidextrousSofa
