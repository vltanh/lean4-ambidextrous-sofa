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
  have hsub : Ioo (11 / 15 : ℝ) b ⊆ Ioo (0 : ℝ) b :=
    Ioo_subset_Ioo (by norm_num) le_rfl
  by_cases hqstart : q 0 ≤ 1
  · apply ae_restrict_of_ae_restrict_of_subset hsub
    exact D.ae_unit_of_second_le_one (by rw [hp0]; linarith only [he1]) hqstart
  · have hpstart : 0 < p 0 := by rw [hp0]; linarith only [he0]
    rcases D.exists_first_excess_crossings hpstart (lt_of_not_ge hqstart) hqb with
      hunit | hcross
    · exact ae_restrict_of_ae_restrict_of_subset hsub hunit
    · obtain ⟨A, B, hA, hB, hpA, _hqB, hqA, _hpbefore, hqbefore, hquad, hout⟩ := hcross
      have hAmem : A ∈ Icc (0 : ℝ) b := ⟨hA.1.le, hA.2.le.trans hB.2⟩
      have hEA : clippedCornerEnergy p q A = 1 / 4 + (q A + 1) ^ 2 := by
        unfold clippedCornerEnergy
        rw [hpA]
        norm_num
      have hEAhigh : 17 / 4 < clippedCornerEnergy p q A := by
        rw [hEA]
        have hprod := mul_pos (show 0 < q A - 1 by linarith only [hqA])
          (show 0 < q A + 3 by linarith only [hqA])
        nlinarith only [hprod]
      have hdecrease : clippedCornerEnergy p q A ≤ clippedCornerEnergy p q 0 := by
        rcases le_max_iff.mp (D.energy_le_max_initial hAmem) with hbad | hgood
        · exact False.elim (not_le_of_gt hEAhigh hbad)
        · exact hgood
      have hE0 : clippedCornerEnergy p q 0 = (e - 1 / 2) ^ 2 + d ^ 2 := by
        unfold clippedCornerEnergy
        rw [hp0, hq0, max_eq_left (show 0 ≤ e by linarith only [he0])]
        ring
      have hradius : (2 + (q A - 1)) ^ 2 ≤ d ^ 2 - e * (1 - e) := by
        rw [hEA, hE0] at hdecrease
        nlinarith only [hdecrease]
      have hquad' : 0 ≤ e - d * A + A ^ 2 / 2 := by
        rw [hp0, hq0] at hquad
        nlinarith only [hquad]
      have hAd : A ≤ d := by
        have hAL := hAmem.2.trans hb
        linarith only [hAL, hd0, Real.pi_lt_four]
      obtain ⟨_hε, hell, hend⟩ := Analysis.reflected_excess_stops_early
        hd0 hd1 he0 he1 (by linarith only [hqA]) hradius hAd hquad'
      have henv := D.quadratic_excess_envelope_at_first_crossing
        hA.1.le hA.2 hB.2 hpA.le hqA.le
        (fun t ht => hqbefore t ⟨(hA.1.trans ht.1).le, ht.2⟩) hout
        (by linarith only [hell])
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae_restrict_of_subset hsub henv.2] with t ht hbound
      have hnot : t ∉ Icc A (A + Analysis.quadraticExcessLength (q A - 1)) := by
        intro hmem
        linarith only [ht.1, hmem.2, hend]
      rw [horizontalLeakageEnvelope, indicator_of_notMem hnot] at hbound
      linarith only [hbound]

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq

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
  have hC : 0 < C := by linarith only [hC0]
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have he := hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
    haff hlow hhigh
  have D := fullTiltedSupportQuarterPair_reflected_dynamics
    hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh hκ
  have hvalues := fullTiltedSupportQuarterPair_reflected_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hmpos hheight
  have hq0 : reflectedSupportQ F 0 = 3 * C - 1 := by
    rw [hvalues.2, htop]
    ring
  have hactive := D.ae_first_le_one_after_reflected_deadline
    (fullReflectedActiveEnd_bounds hm).2 hvalues.1 hq0
    (by linarith only [hC0]) (by linarith only [hC1]) he.1.le he.2.le
    (fullTiltedSupportQuarterPair_reflected_second_at_activeEnd
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hsmall)
  have hactiveGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hactive
  have hzeroGlobal := (ae_restrict_iff' measurableSet_Ioo).mp
    (fullTiltedSupportQuarterPair_reflected_zero_after_active
      hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh)
  have hlate : ∀ᵐ r ∂volume.restrict (Ioo (11 / 15 : ℝ) (Real.pi / 2)),
      reflectedFirstWingDensity m ρ r ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hactiveGlobal, ae_restrict_of_ae hzeroGlobal,
      ae_restrict_of_ae (volume.ae_ne (fullReflectedActiveEnd m))] with r hr ha hz hne
    by_cases hrb : r < fullReflectedActiveEnd m
    · exact ha ⟨hr.1, hrb⟩
    · have hbr : fullReflectedActiveEnd m < r :=
        lt_of_le_of_ne (le_of_not_gt hrb) (Ne.symm hne)
      rw [(hz ⟨hbr, hr.2⟩).1]
      norm_num
  have hlateGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hlate
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
    hlateGlobal
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift]
    with t ht hu
  have hrt : Real.pi / 2 - t ∈ Ioo (11 / 15 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith only [ht.1, ht.2]
  have h := hu hrt
  simpa only [reflectedFirstWingDensity, sub_sub_cancel] using h

end ActualPair

end AmbidextrousSofa
