module

public import AmbidextrousSofa.Analysis.FirstUnitCrossings
public import AmbidextrousSofa.Analysis.FirstUnitTopOverhang
public import AmbidextrousSofa.Analysis.TiltedLateExcess

@[expose] public section

/-!
# The actual first-unit tilted corner phases

The actual support pair follows the corner dynamics, and the curvature
vanishes in the shadows of its two equal-sign sectors. All crossing data
below are constructed from the literal support pair. The original sharp
source bounds, the surrogate's short initial arm exception, positive
endpoint pressures, and exact top projection supply the hypotheses of the
absolutely continuous crossing argument.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

/-- The corner dynamics of the actual pair and the shadows of its equal-sign sectors. -/
theorem FirstUnitSetting.corner_dynamics {C h : ℝ} (P : FirstUnitSetting U m ρ C h) :
    CornerArcDynamics p q ρ v 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        (0 < p t → 0 < q t → ρ t = 0) ∧ (p t < 0 → q t < 0 → v t = 0 ∧ ρ t ≤ 1 / 2) :=
  ⟨fullTiltedSupportQuarterPair_cornerArcDynamics hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.C_pos
      P.hsmall P.hheight P.hhigh P.hκ,
    (hU.fullTiltedSupportQuarterPair_source_controls P.hl P.hr P.C_pos hm P.hsmall P.hheight
      haffine P.hhigh hρ hρ0 hρK P.hκ heq).mono fun _ hs =>
        ⟨fun hp hq => (hs.2.2.1 hp hq).1, hs.2.2.2⟩⟩

theorem fullTiltedSupportQuarterPair_exists_strict_sign_phases {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 1 / 3) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∃ α η, StrictCornerSignPhases p q (Real.pi / 2) α η := by
  have P : FirstUnitSetting U m ρ C h :=
    ⟨hl, hr, hC0, hC1, hh0, hh1, hmpos, hsmall, hheight, hlow, hhigh, hκ, hunit⟩
  obtain ⟨Dyn, hshadow⟩ := P.corner_dynamics hU hm haffine hρ hρ0 hρK heq
  obtain ⟨hp0, hq0, -, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  obtain ⟨-, -, -, hpL, hqL⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  have htop := (P.top_overhang hU hm haffine hρ hρ0 hρK heq).1
  have he := hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩
  have hδ0 : 0 ≤ Real.arctan m := Real.arctan_nonneg.mpr hm
  refine Dyn.exists_strict_sign_phases (by positivity) hδ0
    (by rw [hq0]; linarith only [Real.arctan_le_self hm, hsmall, hC0])
    (ContinuousOn.le_on_Icc_of_ae_le_on_Ioo (Dyn.continuousOn.1.mono (Icc_subset_Icc hδ0 le_rfl))
      (Real.arctan_lt_pi_div_two m) ?_)
    (by rw [hp0]; linarith only [he.1, hh0]) (by rw [hpL]; linarith only [htop, hC0])
    (by rw [hqL]; linarith only [he.2]) (by rw [hq0]; nlinarith only [hC0, sq_nonneg (p 0 - 1)])
    (hshadow.mono fun _ hs => hs.2)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact fullTiltedSupportQuarterPair_p_le_one_after_affine
    hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1.le, ht.2⟩ ht.1.le

end ActualPair

end AmbidextrousSofa
