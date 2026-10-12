module

public import AmbidextrousSofa.Analysis.CompanionEndpointEnergy
public import AmbidextrousSofa.Analysis.HorizontalLeakageBound
public import AmbidextrousSofa.Analysis.HorizontalLeakageScalar
public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

/-!
# Unit curvature from the dry-endpoint energy test

For widths at most `2/3`, the endpoint energy criterion holds for any
height in the unit strip. For larger widths, the middle endpoints are
dry and stationarity gives axis height one half. The intrinsic width
`√17/6` is exactly the energy threshold for this height. Both quarters
are controlled on the original cap.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- Clipping changes the representative on a null set only. The result
is still the literal upper-curvature density, with its actual sharp
source bound and the convenient global representative bound `0≤ρ≤1`. -/
theorem IsFullCapMaximizer.exists_unit_density_of_left_endpoint_criterion
    {V : Set Plane} (hV : IsFullCapMaximizer V) (hheight : capHeight V = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = 1)
    (henergy : (3 * capWidth V / 4) ^ 2 ≤
      4 + capRoof V (horizontalLeft V) * (1 - capRoof V (horizontalLeft V))) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1 ∧ ρ t ≤ sourceKappa (upperCornerVelocity V t)) ∧
      (upperCurvature V).restrict (regularCurvatureDomain 0) =
        (volume.restrict (regularCurvatureDomain 0)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨ρ, hρ, hb, hC, heq, -⟩ :=
    hV.horizontal_curvature_density_corner_controls hheight hmiddle
  have hunit := (ae_restrict_iff' measurableSet_Ioo).mp
    (hV.ae_both_density_le_one_of_left_endpoint_criterion hheight hmiddle hρ (fun t => (hb t).1)
      hC (fun t => (hb t).2) heq henergy)
  have hshift :=
    (measurePreserving_add_right volume (-(Real.pi / 2))).quasiMeasurePreserving.ae hunit
  refine ⟨fun t => min (ρ t) 1, hρ.min measurable_const, fun t => ⟨le_min (hb t).1 zero_le_one,
    min_le_right _ _, (min_le_left _ _).trans (hb t).2⟩, heq.trans (withDensity_congr_ae ?_)⟩
  filter_upwards [ae_restrict_mem (measurableSet_regularCurvatureDomain 0),
    ae_restrict_of_ae hunit, ae_restrict_of_ae hshift] with t hmem ht hs
  obtain ⟨h0, hπ, hne, -⟩ := mem_regularCurvatureDomain_iff.mp hmem
  rw [min_eq_left]
  rcases hne.lt_or_gt with hlt | hgt
  · exact (ht ⟨h0, hlt⟩).1
  · simpa using (hs ⟨by linarith, by linarith⟩).2

/-- The original cap supplies both unit-curvature quarters; the existence
statement retains the orientation choice used by its callers. -/
theorem IsFullCapMaximizer.exists_horizontal_oriented_unit_density_of_width_le
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ horizontalEnergyWidth) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    ∃ V : Set Plane, (V = U ∨ V = AmbidextrousSofa.horizontalMirror U) ∧ IsFullCapMaximizer V ∧
      horizontalLeft V = -2 * C ∧ horizontalRight V = 2 * C ∧
      capHeight V = 1 ∧ capWidth V = capWidth U ∧
      capScore V (Real.pi / 2) = capScore U (Real.pi / 2) ∧
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = 1) ∧
      ∃ ρ : ℝ → ℝ, Measurable ρ ∧
        (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1 ∧ ρ t ≤ sourceKappa (upperCornerVelocity V t)) ∧
        (upperCurvature V).restrict (regularCurvatureDomain 0) =
          (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hw : capWidth U = 4 * C := by rw [capWidth, hl, hr]; ring
  have henergy : (3 * capWidth U / 4) ^ 2 ≤
      4 + capRoof U (horizontalLeft U) * (1 - capRoof U (horizontalLeft U)) := by
    rw [hw]
    rcases le_or_gt C (2 / 3) with hsmall | hlarge
    · have he0 := capRoof_nonneg hU.isCap.isCompact (fun p hp =>
        (hU.isCap.inStrip hp).1) (horizontalLeft U)
      have he1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (horizontalLeft U)
      nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
    · rw [(hU.horizontal_axis_heights_eq_half hl hr hheight hmiddle hlarge).2]
      nlinarith only [horizontal_energy_of_intrinsic_width hC0 hC1]
  exact ⟨U, Or.inl rfl, hU, hl, hr, hheight, rfl, rfl, hmiddle,
    hU.exists_unit_density_of_left_endpoint_criterion hheight hmiddle henergy⟩

end AmbidextrousSofa
