import AmbidextrousSofa.Analysis.CompanionEndpointEnergy
import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
import AmbidextrousSofa.Analysis.HorizontalLeakageScalar
import AmbidextrousSofa.Analysis.CapReflection

/-!
# Actual unit curvature after an explicit horizontal orientation

The box-wall endpoint estimate and endpoint stationarity supply one
good endpoint. If necessary the cap is reflected before its density
is constructed. The full objective, maximality, width and horizontal
middle roof are preserved by this explicit geometric operation.
The terminal energy and one-good-quarter propagation then prove unit
curvature for both quarters of that same oriented cap.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.horizontal_middle_roof_mirror
    {U : Set Plane} (hU : IsDownwardCap U)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    ∀ x ∈ middleHalfInterval (horizontalLeft (horizontalMirror U))
      (horizontalRight (horizontalMirror U)), capRoof (horizontalMirror U) x = 1 := by
  intro x hx
  rw [capRoof_horizontalMirror]
  apply hmiddle
  unfold middleHalfInterval at hx ⊢
  rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem IsFullCapMaximizer.exists_horizontal_orientation_left_endpoint_criterion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 8571 / 12500) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    ∃ V : Set Plane, (V = U ∨ V = horizontalMirror U) ∧ IsFullCapMaximizer V ∧
      horizontalLeft V = -2 * C ∧ horizontalRight V = 2 * C ∧
      capHeight V = 1 ∧ capWidth V = capWidth U ∧
      capScore V (Real.pi / 2) = capScore U (Real.pi / 2) ∧
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = 1) ∧
      (3 * capWidth V / 4) ^ 2 ≤
        4 + capRoof V (horizontalLeft V) * (1 - capRoof V (horizontalLeft V)) := by
  have hw : capWidth U = 4 * C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hscalar := horizontal_energy_threshold_of_width_le hC0 hC1
  have hprod := hU.horizontal_endpoint_product_one_ge hl hr hC0
    (by linarith : C ≤ 1) hheight hmiddle
  rcases hprod with hR | hL
  · have hright : (3 * capWidth U / 4) ^ 2 ≤
        4 + capRoof U (horizontalRight U) * (1 - capRoof U (horizontalRight U)) := by
      rw [hw]
      nlinarith only [hscalar, hR]
    refine ⟨horizontalMirror U, Or.inr rfl, hU.horizontalMirror, ?_, ?_, ?_,
      capWidth_horizontalMirror hU.isCap, capScore_horizontalMirror hU.isCap,
      hU.isCap.horizontal_middle_roof_mirror hmiddle, ?_⟩
    · rw [horizontalLeft_horizontalMirror hU.isCap, hr]
      ring
    · rw [horizontalRight_horizontalMirror hU.isCap, hl]
      ring
    · rw [capHeight_horizontalMirror, hheight]
    · simpa only [capWidth_horizontalMirror hU.isCap,
        horizontalLeft_horizontalMirror hU.isCap, capRoof_horizontalMirror, neg_neg] using hright
  · have hleft : (3 * capWidth U / 4) ^ 2 ≤
        4 + capRoof U (horizontalLeft U) * (1 - capRoof U (horizontalLeft U)) := by
      rw [hw]
      nlinarith only [hscalar, hL]
    exact ⟨U, Or.inl rfl, hU, hl, hr, hheight, rfl, rfl, hmiddle, hleft⟩

theorem ae_density_le_one_on_regularCurvatureDomain_of_both_quarters
    {ρ : ℝ → ℝ}
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) :
    ∀ᵐ t ∂volume.restrict (regularCurvatureDomain 0), ρ t ≤ 1 := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioo).mp hunit
  have hshift := (measurePreserving_add_right volume (-(Real.pi / 2))).quasiMeasurePreserving.ae
    hglobal
  apply (ae_restrict_iff' (measurableSet_regularCurvatureDomain 0)).mpr
  filter_upwards [hglobal, hshift] with t ht hs
  intro hmem
  have hm := mem_regularCurvatureDomain_iff.mp hmem
  rcases lt_or_gt_of_ne hm.2.2.1 with hleft | hright
  · exact (ht ⟨hm.1, hleft⟩).1
  · have hquarter : t + -(Real.pi / 2) ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [hm.2.1]
    simpa only [add_assoc, neg_add_cancel, add_zero] using (hs hquarter).2

/-- Clipping changes the representative on a null set only. The result
is still the literal upper-curvature density, with its actual sharp
source bound and the convenient global representative bound `0≤ρ≤1`. -/
theorem exists_unit_density_of_both_quarters
    {U : Set Plane} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) :
    ∃ σ : ℝ → ℝ, Measurable σ ∧
      (∀ t, 0 ≤ σ t ∧ σ t ≤ 1 ∧ σ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (upperCurvature U).restrict (regularCurvatureDomain 0) =
        (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (σ t)) := by
  refine ⟨fun t => min (ρ t) 1, hρ.min measurable_const, ?_, ?_⟩
  · intro t
    exact ⟨le_min (hρ0 t) (by norm_num), min_le_right _ _,
      (min_le_left _ _).trans (hκ t)⟩
  · rw [heq]
    apply withDensity_congr_ae
    filter_upwards [ae_density_le_one_on_regularCurvatureDomain_of_both_quarters hunit]
      with t ht
    rw [min_eq_left ht]

/-- This is a geometric existence statement for an actual orientation
of the cap, not a reflection-transport claim for an unproved density.
Every law for the chosen density is supplied by that chosen maximizer. -/
theorem IsFullCapMaximizer.exists_horizontal_oriented_unit_density_of_width_le
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 8571 / 12500) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    ∃ V : Set Plane, (V = U ∨ V = horizontalMirror U) ∧ IsFullCapMaximizer V ∧
      horizontalLeft V = -2 * C ∧ horizontalRight V = 2 * C ∧
      capHeight V = 1 ∧ capWidth V = capWidth U ∧
      capScore V (Real.pi / 2) = capScore U (Real.pi / 2) ∧
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = 1) ∧
      ∃ ρ : ℝ → ℝ, Measurable ρ ∧
        (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1 ∧ ρ t ≤ sourceKappa (upperCornerVelocity V t)) ∧
        (upperCurvature V).restrict (regularCurvatureDomain 0) =
          (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨V, hchoice, hV, hlV, hrV, hheightV, hwidthV, hscoreV, hmiddleV, henergy⟩ :=
    hU.exists_horizontal_orientation_left_endpoint_criterion hl hr hC0 hC1 hheight hmiddle
  obtain ⟨ρ, hρ, hb, hC, heq, _⟩ :=
    hV.horizontal_curvature_density_corner_controls hheightV hmiddleV
  have hunit := hV.ae_both_density_le_one_of_left_endpoint_criterion hheightV hmiddleV
    hρ (fun t => (hb t).1) hC (fun t => (hb t).2) heq henergy
  obtain ⟨σ, hσ, hσb, hσeq⟩ := exists_unit_density_of_both_quarters hρ
    (fun t => (hb t).1) (fun t => (hb t).2) heq hunit
  exact ⟨V, hchoice, hV, hlV, hrV, hheightV, hwidthV, hscoreV, hmiddleV,
    σ, hσ, hσb, hσeq⟩

end AmbidextrousSofa
