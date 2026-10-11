module

public import AmbidextrousSofa.Analysis.CompanionEndpointEnergy
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.HorizontalLeakageScalar
public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

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

/-- This is a geometric existence statement for an actual orientation
of the cap, not a reflection-transport claim for an unproved density.
Every law for the chosen density is supplied by that chosen maximizer. -/
theorem IsFullCapMaximizer.exists_horizontal_oriented_unit_density_of_width_le
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 8571 / 12500) (hheight : capHeight U = 1)
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
  have hscalar := horizontal_energy_threshold_of_width_le hC0 hC1
  rcases hU.horizontal_endpoint_product_one_ge hl hr hC0 (by linarith) hheight hmiddle with hR | hL
  · have hl' := horizontalLeft_horizontalMirror hU.isCap
    have hr' := horizontalRight_horizontalMirror hU.isCap
    have hheight' : capHeight (AmbidextrousSofa.horizontalMirror U) = 1 := by
      rw [capHeight_horizontalMirror, hheight]
    have hmid : ∀ x ∈ middleHalfInterval (horizontalLeft (AmbidextrousSofa.horizontalMirror U))
        (horizontalRight (AmbidextrousSofa.horizontalMirror U)),
        capRoof (AmbidextrousSofa.horizontalMirror U) x = 1 := fun x hx => by
      rw [capRoof_horizontalMirror]
      refine hmiddle _ ?_
      simp only [middleHalfInterval, hl', hr', hl, hr, mem_Icc] at hx ⊢
      constructor <;> linarith
    refine ⟨_, Or.inr rfl, hU.horizontalMirror, by rw [hl', hr]; ring, by rw [hr', hl]; ring,
      hheight', capWidth_horizontalMirror hU.isCap, capScore_horizontalMirror hU.isCap, hmid,
      hU.horizontalMirror.exists_unit_density_of_left_endpoint_criterion hheight' hmid ?_⟩
    rw [capWidth_horizontalMirror hU.isCap, hl', capRoof_horizontalMirror, neg_neg, hw]
    nlinarith only [hscalar, hR]
  · exact ⟨U, Or.inl rfl, hU, hl, hr, hheight, rfl, rfl, hmiddle,
      hU.exists_unit_density_of_left_endpoint_criterion hheight hmiddle
        (by rw [hw]; nlinarith only [hscalar, hL])⟩

end AmbidextrousSofa
