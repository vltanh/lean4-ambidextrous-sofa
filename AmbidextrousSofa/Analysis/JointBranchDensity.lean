module

public import AmbidextrousSofa.Analysis.JointSourceBranches

@[expose] public section

/-!
# Angular densities of the four common-source branches

Translate a source family back to the first quarter by its quarter turn.
The sum of its tangent and corner branch densities is then the actual
curvature density there: the first density for the first family and the
companion density for the second, by one argument. These statements
identify the Radon--Nikodym representatives of the literal restrictions,
rather than introducing independent occupation weights. A branch whose
sources avoid a measurable angular set has zero density on it.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem ae_realRnDensity_eq_on_of_withDensity_restrict
    {μ : Measure ℝ} {S : Set ℝ} {ρ : ℝ → ℝ}
    (hS : MeasurableSet S) (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hμ : μ = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict S, realRnDensity μ volume t = ρ t := by
  have hd := ae_realRnDensity_eq_of_withDensity (μ := μ) (ν := volume) (hρ.indicator hS)
    (indicator_nonneg fun t _ => hρ0 t) (by
      rw [hμ, ← withDensity_indicator hS]
      exact congrArg _ (indicator_comp_of_zero ENNReal.ofReal_zero))
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hd] with t ht heq
  simpa only [indicator_of_mem ht] using heq

/-- Translating an interval back to `(0, π / 2)` carries its density along. -/
theorem map_quarter_density {ρ : ℝ → ℝ} (hρ : Measurable ρ) {d : ℝ} {I : Set ℝ}
    (hI : (fun t => t - d) ⁻¹' Ioo 0 (Real.pi / 2) = I) :
    ((volume.restrict I).withDensity (fun t => ENNReal.ofReal (ρ t))).map (fun t => t - d) =
      (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
        (fun t => ENNReal.ofReal (ρ (t + d))) := by
  have hv : (volume.restrict I).map (fun t => t - d) =
      volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [← hI, ← Measure.restrict_map (measurable_sub_const' _) measurableSet_Ioo,
      map_sub_right_eq_self]
  simpa only [Function.comp_apply, sub_add_cancel, hv] using map_withDensity_comp
    (volume.restrict I) (measurable_sub_const' d) (hρ.comp (measurable_add_const d)).ennreal_ofReal

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b)

/-- The two branches of one source family, on the slice `I` of angles translated back to
`(0, π / 2)` by `d`, have the translated curvature density as the sum of their densities. -/
theorem ae_source_density_sum (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)
    {S₁ S₂ : Set Plane} {d : ℝ} {I : Set ℝ}
    (hI : (fun t => t - d) ⁻¹' Ioo 0 (Real.pi / 2) = I) (hIsub : I ⊆ Ioo 0 Real.pi)
    (hpart : J.sourceBranchMeasure S₁ + J.sourceBranchMeasure S₂ =
      J.sourceBranchMeasure (Prod.fst ⁻¹' I)) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity S₁ d t + J.sourceBranchDensity S₂ d t = ρ (t + d) := by
  have hImeas : MeasurableSet I := hI ▸ measurableSet_Ioo.preimage (measurable_sub_const' d)
  have hsum : J.sourceBranchAngular S₁ d + J.sourceBranchAngular S₂ d =
      (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
        (fun t => ENNReal.ofReal (ρ (t + d))) := by
    have h : J.sourceBranchAngular S₁ d + J.sourceBranchAngular S₂ d =
        (J.angularMeasure.restrict I).map (fun t => t - d) := by
      rw [sourceBranchAngular, sourceBranchAngular, ← Measure.map_add _ _
        (measurable_fst.sub_const d), hpart, angularMeasure,
        Measure.restrict_map measurable_fst hImeas, Measure.map_map (measurable_sub_const' _)
          measurable_fst]
      rfl
    rw [h, J.angularMeasure_eq_density H, restrict_withDensity hImeas,
      Measure.restrict_restrict_of_subset hIsub, map_quarter_density H.hρ hI]
  filter_upwards [ae_realRnDensity_eq_on_of_withDensity_restrict measurableSet_Ioo
    (H.hρ.comp (measurable_add_const _)) (fun t => H.hρ0 _) hsum,
    ae_restrict_of_ae (ae_realRnDensity_add (J.sourceBranchAngular S₁ d)
      (J.sourceBranchAngular S₂ d) volume)] with t ht hs
  exact hs.symm.trans ht

theorem ae_first_source_density_sum (H : IsTiltedFirstUnitTarget target a b C h m c ρ K) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (firstTangentSource target) 0 t +
        J.sourceBranchDensity (firstCornerSource target) 0 t = ρ t := by
  simpa only [add_zero] using J.ae_source_density_sum H (d := 0) (by ext; simp)
    (Ioo_subset_Ioo le_rfl (by linarith [Real.pi_pos])) (J.first_source_partition H)

theorem ae_second_source_density_sum (H : IsTiltedFirstUnitTarget target a b C h m c ρ K) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (secondTangentSource target) (Real.pi / 2) t +
        J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2) t =
          ρ (t + Real.pi / 2) :=
  J.ae_source_density_sum H (by rw [preimage_sub_const_Ioo, zero_add, add_halves])
    (Ioo_subset_Ioo (by positivity) le_rfl) (J.second_source_partition H)

theorem ae_sourceBranchDensity_eq_zero_on (hac : J.angularMeasure ≪ volume)
    {S : Set Plane} {d : ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (hzero : ∀ᵐ z ∂J.sourceBranchMeasure S, z.1 - d ∉ E) :
    ∀ᵐ t ∂volume, t ∈ E → J.sourceBranchDensity S d t = 0 := by
  have hz : J.sourceBranchAngular S d E = 0 := (Measure.map_apply
    (measurable_fst.sub_const d) hE).trans (measure_eq_zero_iff_ae_notMem.mpr hzero)
  rw [J.sourceBranchAngular_eq_density hac, withDensity_apply _ hE,
    lintegral_eq_zero_iff (J.measurable_sourceBranchDensity S d).ennreal_ofReal] at hz
  exact (ae_restrict_iff' hE).mp (hz.mono fun t ht =>
    le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (J.sourceBranchDensity_nonneg S d t))

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
