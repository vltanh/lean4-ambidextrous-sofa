module

public import AmbidextrousSofa.Analysis.CornerCrossing

@[expose] public section

/-!
# Unit companion curvature forces unit curvature on the first quarter

A first level crossing extends the actual positive-corner contradiction
from `q = 1` to every `q > 1`. The zero level of the second velocity
is treated by its actual almost-everywhere derivative. Thus the final
statement includes all sign regimes and requires no phase decomposition.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.firstCornerVelocity_le_one_of_second_pos_of_unit_companion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C a : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hcompanion : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (t + Real.pi / 2) ≤ 1)
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hra : 0 < secondCornerVelocity U a) :
    firstCornerVelocity U a ≤ 1 := by
  by_contra! hqa
  obtain ⟨T, hT, hqT⟩ := hU.exists_later_negative_firstCornerVelocity hheight hmiddle ha.2
  have hsubT : Icc a T ⊆ regularCornerDomain 0 :=
    regularCornerDomain_zero ▸ fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hT.2⟩
  have hdirT := regularCornerDomain_interval_directions hsubT
  have hacT := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hT.1.le hdirT.1 hdirT.2
  obtain ⟨b, hb, hqb, hqpos⟩ := exists_first_level_crossing hT.1
    (by simpa only [uIcc_of_le hT.1.le] using hacT.1.continuousOn) hqa (by linarith)
  have hdir := regularCornerDomain_interval_directions ((Icc_subset_Icc le_rfl hb.2).trans hsubT)
  have hdrift : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (secondCornerVelocity U) (firstCornerVelocity U t + 1 - ρ t) t ∧
        1 / 2 ≤ firstCornerVelocity U t + 1 - ρ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      hU.isCap.ae_hasDerivAt_cornerVelocities_of_density hρ hρ0 hρC heq hb.1.le hdir.1 hdir.2]
      with t ht hd
    have hqt := hqpos t ⟨ht.1.le, ht.2⟩
    have hu := (upperCorner_density_bounds_on_quarter hκ ⟨ha.1.trans ht.1,
      (ht.2.trans_le hb.2).trans hT.2⟩).1.trans (sourceKappa_le_self_add_half (by linarith))
    exact ⟨hd.2, by linarith⟩
  have hrb := absolutelyContinuousOnInterval_linear_lower_bound
    (hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
      hρ hρ0 hρC heq hb.1.le hdir.1 hdir.2).2 hb.1.le hdrift (right_mem_Icc.mpr hb.1.le)
  exact hU.not_first_eq_one_and_second_pos_of_unit_companion hheight hmiddle hρ hρ0 hρC hκ heq
    hcompanion ⟨ha.1.trans hb.1, hb.2.trans_lt hT.2⟩ ⟨hqb, by linarith [hb.1]⟩

/-- This is the actual one-good-quarter propagation theorem. All source
laws, positive-corner visibility, endpoint limits and crossing geometry
are supplied by the maximizing cap itself. -/
theorem IsFullCapMaximizer.ae_first_density_le_one_of_unit_companion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hcompanion : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (t + Real.pi / 2) ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1 := by
  have hshadow := hU.ae_curvature_same_sign_quadrants (m := 0) (c := 1)
    (by simpa only [zero_mul, zero_add] using hmiddle) hρ hρ0 hρC heq
  rw [regularCornerDomain_zero] at hshadow
  refine ae_restrict_of_local_intervals isOpen_Ioo fun x hx => ?_
  obtain ⟨a, ha0, hax⟩ := exists_between hx.1
  obtain ⟨b, hxb, hbL⟩ := exists_between hx.2
  have hdir := regularCornerDomain_interval_directions (m := 0) (a := a) (b := b)
    (regularCornerDomain_zero ▸ fun t ht => ⟨ha0.trans_le ht.1, ht.2.trans_lt hbL⟩)
  have hI : Ioo a b ⊆ Ioo (0 : ℝ) (Real.pi / 2) := Ioo_subset_Ioo ha0.le hbL.le
  refine ⟨a, b, ⟨hax, hxb⟩, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.isCap.ae_hasDerivAt_cornerVelocities_of_density hρ hρ0 hρC heq (hax.trans hxb).le
      hdir.1 hdir.2, ae_restrict_of_ae_restrict_of_subset hI hshadow,
    ae_restrict_of_ae (ae_deriv_eq_zero_on_level (secondCornerVelocity U) 0)] with t ht hd hs hz
  have hk := (upperCorner_density_bounds_on_quarter hκ (hI ht)).1
  rcases le_or_gt (firstCornerVelocity U t) 1 with hq1 | hq1
  · exact hk.trans (sourceKappa_le_one_of_bounds (hU.isCap.firstCornerVelocity_ge_neg_one t) hq1)
  rcases lt_trichotomy (secondCornerVelocity U t) 0 with hr | hr | hr
  · exact (hs.1 ⟨by linarith, hr⟩).1.trans_le zero_le_one
  · linarith [hd.2.deriv.symm.trans (hz hr), sourceKappa_eq_self_of_one_le hq1.le]
  · exact absurd hq1 (hU.firstCornerVelocity_le_one_of_second_pos_of_unit_companion hheight
      hmiddle hρ hρ0 hρC hκ heq hcompanion (hI ht) hr).not_gt

end AmbidextrousSofa
