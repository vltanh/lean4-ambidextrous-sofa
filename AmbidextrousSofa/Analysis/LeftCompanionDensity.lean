module

public import AmbidextrousSofa.Analysis.LeftCompanionCurvature
public import AmbidextrousSofa.Analysis.PartialCurvatureDensity

@[expose] public section

/-!
# Actual density of the left charged companion cap

The proper selected-polygon construction supplies the original cap's
density away from its affine normal. The left cut has identical actual
curvature after that normal and zero initial mass through the normal
when the middle slope is positive. These two proved geometric facts
splice the density onto the entire open companion arc.

The top atom remains outside the open arc. The original affine-face
atom is never transferred to the cut: the cut's joining atom is proved
zero by actual middle-facet pinning. The construction works in every
sign of the middle slope.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace AmbidextrousSofa

theorem restrict_withDensity_of_subset
    {μ : Measure ℝ} {S T : Set ℝ} {f : ℝ → ℝ≥0∞}
    (heq : μ.restrict S = (volume.restrict S).withDensity f)
    (hT : MeasurableSet T) (hsub : T ⊆ S) :
    μ.restrict T = (volume.restrict T).withDensity f := by
  rw [← Measure.restrict_restrict_of_subset hsub, heq, restrict_withDensity hT,
    Measure.restrict_restrict_of_subset hsub]

/-- Equality after the affine normal holds on the whole open wing,
obtained from equality on each compactly contained Stieltjes arc. -/
theorem IsDownwardCap.leftCompanion_curvature_restrict_open_after_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ z ∈ Icc a b, capRoof U z = m * z + c)
    (hmx : affineNormalAngle m ≤ x) :
    (upperCurvature (AmbidextrousSofa.leftCompanionCap U a)).restrict (Ioo x Real.pi) =
      (upperCurvature U).restrict (Ioo x Real.pi) := by
  have hlocal (r s : ℝ) (hxr : x < r) (hrs : r ≤ s) (hsπ : s < Real.pi) :
      (upperCurvature (AmbidextrousSofa.leftCompanionCap U a)).restrict (Ioo r s) =
        (upperCurvature U).restrict (Ioo r s) := by
    rw [← Measure.restrict_restrict_of_subset Ioo_subset_Ioc_self,
      hU.leftCompanion_curvature_restrict_after_affine ha hb hab haffine hrs (hmx.trans hxr.le) hsπ,
      Measure.restrict_restrict_of_subset Ioo_subset_Ioc_self]
  exact le_antisymm
    (measure_restrict_Ioo_le_of_compactly_contained fun r s h₁ h₂ h₃ => (hlocal r s h₁ h₂ h₃).le)
    (measure_restrict_Ioo_le_of_compactly_contained fun r s h₁ h₂ h₃ => (hlocal r s h₁ h₂ h₃).ge)

def leftCompanionWingDensity (m : ℝ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  (Ioi (max (Real.pi / 2) (affineNormalAngle m))).indicator ρ

theorem measurable_leftCompanionWingDensity {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (m : ℝ) : Measurable (leftCompanionWingDensity m ρ) :=
  hρ.indicator measurableSet_Ioi

theorem leftCompanionWingDensity_eq_zero {m t : ℝ} {ρ : ℝ → ℝ}
    (ht : t ≤ max (Real.pi / 2) (affineNormalAngle m)) :
    leftCompanionWingDensity m ρ t = 0 :=
  indicator_of_notMem (not_lt_of_ge ht) ρ

theorem leftCompanionWingDensity_eq {m t : ℝ} {ρ : ℝ → ℝ}
    (ht : max (Real.pi / 2) (affineNormalAngle m) < t) :
    leftCompanionWingDensity m ρ t = ρ t :=
  indicator_of_mem ht ρ

/-- The regular original density gives the literal cut density without
including the original affine-face atom. -/
theorem IsJointCapMaximizer.leftCompanion_density_of_regular_companion
    {U : Set Plane} {α m c : ℝ} {ρ : ℝ → ℝ}
    (hU : IsJointCapMaximizer U α)
    (haffine : ∀ z ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U z = m * z + c)
    (heq : (upperCurvature U).restrict (regularCompanionDomain m) =
      (volume.restrict (regularCompanionDomain m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
        (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) := by
  let b := max (Real.pi / 2) (affineNormalAngle m)
  have hLb : Real.pi / 2 ≤ b := le_max_left _ _
  have hθb : affineNormalAngle m ≤ b := le_max_right _ _
  have hbπ : b < Real.pi := max_lt (by linarith only [Real.pi_pos]) (affineNormalAngle_mem m).2
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (by linarith only [hU.width_bounds.1, one_lt_M])
  have hzero : upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) b) = 0 := by
    rcases le_or_gt (affineNormalAngle m) (Real.pi / 2) with hθ | hθ
    · rw [show b = Real.pi / 2 from max_eq_left hθ, Ioc_self, measure_empty]
    · rw [show b = affineNormalAngle m from max_eq_right hθ.le]
      exact hU.leftCompanion_initial_curvature_zero
        (Real.arctan_pos.mp ((lt_add_iff_pos_left _).mp hθ)) haffine
  have hind : (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) =
      (Ioi b).indicator (fun t => ENNReal.ofReal (ρ t)) :=
    (indicator_comp_of_zero (g := ENNReal.ofReal) ENNReal.ofReal_zero).symm
  -- On `Ioo b π` the claimed density is the original one, so the cut curvature matches it.
  rw [hind, withDensity_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioo, max_eq_left hLb, ← restrict_withDensity_of_subset heq measurableSet_Ioo
      fun t ht => ⟨⟨hLb.trans_lt ht.1, ht.2⟩, (hθb.trans_lt ht.1).ne'⟩,
    ← hU.isCap.leftCompanion_curvature_restrict_open_after_affine ha hb hab haffine hθb]
  -- On `Ioc (π / 2) b` the cut has no curvature.
  rw [← Ioc_union_Ioo_eq_Ioo hLb hbπ, Measure.restrict_union
    (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self) measurableSet_Ioo,
    Measure.restrict_eq_zero.mpr hzero, zero_add]

end AmbidextrousSofa
