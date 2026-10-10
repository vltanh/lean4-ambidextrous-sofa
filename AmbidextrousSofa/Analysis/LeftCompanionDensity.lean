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
  have h := congrArg (fun ν : Measure ℝ => ν.restrict T) heq
  simpa only [Measure.restrict_restrict_of_subset hsub,
    restrict_withDensity hT] using h

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
    have heq := hU.leftCompanion_curvature_restrict_after_affine ha hb hab haffine
      hrs (hmx.trans hxr.le) hsπ
    have h := congrArg (fun ν : Measure ℝ => ν.restrict (Ioo r s)) heq
    simpa only [Measure.restrict_restrict_of_subset Ioo_subset_Ioc_self] using h
  apply le_antisymm
  · apply measure_restrict_Ioo_le_of_compactly_contained
    intro r s hxr hrs hsπ
    exact (hlocal r s hxr hrs hsπ).le
  · apply measure_restrict_Ioo_le_of_compactly_contained
    intro r s hxr hrs hsπ
    exact (hlocal r s hxr hrs hsπ).ge

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
  have hbπ : b < Real.pi := max_lt
    (by linarith only [Real.pi_pos]) (affineNormalAngle_mem m).2
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hzero : upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) b) = 0 := by
    by_cases hθ : affineNormalAngle m ≤ Real.pi / 2
    · have hb : b = Real.pi / 2 := max_eq_left hθ
      rw [hb, Ioc_self, measure_empty]
    · have hm : 0 < m := Real.arctan_pos.mp (by
        have hpos : Real.pi / 2 < affineNormalAngle m := lt_of_not_ge hθ
        unfold affineNormalAngle at hpos
        linarith only [hpos])
      have hb : b = affineNormalAngle m := max_eq_right (le_of_not_ge hθ)
      rw [hb]
      exact hU.leftCompanion_initial_curvature_zero hm haffine
  have hlast := hU.isCap.leftCompanion_curvature_restrict_open_after_affine
    ha hb hab haffine hθb
  have hsub : Ioo b Real.pi ⊆ regularCompanionDomain m := by
    intro t ht
    exact ⟨⟨hLb.trans_lt ht.1, ht.2⟩, (hθb.trans_lt ht.1).ne'⟩
  have hρlast := restrict_withDensity_of_subset heq measurableSet_Ioo hsub
  have hdecomp : Ioo (Real.pi / 2) Real.pi =
      Ioc (Real.pi / 2) b ∪ Ioo b Real.pi := by
    ext t
    constructor
    · intro ht
      by_cases htb : t ≤ b
      · exact Or.inl ⟨ht.1, htb⟩
      · exact Or.inr ⟨lt_of_not_ge htb, ht.2⟩
    · intro ht
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans_lt hbπ⟩
      · exact ⟨hLb.trans_lt ht.1, ht.2⟩
  have hd : Disjoint (Ioc (Real.pi / 2) b) (Ioo b Real.pi) := by
    apply disjoint_left.mpr
    intro t ht hs
    exact (not_lt_of_ge ht.2) hs.1
  have hinter : Ioi b ∩ Ioo (Real.pi / 2) Real.pi = Ioo b Real.pi := by
    ext t
    constructor
    · exact fun ht => ⟨ht.1, ht.2.2⟩
    · exact fun ht => ⟨ht.1, hLb.trans_lt ht.1, ht.2⟩
  have hind : (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) =
      (Ioi b).indicator (fun t => ENNReal.ofReal (ρ t)) := by
    funext t
    change ENNReal.ofReal ((Ioi b).indicator ρ t) =
      (Ioi b).indicator (fun r => ENNReal.ofReal (ρ r)) t
    by_cases ht : t ∈ Ioi b
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht, ENNReal.ofReal_zero]
  calc
    _ = (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioc (Real.pi / 2) b) +
        (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioo b Real.pi) := by rw [hdecomp, Measure.restrict_union hd measurableSet_Ioo]
    _ = (volume.restrict (Ioo b Real.pi)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
      rw [Measure.restrict_eq_zero.mpr hzero, zero_add, hlast, hρlast]
    _ = _ := by
      rw [hind, withDensity_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, hinter]

/-- An actual proper maximizer supplies a globally bounded measurable
density for its literal left companion cut on the full open companion
arc. The initial zero region is retained pointwise in the representative. -/
theorem IsJointCapMaximizer.leftCompanion_curvature_density
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ z ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U z = m * z + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (∀ t ≤ max (Real.pi / 2) (affineNormalAngle m), ρ t = 0) ∧
      (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨ρ, hρ, hbounds, heq⟩ :=
    hU.curvature_density_on_regular_companion_domain hproper haffine
  refine ⟨leftCompanionWingDensity m ρ, measurable_leftCompanionWingDensity hρ m,
    ?_, (fun t ht => leftCompanionWingDensity_eq_zero ht),
    hU.leftCompanion_density_of_regular_companion haffine heq⟩
  intro t
  by_cases ht : max (Real.pi / 2) (affineNormalAngle m) < t
  · rw [leftCompanionWingDensity_eq ht]
    exact hbounds t
  · rw [leftCompanionWingDensity_eq_zero (le_of_not_gt ht)]
    exact ⟨le_rfl, by positivity⟩

end AmbidextrousSofa
