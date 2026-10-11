module

public import AmbidextrousSofa.Analysis.PartialCurvatureIntervals
public import AmbidextrousSofa.Analysis.OpenWingCurvature
public import AmbidextrousSofa.Analysis.RegularCurvatureDomain

@[expose] public section

/-!
# Actual proper-angle curvature density

The literal selected source interval bounds imply domination by a finite
multiple of Lebesgue measure away from the top, middle and terminal
normals. Radon–Nikodym gives an everywhere bounded measurable density.
On the companion semicircle the terminal normal is absent automatically.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

-- `hab` is not needed for the domination; it stays in the statement for the callers.
set_option linter.unusedVariables false in
theorem curvature_restrict_le_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : (α : ℝ) ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature target).restrict (Ioo a b) ≤
      ENNReal.ofReal (8 * R + 24) • (volume.restrict (Ioo a b)) := by
  have : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have := Measure.smul_finite ((volume : Measure ℝ).restrict (Ioo a b))
    (ENNReal.ofReal_ne_top (r := 8 * R + 24))
  refine MovingSofaOptimality.inj_measure_le_of_Ioo fun x y _ => ?_
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo,
    Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioo, smul_eq_mul]
  rcases lt_or_ge (max x a) (min y b) with hxy | hxy
  · rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith), ENNReal.le_ofReal_iff_toReal_le
      measure_Ioo_lt_top.ne (mul_nonneg (by linarith) (sub_nonneg.2 hxy.le))]
    exact (measureReal_mono Ioo_subset_Icc_self measure_Icc_lt_top.ne).trans
      (curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth haffine hA hB
        htop hterminal hperp (ha.trans_le (le_max_right _ _)) hxy.le
        ((min_le_right _ _).trans_lt hb))
  · simp [Ioo_eq_empty_of_le hxy]

theorem curvature_density_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : (α : ℝ) ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 8 * R + 24) ∧
      (upperCurvature target).restrict (Ioo a b) =
        (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  exact exists_bounded_real_density_of_le_smul (by linarith)
    (curvature_restrict_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth
      haffine hA hB htop hterminal hperp ha hab hb)

end PartialGrid

/-- The selected polygon sequence belongs to the actual given joint
maximum and is constructed inside this theorem. -/
theorem IsJointCapMaximizer.curvature_restrict_le_on_proper_open_wing
    {K : Set Plane} {α m c A B : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : α ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    (upperCurvature K).restrict (Ioo A B) ≤
      ENNReal.ofReal (8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) •
        volume.restrict (Ioo A B) := by
  have hR : 0 ≤ |horizontalLeft K| + |horizontalRight K| + 1 := by positivity
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hK.angle_mem⟩ hproper hK (neg_le_self hR)
      (subset_symmetricBox_of_horizontalBox fun p hp =>
        ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  rw [← Measure.restrict_smul]
  refine measure_restrict_Ioo_le_of_compactly_contained fun a b ha hab hb => ?_
  rw [Measure.restrict_smul]
  exact PartialGrid.curvature_restrict_le_on_wing hK.isCap hU hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox)
    (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hA hB htop hterminal hperp ha hab hb

def regularCompanionDomain (m : ℝ) : Set ℝ :=
  Ioo (Real.pi / 2) Real.pi \ {affineNormalAngle m}

theorem measurableSet_regularCompanionDomain (m : ℝ) : MeasurableSet (regularCompanionDomain m) :=
  measurableSet_Ioo.diff (measurableSet_singleton _)

end AmbidextrousSofa
