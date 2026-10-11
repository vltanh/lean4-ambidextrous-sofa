module

public import AmbidextrousSofa.Analysis.WingCurvatureIntervals
public import MovingSofaOptimality.Injectivity.LimitIneq

@[expose] public section

/-!
# Actual bounded curvature densities on the wings

The interval bound is promoted to domination of finite measures by the
generic open-interval comparison lemma. The Radon–Nikodym derivative then
gives an actual measurable curvature density. Truncating its null-set
values produces a representative bounded everywhere by the proved box
constant. No density or absolute-continuity hypothesis is supplied.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- A finite measure dominated by a finite constant multiple has a
measurable real density with the same everywhere bound. -/
theorem exists_bounded_real_density_of_le_smul
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) (hle : μ ≤ ENNReal.ofReal C • ν) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t, 0 ≤ ρ t ∧ ρ t ≤ C) ∧
      μ = ν.withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hbound : ∀ᵐ t ∂ν, μ.rnDeriv ν t ≤ ENNReal.ofReal C :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ => by
      simpa [setLIntegral_const] using (Measure.setLIntegral_rnDeriv_le s).trans (hle s)
  refine ⟨fun t => min (μ.rnDeriv ν t).toReal C,
    (μ.measurable_rnDeriv ν).ennreal_toReal.min measurable_const,
    fun t => ⟨le_min ENNReal.toReal_nonneg hC, min_le_right _ _⟩,
    (Measure.withDensity_rnDeriv_eq μ ν (Measure.absolutelyContinuous_of_le_smul hle)).symm.trans
      (withDensity_congr_ae ?_)⟩
  filter_upwards [Measure.rnDeriv_lt_top μ ν, hbound] with t ht htC
  rw [ENNReal.ofReal_mono.map_min, ENNReal.ofReal_toReal ht.ne, min_eq_left htC]

namespace AngularGrid

/-- Domination is for the literal Stieltjes measure of the target cap. -/
theorem curvature_restrict_le_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature target).restrict (Ioo a b) ≤
      ENNReal.ofReal (4 * R + 10) • (volume.restrict (Ioo a b)) := by
  have _ := hab -- not needed by the proof; it stays in the statement for the callers
  have : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have : IsFiniteMeasure (ENNReal.ofReal (4 * R + 10) • (volume.restrict (Ioo a b))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hC : 0 ≤ 4 * R + 10 := by linarith
  refine MovingSofaOptimality.inj_measure_le_of_Ioo fun x y _ => ?_
  rw [Measure.restrict_apply measurableSet_Ioo, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioo]
  rcases lt_or_ge (x ⊔ a) (y ⊓ b) with hxy | hxy
  · rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hC, ENNReal.le_ofReal_iff_toReal_le
      measure_Ioo_lt_top.ne (mul_nonneg hC (sub_nonneg.mpr hxy.le))]
    exact (measureReal_mono Ioo_subset_Icc_self measure_Icc_lt_top.ne).trans
      (curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth haffine hA hB
        htop hperp (ha.trans_le le_sup_right) hxy.le (inf_le_right.trans_lt hb))
  · rw [Ioo_eq_empty hxy.not_gt, measure_empty, measure_empty, mul_zero]

theorem curvature_density_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 4 * R + 10) ∧
      (upperCurvature target).restrict (Ioo a b) =
        (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  exact exists_bounded_real_density_of_le_smul (by linarith)
    (curvature_restrict_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth
      haffine hA hB htop hperp ha hab hb)

end AngularGrid

end AmbidextrousSofa
