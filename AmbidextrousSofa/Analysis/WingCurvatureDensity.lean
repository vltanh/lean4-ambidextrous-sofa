import AmbidextrousSofa.Analysis.WingCurvatureIntervals
import AmbidextrousSofa.Imported.Injectivity.LimitIneq

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
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hle
  let r := fun t => (μ.rnDeriv ν t).toReal
  have hr : Measurable r := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hr0 : ∀ t, 0 ≤ r t := fun _ => ENNReal.toReal_nonneg
  have heq : μ = ν.withDensity (fun t => ENNReal.ofReal (r t)) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hac]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with t ht
    exact (ENNReal.ofReal_toReal ht.ne).symm
  have hbound : ∀ᵐ t ∂ν, r t ≤ C := by
    have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (μ := ν) (f := fun t => ENNReal.ofReal (r t))
      (g := fun _ => ENNReal.ofReal C) hr.ennreal_ofReal
      (fun s hs _ => by
        rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← heq, withDensity_const]
        exact Measure.le_iff'.mp hle s)
    filter_upwards [h] with t ht
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp ht
  refine ⟨fun t => min (r t) C, hr.min measurable_const,
    fun t => ⟨le_min (hr0 t) hC, min_le_right _ _⟩, heq.trans ?_⟩
  apply withDensity_congr_ae
  filter_upwards [hbound] with t ht
  rw [min_eq_left ht]

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
  letI : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure (ENNReal.ofReal (4 * R + 10) • (volume.restrict (Ioo a b))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hC : 0 ≤ 4 * R + 10 := by linarith
  apply Imported.inj_measure_le_of_Ioo
  intro x y _
  simp only [Measure.restrict_apply measurableSet_Ioo, Measure.smul_apply, smul_eq_mul]
  have hinter : Ioo x y ∩ Ioo a b = Ioo (max x a) (min y b) := by
    ext z
    simp only [mem_inter_iff, mem_Ioo, max_lt_iff, lt_min_iff]
    tauto
  rw [hinter]
  by_cases hxy : max x a < min y b
  · have hbound := curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox
      hwidth haffine hA hB htop hperp
      (ha.trans_le (le_max_right _ _)) hxy.le ((min_le_right _ _).trans_lt hb)
    have hmono : (upperCurvature target).real (Ioo (max x a) (min y b)) ≤
        (upperCurvature target).real (Icc (max x a) (min y b)) :=
      measureReal_mono Ioo_subset_Icc_self measure_Icc_lt_top.ne
    rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hC]
    apply (ENNReal.toReal_le_toReal measure_Ioo_lt_top.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (mul_nonneg hC (sub_nonneg.mpr hxy.le))]
    exact hmono.trans hbound
  · rw [Ioo_eq_empty hxy, measure_empty, measure_empty, mul_zero]

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
  letI : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  exact exists_bounded_real_density_of_le_smul (by linarith)
    (curvature_restrict_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth
      haffine hA hB htop hperp ha hab hb)

end AngularGrid

/-- A full maximizer with an affine middle has actual bounded curvature
density on each closedly contained wing interval. Its selected polygon
sequence is constructed by the proof and is not an input certificate. -/
theorem IsFullCapMaximizer.curvature_density_on_wing {K : Set Plane}
    (hK : IsFullCapMaximizer K) {m c A B a b : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10) ∧
      (upperCurvature K).restrict (Ioo a b) =
        (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (by linarith : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith [hK.width_bounds.1, one_lt_M]
  exact AngularGrid.curvature_density_on_wing hK.isCap hU hHausdorff hlevelTop
    (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox) hwidth haffine
    hA hB htop hperp ha hab hb

end AmbidextrousSofa
