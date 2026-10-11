module

public import AmbidextrousSofa.Analysis.SharpCurvatureDensity

@[expose] public section

/-!
# Curvature on entire open wings

An explicit increasing exhaustion promotes the compactly contained
interval bounds to each whole open wing. The actual curvature has a
single measurable density on that whole interval, with the proved
coarse bound and the sharp velocity-dependent bound simultaneously.
No endpoint atom is included in an open-wing density.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem measure_restrict_Ioo_le_of_compactly_contained
    {μ ν : Measure ℝ} {A B : ℝ}
    (h : ∀ a b : ℝ, A < a → a ≤ b → b < B →
      μ.restrict (Ioo a b) ≤ ν.restrict (Ioo a b)) :
    μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B) := by
  -- Exhaust `Ioo A B` by the increasing intervals `Ioo (A + 1 / (n + 1)) (B - 1 / (n + 1))`.
  have hf : Antitone fun n : ℕ => A + 1 / ((n : ℝ) + 1) := fun _ _ h => by dsimp only; gcongr
  have hg : Monotone fun n : ℕ => B - 1 / ((n : ℝ) + 1) := fun _ _ h => by dsimp only; gcongr
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  rw [← iUnion_Ioo_of_mono_of_isGLB_of_isLUB hf hg
    (isGLB_of_tendsto_atTop hf (by simpa using ht.const_add A))
    (isLUB_of_tendsto_atTop hg (by simpa using ht.const_sub B))]
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.restrict_iUnion_apply_eq_iSup (hf.Ioo hg).directed_le hs,
    Measure.restrict_iUnion_apply_eq_iSup (hf.Ioo hg).directed_le hs]
  refine iSup_mono fun n => ?_
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  rcases le_or_gt (A + 1 / ((n : ℝ) + 1)) (B - 1 / ((n : ℝ) + 1)) with hab | hab
  · exact Measure.le_iff'.mp (h _ _ (by linarith) hab (by linarith)) s
  · rw [Ioo_eq_empty (not_lt.2 hab.le)]
    simp

/-- A single density can obey a uniform bound and a second measurable
pointwise bound at once. Both are derived from domination of measures. -/
theorem exists_real_density_of_two_bounds
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : ℝ} {k : ℝ → ℝ} (hC : 0 ≤ C) (hk : Measurable k) (hk0 : ∀ t, 0 ≤ k t)
    (hcoarse : μ ≤ ENNReal.ofReal C • ν)
    (hsharp : μ ≤ ν.withDensity (fun t => ENNReal.ofReal (k t))) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t, 0 ≤ ρ t ∧ ρ t ≤ k t) ∧
      (∀ t, ρ t ≤ C) ∧ μ = ν.withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨ρ, hρ, hρbounds, heq⟩ := exists_bounded_real_density_of_le_smul hC hcoarse
  have hbound : ∀ᵐ t ∂ν, ρ t ≤ k t := by
    filter_upwards [ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := ν)
      (g := fun t => ENNReal.ofReal (k t)) hρ.ennreal_ofReal fun s hs _ => by
        rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← heq]
        exact Measure.le_iff'.mp hsharp s] with t ht
    exact (ENNReal.ofReal_le_ofReal_iff (hk0 t)).mp ht
  refine ⟨fun t => min (ρ t) (k t), hρ.min hk,
    fun t => ⟨le_min (hρbounds t).1 (hk0 t), min_le_right _ _⟩,
    fun t => (min_le_left _ _).trans (hρbounds t).2, heq.trans (withDensity_congr_ae ?_)⟩
  filter_upwards [hbound] with t ht
  rw [min_eq_left ht]

namespace AngularGrid

theorem curvature_density_sharp_on_open_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity target t)) ∧
      (∀ t, ρ t ≤ 4 * R + 10) ∧
      (upperCurvature target).restrict (Ioo A B) =
        (volume.restrict (Ioo A B)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have : IsFiniteMeasure ((upperCurvature target).restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  refine exists_real_density_of_two_bounds (by linarith)
    (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) ?_ ?_
  · rw [← Measure.restrict_smul]
    exact measure_restrict_Ioo_le_of_compactly_contained fun a b ha hab hb => by
      simpa only [Measure.restrict_smul] using curvature_restrict_le_on_wing hTarget hU
        hHausdorff hlevel hc hrate hR hbox hwidth haffine hA hB htop hperp ha hab hb
  · rw [← restrict_withDensity measurableSet_Ioo]
    exact measure_restrict_Ioo_le_of_compactly_contained fun a b ha hab hb => by
      simpa only [restrict_withDensity measurableSet_Ioo] using
        curvature_restrict_le_source_density hTarget hU hHausdorff hlevel hc hrate hR hbox
          hwidth haffine hA hB htop hperp ha hab hb

end AngularGrid

theorem IsFullCapMaximizer.curvature_density_sharp_on_open_wing {K : Set Plane}
    (hK : IsFullCapMaximizer K) {m c A B : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10) ∧
      (upperCurvature K).restrict (Ioo A B) =
        (volume.restrict (Ioo A B)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hR : 0 ≤ |horizontalLeft K| + |horizontalRight K| + 1 := by positivity
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (neg_le_self hR) (subset_symmetricBox_of_horizontalBox
      fun p hp => ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  exact AngularGrid.curvature_density_sharp_on_open_wing hK.isCap hU hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox)
    (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hA hB htop hperp

end AmbidextrousSofa
