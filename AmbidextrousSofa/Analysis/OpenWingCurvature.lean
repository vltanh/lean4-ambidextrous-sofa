module

public import AmbidextrousSofa.Analysis.SharpCurvatureDensity

@[expose] public section

/-!
# Curvature on entire open wings

An explicit increasing exhaustion promotes linear bounds on the compactly
contained closed intervals to domination of the actual curvature on a
whole open wing by a multiple of Lebesgue measure. The local sharp source
bounds at almost every normal give domination by the sharp
velocity-dependent coefficient. The actual curvature therefore has a
single measurable density on that whole interval, with the proved coarse
bound and the sharp bound simultaneously. No endpoint atom is included
in an open-wing density.
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

/-- Linear bounds on the closed subintervals of `(A, B)` give domination of the restriction
to `(A, B)` by the same multiple of Lebesgue measure. -/
theorem restrict_Ioo_le_smul_of_Icc_le {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {A B C : ℝ}
    (hC : 0 ≤ C) (h : ∀ a b, A < a → a ≤ b → b < B → μ.real (Icc a b) ≤ C * (b - a)) :
    μ.restrict (Ioo A B) ≤ ENNReal.ofReal C • volume.restrict (Ioo A B) := by
  rw [← Measure.restrict_smul]
  refine measure_restrict_Ioo_le_of_compactly_contained fun a b ha hab hb => ?_
  rw [Measure.restrict_smul]
  have : IsFiniteMeasure (μ.restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have : IsFiniteMeasure (ENNReal.ofReal C • volume.restrict (Ioo a b)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  refine MovingSofaOptimality.inj_measure_le_of_Ioo fun x y _ => ?_
  rw [Measure.restrict_apply measurableSet_Ioo, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioo]
  rcases lt_or_ge (x ⊔ a) (y ⊓ b) with hxy | hxy
  · rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hC, ENNReal.le_ofReal_iff_toReal_le
      measure_Ioo_lt_top.ne (mul_nonneg hC (sub_nonneg.mpr hxy.le))]
    exact (measureReal_mono Ioo_subset_Icc_self measure_Icc_lt_top.ne).trans
      (h _ _ (ha.trans_le le_sup_right) hxy.le (inf_le_right.trans_lt hb))
  · rw [Ioo_eq_empty hxy.not_gt, measure_empty, measure_empty, mul_zero]

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

/-- Both source families are covered by their full upper normal; their exceptional companion
atoms are a null set and do not need a regularity hypothesis. -/
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
  have hC : 0 ≤ 4 * R + 10 := by linarith
  have hcoarse := restrict_Ioo_le_smul_of_Icc_le hC fun a b ha hab hb =>
    curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth haffine hA hB
      htop hperp ha hab hb
  have : IsFiniteMeasure ((upperCurvature target).restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  refine exists_real_density_of_two_bounds hC
    (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) hcoarse
    (restrict_Ioo_le_withDensity_of_local_bound hC hcoarse ?_)
  filter_upwards [ae_sigmaAt_companionSourceAngle_eq_zero target] with t hcomp ht ε hε
  obtain ⟨δ, hδ, -, hlocal⟩ := curvature_local_source_bound hTarget hU hHausdorff hlevel hc hrate
    hR hbox hwidth haffine hA hB htop hperp ht hcomp hε
  exact ⟨δ, hδ, hlocal⟩

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
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, hHausdorff⟩ :=
    hK.exists_symmetric_selected_sequence
  exact AngularGrid.curvature_density_sharp_on_open_wing hK.isCap hU hHausdorff hlevel hc hrate
    (by positivity) (fun n => (hU n).inBox) (by linarith only [hK.width_bounds.1, one_lt_M])
    haffine hA hB htop hperp

end AmbidextrousSofa
