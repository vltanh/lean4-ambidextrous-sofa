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

def insetInterval (a b : ℝ) (n : ℕ) : Set ℝ :=
  Ioo (a + AngularGrid.selectionRate n) (b - AngularGrid.selectionRate n)

theorem selectionRate_antitone : Antitone AngularGrid.selectionRate := by
  intro i j hij
  have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold AngularGrid.selectionRate
  rw [div_le_div_iff₀ (by positivity : 0 < (j : ℝ) + 1)
    (by positivity : 0 < (i : ℝ) + 1)]
  nlinarith

theorem monotone_insetInterval (a b : ℝ) : Monotone (insetInterval a b) := by
  intro i j hij x hx
  have hrate := selectionRate_antitone hij
  change a + AngularGrid.selectionRate j < x ∧ x < b - AngularGrid.selectionRate j
  change a + AngularGrid.selectionRate i < x ∧ x < b - AngularGrid.selectionRate i at hx
  constructor <;> linarith [hx.1, hx.2]

theorem iUnion_insetInterval (a b : ℝ) : (⋃ n, insetInterval a b n) = Ioo a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hrate := AngularGrid.selectionRate_pos n
    change a + AngularGrid.selectionRate n < x ∧ x < b - AngularGrid.selectionRate n at hn
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
  · intro hx
    have hε : 0 < min (x - a) (b - x) :=
      lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
    obtain ⟨n, hn⟩ := (AngularGrid.selectionRate_tendsto.eventually
      (isOpen_Iio.mem_nhds hε)).exists
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change a + AngularGrid.selectionRate n < x ∧ x < b - AngularGrid.selectionRate n
    constructor <;> linarith [(lt_min_iff.mp hn).1, (lt_min_iff.mp hn).2]

theorem measure_restrict_Ioo_le_of_compactly_contained
    {μ ν : Measure ℝ} {A B : ℝ}
    (h : ∀ a b : ℝ, A < a → a ≤ b → b < B →
      μ.restrict (Ioo a b) ≤ ν.restrict (Ioo a b)) :
    μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B) := by
  have hstage (n : ℕ) : μ.restrict (insetInterval A B n) ≤ ν.restrict (insetInterval A B n) := by
    have hpos := AngularGrid.selectionRate_pos n
    by_cases hab : A + AngularGrid.selectionRate n ≤ B - AngularGrid.selectionRate n
    · exact h _ _ (by linarith) hab (by linarith)
    · have hempty : insetInterval A B n = ∅ := Ioo_eq_empty (fun h => hab h.le)
      rw [hempty, Measure.restrict_empty, Measure.restrict_empty]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [← iUnion_insetInterval A B,
    Measure.restrict_iUnion_apply_eq_iSup (monotone_insetInterval A B).directed_le hs]
  exact iSup_mono (fun n => Measure.le_iff'.mp (hstage n) s)

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
    have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (μ := ν) (f := fun t => ENNReal.ofReal (ρ t))
      (g := fun t => ENNReal.ofReal (k t)) hρ.ennreal_ofReal
      (fun s hs _ => by
        rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← heq]
        exact Measure.le_iff'.mp hsharp s)
    filter_upwards [h] with t ht
    exact (ENNReal.ofReal_le_ofReal_iff (hk0 t)).mp ht
  refine ⟨fun t => min (ρ t) (k t), hρ.min hk,
    (fun t => ⟨le_min (hρbounds t).1 (hk0 t), min_le_right _ _⟩),
    (fun t => (min_le_left _ _).trans (hρbounds t).2), heq.trans ?_⟩
  apply withDensity_congr_ae
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
  have hcoarse : (upperCurvature target).restrict (Ioo A B) ≤
      ENNReal.ofReal (4 * R + 10) • volume.restrict (Ioo A B) := by
    have h : (upperCurvature target).restrict (Ioo A B) ≤
        (ENNReal.ofReal (4 * R + 10) • (volume : Measure ℝ)).restrict (Ioo A B) := by
      apply measure_restrict_Ioo_le_of_compactly_contained
      intro a b ha hab hb
      simpa only [Measure.restrict_smul] using
        curvature_restrict_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth
          haffine hA hB htop hperp ha hab hb
    simpa only [Measure.restrict_smul] using h
  have hsharp : (upperCurvature target).restrict (Ioo A B) ≤
      (volume.restrict (Ioo A B)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity target t))) := by
    have h : (upperCurvature target).restrict (Ioo A B) ≤
        ((volume : Measure ℝ).withDensity
          (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity target t)))).restrict
            (Ioo A B) := by
      apply measure_restrict_Ioo_le_of_compactly_contained
      intro a b ha hab hb
      simpa only [restrict_withDensity measurableSet_Ioo] using
        curvature_restrict_le_source_density hTarget hU hHausdorff hlevel hc hrate hR hbox
          hwidth haffine hA hB htop hperp ha hab hb
    simpa only [restrict_withDensity measurableSet_Ioo] using h
  letI : IsFiniteMeasure ((upperCurvature target).restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  exact exists_real_density_of_two_bounds (by linarith)
    (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) hcoarse hsharp

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
  exact AngularGrid.curvature_density_sharp_on_open_wing hK.isCap hU hHausdorff hlevelTop
    (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox) hwidth haffine
    hA hB htop hperp

end AmbidextrousSofa
