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
  letI : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure (ENNReal.ofReal (8 * R + 24) • (volume.restrict (Ioo a b))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hC : 0 ≤ 8 * R + 24 := by linarith
  apply MovingSofaOptimality.inj_measure_le_of_Ioo
  intro x y _
  simp only [Measure.restrict_apply measurableSet_Ioo, Measure.smul_apply, smul_eq_mul]
  have hinter : Ioo x y ∩ Ioo a b = Ioo (max x a) (min y b) := by
    ext z
    simp only [mem_inter_iff, mem_Ioo, max_lt_iff, lt_min_iff]
    tauto
  rw [hinter]
  by_cases hxy : max x a < min y b
  · have hbound := curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox
      hwidth haffine hA hB htop hterminal hperp
      (ha.trans_le (le_max_right _ _)) hxy.le ((min_le_right _ _).trans_lt hb)
    have hmono : (upperCurvature target).real (Ioo (max x a) (min y b)) ≤
        (upperCurvature target).real (Icc (max x a) (min y b)) :=
      measureReal_mono Ioo_subset_Icc_self measure_Icc_lt_top.ne
    rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hC]
    apply (ENNReal.toReal_le_toReal measure_Ioo_lt_top.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (mul_nonneg hC (sub_nonneg.mpr hxy.le))]
    exact hmono.trans hbound
  · rw [Ioo_eq_empty_of_le (le_of_not_gt hxy), measure_empty, measure_empty, mul_zero]

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
  letI : IsFiniteMeasure ((upperCurvature target).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a b)) :=
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
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  let β : TerminalAngle := ⟨α, hK.angle_mem⟩
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence β hproper hK (by linarith : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith [hK.width_bounds.1, one_lt_M]
  have hdom : (upperCurvature K).restrict (Ioo A B) ≤
      (ENNReal.ofReal (8 * R + 24) • (volume : Measure ℝ)).restrict (Ioo A B) := by
    apply measure_restrict_Ioo_le_of_compactly_contained
    intro a b ha hab hb
    have h := PartialGrid.curvature_restrict_le_on_wing hK.isCap hU hHausdorff hlevelTop
      (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox) hwidth haffine
      hA hB htop hterminal hperp ha hab hb
    simpa only [Measure.restrict_smul] using h
  simpa only [Measure.restrict_smul] using hdom

theorem IsJointCapMaximizer.curvature_density_on_proper_open_wing
    {K : Set Plane} {α m c A B : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : α ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) ∧
      (upperCurvature K).restrict (Ioo A B) =
        (volume.restrict (Ioo A B)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  letI : IsFiniteMeasure ((upperCurvature K).restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  exact exists_bounded_real_density_of_le_smul (by positivity)
    (hK.curvature_restrict_le_on_proper_open_wing hproper haffine hA hB htop hterminal hperp)

def regularCompanionDomain (m : ℝ) : Set ℝ :=
  Ioo (Real.pi / 2) Real.pi \ {affineNormalAngle m}

theorem regularCompanionDomain_eq_two (m : ℝ) :
    regularCompanionDomain m =
      Ioo (Real.pi / 2) (max (Real.pi / 2) (affineNormalAngle m)) ∪
        Ioo (max (Real.pi / 2) (affineNormalAngle m)) Real.pi := by
  ext t
  simp only [regularCompanionDomain, Set.mem_sdiff, mem_Ioo, mem_singleton_iff, mem_union]
  by_cases hm : affineNormalAngle m ≤ Real.pi / 2
  · rw [max_eq_left hm]
    constructor
    · intro ht
      exact Or.inr ht.1
    · intro ht
      rcases ht with ht | ht
      · exact False.elim (lt_irrefl _ (ht.1.trans ht.2))
      · exact ⟨ht, by linarith only [ht.1, hm]⟩
  · rw [max_eq_right (le_of_not_ge hm)]
    constructor
    · rintro ⟨ht, hne⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨ht.1, hlt⟩
      · exact Or.inr ⟨hgt, ht.2⟩
    · intro ht
      rcases ht with ht | ht
      · exact ⟨⟨ht.1, ht.2.trans (affineNormalAngle_mem m).2⟩, ht.2.ne⟩
      · exact ⟨⟨(lt_of_not_ge hm).trans ht.1, ht.2⟩, ht.1.ne'⟩

theorem measurableSet_regularCompanionDomain (m : ℝ) : MeasurableSet (regularCompanionDomain m) :=
  measurableSet_Ioo.diff (measurableSet_singleton _)

/-- The companion arc has an actual bounded density. Only its possible
middle-face atom is removed; the top and terminal normals lie outside the
open companion arc. -/
theorem IsJointCapMaximizer.curvature_density_on_regular_companion_domain
    {K : Set Plane} {α m c : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) ∧
      (upperCurvature K).restrict (regularCompanionDomain m) =
        (volume.restrict (regularCompanionDomain m)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  let b := max (Real.pi / 2) (affineNormalAngle m)
  let C := 8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24
  have hLb : Real.pi / 2 ≤ b := le_max_left _ _
  have hθb : affineNormalAngle m ≤ b := le_max_right _ _
  have hbπ : b ≤ Real.pi := max_le (by linarith [Real.pi_pos]) (affineNormalAngle_mem m).2.le
  have hfirst : (upperCurvature K).restrict (Ioo (Real.pi / 2) b) ≤
      ENNReal.ofReal C • volume.restrict (Ioo (Real.pi / 2) b) := by
    apply hK.curvature_restrict_le_on_proper_open_wing hproper haffine
      (by linarith [Real.pi_pos]) hbπ
    · exact fun ht => lt_irrefl _ ht.1
    · exact fun ht => (not_lt_of_ge hproper.le) ht.1
    · intro t ht hz
      have heq := (cos_add_mul_sin_eq_zero_iff
        ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_le hbπ⟩).mp hz
      by_cases hθ : affineNormalAngle m ≤ Real.pi / 2
      · have hb : b = Real.pi / 2 := max_eq_left hθ
        linarith only [ht.1, ht.2, hb]
      · have hb : b = affineNormalAngle m := max_eq_right (le_of_not_ge hθ)
        linarith only [ht.2, hb, heq]
  have hlast : (upperCurvature K).restrict (Ioo b Real.pi) ≤
      ENNReal.ofReal C • volume.restrict (Ioo b Real.pi) := by
    apply hK.curvature_restrict_le_on_proper_open_wing hproper haffine
      (by linarith [Real.pi_pos]) le_rfl
    · exact fun ht => (not_lt_of_ge hLb) ht.1
    · intro ht
      linarith only [ht.1, hLb, hproper]
    · intro t ht hz
      have heq := (cos_add_mul_sin_eq_zero_iff
        ⟨by linarith [ht.1, hLb, Real.pi_pos], ht.2⟩).mp hz
      linarith only [heq, hθb, ht.1]
  have hd : Disjoint (Ioo (Real.pi / 2) b) (Ioo b Real.pi) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hy.1.le) hx.2
  have hdom : (upperCurvature K).restrict (regularCompanionDomain m) ≤
      ENNReal.ofReal C • volume.restrict (regularCompanionDomain m) := by
    rw [regularCompanionDomain_eq_two]
    change (upperCurvature K).restrict (Ioo (Real.pi / 2) b ∪ Ioo b Real.pi) ≤
      ENNReal.ofReal C • volume.restrict (Ioo (Real.pi / 2) b ∪ Ioo b Real.pi)
    rw [Measure.restrict_union hd measurableSet_Ioo,
      Measure.restrict_union hd measurableSet_Ioo, smul_add]
    exact add_le_add hfirst hlast
  have hsub : regularCompanionDomain m ⊆ Ioo (Real.pi / 2) Real.pi := sdiff_subset
  letI : IsFiniteMeasure ((upperCurvature K).restrict (regularCompanionDomain m)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hsub).trans_lt measure_Ioo_lt_top).ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (regularCompanionDomain m)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hsub).trans_lt measure_Ioo_lt_top).ne
  exact exists_bounded_real_density_of_le_smul (by positivity) hdom

end AmbidextrousSofa
