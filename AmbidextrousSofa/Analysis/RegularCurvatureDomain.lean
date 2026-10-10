import AmbidextrousSofa.Analysis.OpenWingCurvature
import AmbidextrousSofa.Analysis.AffineNormal

/-!
# The actual regular upper curvature domain

The central affine segment has one upward normal. Together with the top
normal this divides the open upper semicircle into at most three wings.
The open-wing estimates therefore yield one bounded measurable density
on the entire complement of those two normals. The remaining measure is
the restriction of the actual face measure to those actual normals.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem affineNormalAngle_zero (m : ℝ) :
    Real.cos (affineNormalAngle m) + m * Real.sin (affineNormalAngle m) = 0 := by
  simpa only [coordDot, unitNormal, one_mul, mul_one, sub_self, mul_zero] using
    coordDot_affineNormalAngle (1, m) m

theorem cos_add_mul_sin_eq_zero_iff {m t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    Real.cos t + m * Real.sin t = 0 ↔ t = affineNormalAngle m := by
  constructor
  · intro hz
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have htan : Real.tan (t - Real.pi / 2) = Real.tan (Real.arctan m) := by
      rw [Real.tan_arctan, Real.tan_eq_sin_div_cos,
        Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
      apply (div_eq_iff hs.ne').mpr
      linarith
    have hmem : t - Real.pi / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [ht.1, ht.2]
    have heq := Real.strictMonoOn_tan.injOn hmem (Real.arctan_mem_Ioo m) htan
    unfold affineNormalAngle
    linarith
  · rintro rfl
    exact affineNormalAngle_zero m

/-- The only removed upper normals are the top and the central affine normal. -/
def regularCurvatureDomain (m : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) Real.pi \ {Real.pi / 2, affineNormalAngle m}

theorem measurableSet_regularCurvatureDomain (m : ℝ) :
    MeasurableSet (regularCurvatureDomain m) :=
  measurableSet_Ioo.diff ((measurableSet_singleton _).insert _)

theorem regularCurvatureDomain_subset (m : ℝ) :
    regularCurvatureDomain m ⊆ Ioo (0 : ℝ) Real.pi :=
  sdiff_subset

theorem mem_regularCurvatureDomain_iff {m t : ℝ} :
    t ∈ regularCurvatureDomain m ↔
      0 < t ∧ t < Real.pi ∧ t ≠ Real.pi / 2 ∧
        Real.cos t + m * Real.sin t ≠ 0 := by
  simp only [regularCurvatureDomain, mem_sdiff, mem_Ioo, mem_insert_iff,
    mem_singleton_iff, not_or]
  constructor
  · rintro ⟨ht, htop, hcentral⟩
    exact ⟨ht.1, ht.2, htop, fun hz => hcentral
      ((cos_add_mul_sin_eq_zero_iff ht).mp hz)⟩
  · rintro ⟨ht0, htπ, htop, hcentral⟩
    exact ⟨⟨ht0, htπ⟩, htop, fun heq => hcentral
      ((cos_add_mul_sin_eq_zero_iff ⟨ht0, htπ⟩).mpr heq)⟩

theorem Ioo_sdiff_pair_eq_three {l a b r : ℝ}
    (hla : l ≤ a) (hab : a ≤ b) (hbr : b ≤ r) :
    Ioo l r \ {a, b} = Ioo l a ∪ Ioo a b ∪ Ioo b r := by
  ext x
  simp only [mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff, not_or, mem_union]
  constructor
  · rintro ⟨⟨hlx, hxr⟩, hxa, hxb⟩
    rcases lt_or_gt_of_ne hxa with hxa | hax
    · exact Or.inl (Or.inl ⟨hlx, hxa⟩)
    · rcases lt_or_gt_of_ne hxb with hxb | hbx
      · exact Or.inl (Or.inr ⟨hax, hxb⟩)
      · exact Or.inr ⟨hbx, hxr⟩
  · rintro ((h | h) | h)
    · exact ⟨⟨h.1, h.2.trans_le (hab.trans hbr)⟩,
        h.2.ne, (h.2.trans_le hab).ne⟩
    · exact ⟨⟨hla.trans_lt h.1, h.2.trans_le hbr⟩, h.1.ne', h.2.ne⟩
    · exact ⟨⟨(hla.trans hab).trans_lt h.1, h.2⟩,
        (hab.trans_lt h.1).ne', h.1.ne'⟩

theorem regularCurvatureDomain_eq_three (m : ℝ) :
    regularCurvatureDomain m =
      Ioo 0 (min (affineNormalAngle m) (Real.pi / 2)) ∪
      Ioo (min (affineNormalAngle m) (Real.pi / 2))
        (max (affineNormalAngle m) (Real.pi / 2)) ∪
      Ioo (max (affineNormalAngle m) (Real.pi / 2)) Real.pi := by
  have hθ := affineNormalAngle_mem m
  have hpair : ({Real.pi / 2, affineNormalAngle m} : Set ℝ) =
      {min (affineNormalAngle m) (Real.pi / 2),
        max (affineNormalAngle m) (Real.pi / 2)} := by
    by_cases h : affineNormalAngle m ≤ Real.pi / 2
    · rw [min_eq_left h, max_eq_right h]
      exact pair_comm _ _
    · rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
  rw [regularCurvatureDomain, hpair]
  exact Ioo_sdiff_pair_eq_three
    (le_min hθ.1.le (by positivity)) (min_le_max _ _)
    (max_le hθ.2.le (by linarith [Real.pi_pos]))

/-- Domination on each actual open wing gives domination on their full union. -/
theorem measure_restrict_regularCurvatureDomain_le
    {μ ν : Measure ℝ} {m : ℝ}
    (h : ∀ A B : ℝ, 0 ≤ A → B ≤ Real.pi → Real.pi / 2 ∉ Ioo A B →
      (∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) →
      μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B)) :
    μ.restrict (regularCurvatureDomain m) ≤ ν.restrict (regularCurvatureDomain m) := by
  let a := min (affineNormalAngle m) (Real.pi / 2)
  let b := max (affineNormalAngle m) (Real.pi / 2)
  have hθ := affineNormalAngle_mem m
  have ha0 : 0 ≤ a := le_min hθ.1.le (by positivity)
  have hbπ : b ≤ Real.pi := max_le hθ.2.le (by linarith [Real.pi_pos])
  have hab : a ≤ b := min_le_max _ _
  have haθ : a ≤ affineNormalAngle m := min_le_left _ _
  have haL : a ≤ Real.pi / 2 := min_le_right _ _
  have hθb : affineNormalAngle m ≤ b := le_max_left _ _
  have hLb : Real.pi / 2 ≤ b := le_max_right _ _
  have hfirst : μ.restrict (Ioo 0 a) ≤ ν.restrict (Ioo 0 a) := by
    apply h 0 a le_rfl (hab.trans hbπ)
    · intro ht
      linarith [ht.2]
    · intro t ht hz
      have heq := (cos_add_mul_sin_eq_zero_iff
        ⟨ht.1, ht.2.trans_le (hab.trans hbπ)⟩).mp hz
      linarith [ht.2]
  have hmiddle : μ.restrict (Ioo a b) ≤ ν.restrict (Ioo a b) := by
    apply h a b ha0 hbπ
    · intro ht
      by_cases hθL : affineNormalAngle m ≤ Real.pi / 2
      · have hb : b = Real.pi / 2 := max_eq_right hθL
        linarith [ht.2]
      · have ha : a = Real.pi / 2 := min_eq_right (le_of_not_ge hθL)
        linarith [ht.1]
    · intro t ht hz
      have heq := (cos_add_mul_sin_eq_zero_iff
        ⟨ha0.trans_lt ht.1, ht.2.trans_le hbπ⟩).mp hz
      by_cases hθL : affineNormalAngle m ≤ Real.pi / 2
      · have ha : a = affineNormalAngle m := min_eq_left hθL
        linarith [ht.1]
      · have hb : b = affineNormalAngle m := max_eq_left (le_of_not_ge hθL)
        linarith [ht.2]
  have hlast : μ.restrict (Ioo b Real.pi) ≤ ν.restrict (Ioo b Real.pi) := by
    apply h b Real.pi (ha0.trans hab) le_rfl
    · intro ht
      linarith [ht.1]
    · intro t ht hz
      have heq := (cos_add_mul_sin_eq_zero_iff
        ⟨(ha0.trans hab).trans_lt ht.1, ht.2⟩).mp hz
      linarith [ht.1]
  have hd12 : Disjoint (Ioo (0 : ℝ) a) (Ioo a b) := by
    apply disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1]
  have hd3 : Disjoint (Ioo (0 : ℝ) a ∪ Ioo a b) (Ioo b Real.pi) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · linarith [hx.2, hy.1]
    · linarith [hx.2, hy.1]
  rw [regularCurvatureDomain_eq_three]
  change μ.restrict ((Ioo 0 a ∪ Ioo a b) ∪ Ioo b Real.pi) ≤
    ν.restrict ((Ioo 0 a ∪ Ioo a b) ∪ Ioo b Real.pi)
  rw [Measure.restrict_union hd3 measurableSet_Ioo,
    Measure.restrict_union hd3 measurableSet_Ioo,
    Measure.restrict_union hd12 measurableSet_Ioo,
    Measure.restrict_union hd12 measurableSet_Ioo]
  exact add_le_add (add_le_add hfirst hmiddle) hlast

theorem IsFullCapMaximizer.curvature_density_on_regular_domain
    {K : Set Plane} (hK : IsFullCapMaximizer K) {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10) ∧
      (upperCurvature K).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  let C := 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10
  have hcoarse : (upperCurvature K).restrict (regularCurvatureDomain m) ≤
      ENNReal.ofReal C • volume.restrict (regularCurvatureDomain m) := by
    have h : (upperCurvature K).restrict (regularCurvatureDomain m) ≤
        (ENNReal.ofReal C • (volume : Measure ℝ)).restrict (regularCurvatureDomain m) := by
      apply measure_restrict_regularCurvatureDomain_le
      intro A B hA hB htop hperp
      obtain ⟨ρ, _, _, hρC, heq⟩ :=
        hK.curvature_density_sharp_on_open_wing haffine hA hB htop hperp
      rw [heq, Measure.restrict_smul, ← withDensity_const]
      exact withDensity_mono (Eventually.of_forall (fun t =>
        ENNReal.ofReal_le_ofReal (hρC t)))
    simpa only [Measure.restrict_smul] using h
  have hsharp : (upperCurvature K).restrict (regularCurvatureDomain m) ≤
      (volume.restrict (regularCurvatureDomain m)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t))) := by
    have h : (upperCurvature K).restrict (regularCurvatureDomain m) ≤
        ((volume : Measure ℝ).withDensity
          (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t)))).restrict
            (regularCurvatureDomain m) := by
      apply measure_restrict_regularCurvatureDomain_le
      intro A B hA hB htop hperp
      obtain ⟨ρ, _, hρ, _, heq⟩ :=
        hK.curvature_density_sharp_on_open_wing haffine hA hB htop hperp
      rw [heq, Measure.restrict_withDensity measurableSet_Ioo]
      exact withDensity_mono (Eventually.of_forall (fun t =>
        ENNReal.ofReal_le_ofReal (hρ t).2))
    simpa only [Measure.restrict_withDensity (measurableSet_regularCurvatureDomain m)] using h
  letI : IsFiniteMeasure ((upperCurvature K).restrict (regularCurvatureDomain m)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono (regularCurvatureDomain_subset m)).trans_lt measure_Ioo_lt_top).ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (regularCurvatureDomain m)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono (regularCurvatureDomain_subset m)).trans_lt measure_Ioo_lt_top).ne
  exact exists_real_density_of_two_bounds (by positivity)
    (continuous_sourceKappa.measurable.comp hK.isCap.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) hcoarse hsharp

/-- The exceptional part is exactly the actual measure on the two
exceptional face normals; no other singular upper curvature remains. -/
theorem curvature_restrict_upper_decomposition (K : Set Plane) (m : ℝ) :
    (upperCurvature K).restrict (Ioo (0 : ℝ) Real.pi) =
      (upperCurvature K).restrict (regularCurvatureDomain m) +
        (upperCurvature K).restrict {Real.pi / 2, affineNormalAngle m} := by
  have hpair : ({Real.pi / 2, affineNormalAngle m} : Set ℝ) ⊆ Ioo (0 : ℝ) Real.pi := by
    intro t ht
    rcases ht with rfl | ht
    · constructor <;> linarith [Real.pi_pos]
    · rcases ht with rfl
      exact affineNormalAngle_mem m
  have heq : regularCurvatureDomain m ∪ {Real.pi / 2, affineNormalAngle m} =
      Ioo (0 : ℝ) Real.pi := by
    exact sdiff_union_of_subset hpair
  rw [← heq, Measure.restrict_union disjoint_sdiff_left
    ((measurableSet_singleton _).insert _)]

end AmbidextrousSofa
