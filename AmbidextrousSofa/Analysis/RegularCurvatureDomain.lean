module

public import AmbidextrousSofa.Analysis.OpenWingCurvature
public import AmbidextrousSofa.Analysis.AffineNormal

@[expose] public section

/-!
# The actual regular upper curvature domain

The central affine segment has one upward normal. Together with the top
normal this divides the open upper semicircle into at most three wings.
The open-wing estimates therefore yield one bounded measurable density
on the entire complement of those two normals. The remaining measure is
the restriction of the actual face measure to those actual normals. The
file also records that sine and cosine are positive on the open first
quarter.
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
  refine ⟨fun hz => ?_, fun h => h ▸ affineNormalAngle_zero m⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have := Real.strictMonoOn_tan.injOn (⟨by linarith [ht.1], by linarith [ht.2]⟩ :
      t - Real.pi / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (Real.arctan_mem_Ioo m) (by
    rw [Real.tan_arctan, Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two,
      Real.cos_sub_pi_div_two, div_eq_iff hs.ne']
    linarith)
  unfold affineNormalAngle
  linarith

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
  simp only [regularCurvatureDomain, Set.mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff,
    not_or, and_assoc]
  exact and_congr_right fun h0 => and_congr_right fun hπ => and_congr_right fun _ =>
    not_congr (cos_add_mul_sin_eq_zero_iff ⟨h0, hπ⟩).symm

theorem regularCurvatureDomain_eq_three (m : ℝ) :
    regularCurvatureDomain m =
      Ioo 0 (min (affineNormalAngle m) (Real.pi / 2)) ∪
      Ioo (min (affineNormalAngle m) (Real.pi / 2))
        (max (affineNormalAngle m) (Real.pi / 2)) ∪
      Ioo (max (affineNormalAngle m) (Real.pi / 2)) Real.pi := by
  have hθ := affineNormalAngle_mem m
  have := Real.pi_pos
  ext x
  simp only [regularCurvatureDomain, Set.mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff,
    mem_union]
  grind

/-- Domination on each actual open wing gives domination on their full union. -/
theorem measure_restrict_regularCurvatureDomain_le
    {μ ν : Measure ℝ} {m : ℝ}
    (h : ∀ A B : ℝ, 0 ≤ A → B ≤ Real.pi → Real.pi / 2 ∉ Ioo A B →
      (∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) →
      μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B)) :
    μ.restrict (regularCurvatureDomain m) ≤ ν.restrict (regularCurvatureDomain m) := by
  have hθ := affineNormalAngle_mem m
  have key {A B : ℝ} (hA : 0 ≤ A) (hB : B ≤ Real.pi) (h1 : Real.pi / 2 ∉ Ioo A B)
      (h2 : affineNormalAngle m ∉ Ioo A B) : μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B) :=
    h A B hA hB h1 fun t ht hz => h2 ((cos_add_mul_sin_eq_zero_iff
      ⟨hA.trans_lt ht.1, ht.2.trans_le hB⟩).mp hz ▸ ht)
  have hd {x y z w : ℝ} (h : y ≤ z) : Disjoint (Ioo x y) (Ioo z w) :=
    disjoint_left.2 fun t h1 h2 => lt_irrefl t ((h1.2.trans_le h).trans h2.1)
  have ha0 : 0 ≤ min (affineNormalAngle m) (Real.pi / 2) := le_min hθ.1.le (by positivity)
  have hbπ : max (affineNormalAngle m) (Real.pi / 2) ≤ Real.pi :=
    max_le hθ.2.le (by linarith [Real.pi_pos])
  simp only [regularCurvatureDomain_eq_three, Measure.restrict_union
    ((hd min_le_max).union_left (hd le_rfl)) measurableSet_Ioo,
    Measure.restrict_union (hd le_rfl) measurableSet_Ioo]
  refine add_le_add (add_le_add (key le_rfl (min_le_max.trans hbπ) ?_ ?_) (key ha0 hbπ ?_ ?_))
    (key (ha0.trans min_le_max) le_rfl ?_ ?_)
  all_goals grind

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
  have hfin {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] :
      IsFiniteMeasure (μ.restrict (regularCurvatureDomain m)) := isFiniteMeasure_restrict.mpr
    ((measure_mono (regularCurvatureDomain_subset m)).trans_lt measure_Ioo_lt_top).ne
  refine exists_real_density_of_two_bounds (by positivity)
    (continuous_sourceKappa.measurable.comp hK.isCap.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) ?_ ?_
  · rw [← Measure.restrict_smul]
    refine measure_restrict_regularCurvatureDomain_le fun A B hA hB htop hperp => ?_
    obtain ⟨ρ, -, -, hρC, heq⟩ := hK.curvature_density_sharp_on_open_wing haffine hA hB htop hperp
    rw [heq, Measure.restrict_smul, ← withDensity_const]
    exact withDensity_mono (.of_forall fun t => ENNReal.ofReal_le_ofReal (hρC t))
  · rw [← restrict_withDensity (measurableSet_regularCurvatureDomain m)]
    refine measure_restrict_regularCurvatureDomain_le fun A B hA hB htop hperp => ?_
    obtain ⟨ρ, -, hρ, -, heq⟩ := hK.curvature_density_sharp_on_open_wing haffine hA hB htop hperp
    rw [heq, restrict_withDensity measurableSet_Ioo]
    exact withDensity_mono (.of_forall fun t => ENNReal.ofReal_le_ofReal (hρ t).2)

end AmbidextrousSofa
