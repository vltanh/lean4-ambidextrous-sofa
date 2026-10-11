module

public import AmbidextrousSofa.Analysis.JointSourceLimit
public import AmbidextrousSofa.Measure.FiniteMeasurePortmanteau

@[expose] public section

/-!
# The angular marginal of the common source limit

The finite neighboring-wall bound passes to open angular strips. It
forces every angular fiber of the common weak limit to have zero mass,
including the axis, top, and affine normals. Thus interval masses converge
along the same filter that already identifies the selected source masses
with the actual curvature. This identifies the angular marginal on every
regular interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid

/-- Equality on every compactly contained angular interval determines
the restrictions to the open interval. The cover is a literal sequence
of inset intervals, so no boundary atom is added. -/
theorem measure_restrict_Ioo_eq_of_closed_subintervals
    {μ ν : Measure ℝ} {s t : ℝ}
    (hinterval : ∀ x y : ℝ, Icc x y ⊆ Ioo s t →
      μ.restrict (Ioc x y) = ν.restrict (Ioc x y)) :
    μ.restrict (Ioo s t) = ν.restrict (Ioo s t) := by
  have h (x y : ℝ) (hx : s < x) (_ : x ≤ y) (hy : y < t) :
      μ.restrict (Ioo x y) = ν.restrict (Ioo x y) := by
    rw [← Measure.restrict_restrict_of_subset Ioo_subset_Ioc_self,
      hinterval x y (Icc_subset_Ioo hx hy), Measure.restrict_restrict_of_subset Ioo_subset_Ioc_self]
  exact le_antisymm
    (measure_restrict_Ioo_le_of_compactly_contained fun x y h₁ h₂ h₃ => (h x y h₁ h₂ h₃).le)
    (measure_restrict_Ioo_le_of_compactly_contained fun x y h₁ h₂ h₃ => (h x y h₁ h₂ h₃).ge)

/-- The finite neighboring-wall estimate on a closed angular interval, with one boundary mesh
cell: the bound `innerSourceMass_sum_interval_le` of `HorizontalCutoff` (not imported here),
stated for `innerAngularMass`, whose filter carries the classical decidability instance. -/
private theorem innerAngularMass_Icc_le {U : Set Plane} (hU : IsDownwardCap U)
    {R s t : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (hst : s ≤ t) :
    innerAngularMass U (dyadic level) (Icc s t) ≤ (4 * R + 12) * (t - s + mesh level) := by
  unfold innerAngularMass
  refine (Finset.sum_le_sum fun j _ => innerSourceMass_dyadic_le hU hR hbox level j).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (by convert sum_mesh_interval_sources_le level hst)
    (by linarith)

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

/-- The boundary mesh cell disappears in the common weak limit. -/
theorem angular_open_mass_le {s t : ℝ} (hst : s ≤ t) :
    (J.measure : Measure Plane).real (Ioo s t ×ˢ univ) ≤
      (4 * (|a| + |b| + 1) + 12) * (t - s) := by
  have hB := (((mesh_tendsto.comp J.level_tendsto).mono_left sourceLimitFilter_le_atTop).const_add
    (t - s)).const_mul (4 * (|a| + |b| + 1) + 12)
  rw [add_zero] at hB
  refine finiteMeasure_real_open_le_of_tendsto_bound J.converges (isOpen_Ioo.prod isOpen_univ)
    (mul_nonneg (by positivity) (sub_nonneg.2 hst)) hB (.of_forall fun n => ?_)
  have hlr := horizontalLeft_le_horizontalRight (J.isCap n).nonempty (J.isCap n).isCompact
  calc _ ≤ (J.finiteMeasure n : Measure Plane).real (Icc s t ×ˢ univ) :=
        measureReal_mono (prod_mono Ioo_subset_Icc_self Subset.rfl)
    _ = innerAngularMass (J.caps n) (dyadic (J.level n)) (Icc s t) :=
        innerJointMeasure_angular_mass (J.caps n) (dyadic (J.level n))
          (show horizontalLeft (J.caps n) + capWidth (J.caps n) / 4 ≤
            horizontalRight (J.caps n) - capWidth (J.caps n) / 4 by unfold capWidth; linarith)
          measurableSet_Icc
    _ ≤ _ := innerAngularMass_Icc_le (J.isCap n) (by positivity)
        (subset_symmetricBox_of_horizontalBox (J.selected n).inBox) _ hst

/-- No angular atom survives, even at a distinguished normal. -/
theorem angular_fiber_eq_zero (θ : ℝ) :
    (J.measure : Measure Plane) ({θ} ×ˢ univ) = 0 := by
  have hB := (selectionRate_tendsto.const_mul 2).const_mul (4 * (|a| + |b| + 1) + 12)
  rw [mul_zero, mul_zero] at hB
  refine (measureReal_eq_zero_iff (measure_ne_top _ _)).1
    (le_antisymm (ge_of_tendsto' hB fun n => ?_) measureReal_nonneg)
  have hd := selectionRate_pos n
  calc _ ≤ (J.measure : Measure Plane).real
        (Ioo (θ - selectionRate n) (θ + selectionRate n) ×ˢ univ) :=
      measureReal_mono (prod_mono (singleton_subset_iff.2 ⟨by linarith, by linarith⟩) Subset.rfl)
    _ ≤ _ := J.angular_open_mass_le (by linarith)
    _ = (4 * (|a| + |b| + 1) + 12) * (2 * selectionRate n) := by ring

theorem angular_Ioc_eq_curvature
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m) :
    (J.measure : Measure Plane) (Ioc s t ×ˢ univ) = upperCurvature target (Ioc s t) := by
  have hfrontier : (J.measure : Measure Plane) (frontier (Ioc s t ×ˢ (univ : Set ℝ))) = 0 := by
    rcases hst.lt_or_eq with hst | rfl
    · rw [frontier_prod_univ_eq, frontier_Ioc hst, insert_eq, union_prod]
      exact measure_union_null (J.angular_fiber_eq_zero s) (J.angular_fiber_eq_zero t)
    · simp
  exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) measure_Ioc_lt_top.ne).1
    (tendsto_nhds_unique (finiteMeasure_tendsto_real_apply_of_null_frontier J.converges hfrontier)
      (J.angular_mass_tendsto hTarget hheight haffine hTargetBox hleft hright hst hregular))

/-- The marginal retains the literal full upper-normal coordinate. -/
def angularMeasure : Measure ℝ := (J.measure : Measure Plane).map Prod.fst

instance angularMeasure_isFinite : IsFiniteMeasure J.angularMeasure :=
  (J.measure : Measure Plane).isFiniteMeasure_map Prod.fst

/-- The marginal equality holds on the entire literal regular domain,
with its actual top and affine normals removed. -/
theorem angularMeasure_restrict_regular_eq_density
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    J.angularMeasure.restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hsub := (regularCurvatureDomain_eq_three m).ge
  have h {u v : ℝ} (huv : Ioo u v ⊆ regularCurvatureDomain m) :
      J.angularMeasure.restrict (Ioo u v) = (upperCurvature target).restrict (Ioo u v) := by
    refine measure_restrict_Ioo_eq_of_closed_subintervals fun s t hst =>
      Measure.ext_of_Ioc _ _ fun x y _ => ?_
    rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
      Ioc_inter_Ioc]
    by_cases hspan : max x s ≤ min y t
    · rw [angularMeasure, Measure.map_apply measurable_fst measurableSet_Ioc, ← prod_univ]
      exact J.angular_Ioc_eq_curvature hTarget hheight haffine hTargetBox hleft hright hspan
        fun z hz => huv (hst ⟨(le_max_right _ _).trans hz.1, hz.2.trans (min_le_right _ _)⟩)
    · simp only [Ioc_eq_empty_of_le (le_of_not_ge hspan), measure_empty]
  rw [← heq, regularCurvatureDomain_eq_three, Measure.restrict_union_congr,
    Measure.restrict_union_congr]
  exact ⟨⟨h fun x hx => hsub (.inl (.inl hx)), h fun x hx => hsub (.inl (.inr hx))⟩,
    h fun x hx => hsub (.inr hx)⟩

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
