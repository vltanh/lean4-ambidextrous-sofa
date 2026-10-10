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
  have hcover : (⋃ n : ℕ, Ioc (s + selectionRate n) (t - selectionRate n)) = Ioo s t := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      have hd := selectionRate_pos n
      exact ⟨by linarith only [hn.1, hd], by linarith only [hn.2, hd]⟩
    · intro hx
      obtain ⟨n, hn₁, hn₂⟩ :=
        ((selectionRate_tendsto.eventually (Iio_mem_nhds (sub_pos.mpr hx.1))).and
          (selectionRate_tendsto.eventually (Iio_mem_nhds (sub_pos.mpr hx.2)))).exists
      exact mem_iUnion.mpr ⟨n, ⟨by linarith only [hn₁], by linarith only [hn₂]⟩⟩
  rw [← hcover]
  apply Measure.restrict_iUnion_congr.mpr
  intro n
  apply hinterval
  intro x hx
  have hd := selectionRate_pos n
  exact ⟨by linarith only [hx.1, hd], by linarith only [hx.2, hd]⟩

/-- The finite neighboring-wall estimate on a closed angular interval, with one boundary mesh
cell: the bound `innerSourceMass_sum_interval_le` of `HorizontalCutoff` (not imported here),
stated for `innerAngularMass`, whose filter carries the classical decidability instance. -/
private theorem innerAngularMass_Icc_le {U : Set Plane} (hU : IsDownwardCap U)
    {R s t : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (hst : s ≤ t) :
    innerAngularMass U (dyadic level) (Icc s t) ≤ (4 * R + 12) * (t - s + mesh level) := by
  classical
  have hmesh := sum_mesh_interval_sources_le level hst
  unfold innerAngularMass
  calc
    _ ≤ ∑ j ∈ _, (4 * R + 12) * mesh level :=
      Finset.sum_le_sum (fun j _ => innerSourceMass_dyadic_le hU hR hbox level j)
    _ = (4 * R + 12) * ∑ j ∈ _, mesh level := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Eq.trans_le (by congr 1; exact Finset.filter_congr_decidable _ _ _) hmesh) (by linarith)

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem finite_angular_mass (n : ℕ) {E : Set ℝ} (hE : MeasurableSet E) :
    (J.finiteMeasure n : Measure Plane).real (E ×ˢ univ) =
      innerAngularMass (J.caps n) (dyadic (J.level n)) E := by
  have hlr := horizontalLeft_le_horizontalRight (J.isCap n).nonempty (J.isCap n).isCompact
  exact innerJointMeasure_angular_mass (J.caps n) (dyadic (J.level n))
    (show horizontalLeft (J.caps n) + capWidth (J.caps n) / 4 ≤
      horizontalRight (J.caps n) - capWidth (J.caps n) / 4 by unfold capWidth; linarith) hE

/-- The boundary mesh cell disappears in the common weak limit. -/
theorem angular_open_mass_le {s t : ℝ} (hst : s ≤ t) :
    (J.measure : Measure Plane).real (Ioo s t ×ˢ univ) ≤
      (4 * (|a| + |b| + 1) + 12) * (t - s) := by
  let R := |a| + |b| + 1
  let K := 4 * R + 12
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; linarith only [hR]
  have hfinite (n : ℕ) :
      (J.finiteMeasure n : Measure Plane).real (Ioo s t ×ˢ univ) ≤
        K * (t - s + mesh (J.level n)) := by
    calc
      _ ≤ (J.finiteMeasure n : Measure Plane).real (Icc s t ×ˢ univ) :=
        measureReal_mono (prod_mono Ioo_subset_Icc_self Subset.rfl)
      _ = innerAngularMass (J.caps n) (dyadic (J.level n)) (Icc s t) :=
        J.finite_angular_mass n measurableSet_Icc
      _ ≤ K * (t - s + mesh (J.level n)) :=
        innerAngularMass_Icc_le (J.isCap n) hR
          (subset_symmetricBox_of_horizontalBox (J.selected n).inBox) (J.level n) hst
  have hmesh : Tendsto (fun n => mesh (J.level n)) (sourceLimitFilter : Filter ℕ) (𝓝 0) :=
    (mesh_tendsto.comp J.level_tendsto).mono_left sourceLimitFilter_le_atTop
  have hboundlim : Tendsto (fun n => K * (t - s + mesh (J.level n)))
      (sourceLimitFilter : Filter ℕ) (𝓝 (K * (t - s))) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hmesh).const_mul K
  exact finiteMeasure_real_open_le_of_tendsto_bound J.converges
    (isOpen_Ioo.prod isOpen_univ) (mul_nonneg hK (sub_nonneg.mpr hst))
    hboundlim (Eventually.of_forall hfinite)

/-- No angular atom survives, even at a distinguished normal. -/
theorem angular_fiber_eq_zero (θ : ℝ) :
    (J.measure : Measure Plane) ({θ} ×ˢ univ) = 0 := by
  have hbound (n : ℕ) :
      (J.measure : Measure Plane).real ({θ} ×ˢ univ) ≤
        (4 * (|a| + |b| + 1) + 12) * (2 * selectionRate n) := by
    have hd := selectionRate_pos n
    calc
      _ ≤ (J.measure : Measure Plane).real
          (Ioo (θ - selectionRate n) (θ + selectionRate n) ×ˢ univ) := by
        apply measureReal_mono _ (measure_ne_top _ _)
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only [mem_singleton_iff] at hx
        subst x
        exact ⟨⟨by linarith only [hd], by linarith only [hd]⟩, hy⟩
      _ ≤ (4 * (|a| + |b| + 1) + 12) *
          ((θ + selectionRate n) - (θ - selectionRate n)) :=
        J.angular_open_mass_le (by linarith only [hd])
      _ = _ := by ring
  have hzero : Tendsto (fun n =>
      (4 * (|a| + |b| + 1) + 12) * (2 * selectionRate n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (selectionRate_tendsto.const_mul 2).const_mul (4 * (|a| + |b| + 1) + 12)
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  exact le_antisymm (ge_of_tendsto hzero (Eventually.of_forall hbound)) measureReal_nonneg

theorem angular_Ioc_frontier_eq_zero (s t : ℝ) :
    (J.measure : Measure Plane) (frontier (Ioc s t ×ˢ (univ : Set ℝ))) = 0 := by
  by_cases hst : s < t
  · have hprod : ({s, t} : Set ℝ) ×ˢ (univ : Set ℝ) =
        ({s} ×ˢ univ) ∪ ({t} ×ˢ univ) := by
      ext z
      simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true, mem_union]
    rw [frontier_prod_univ_eq, frontier_Ioc hst, hprod]
    exact measure_union_null (J.angular_fiber_eq_zero s) (J.angular_fiber_eq_zero t)
  · rw [Ioc_eq_empty_of_le (le_of_not_gt hst), empty_prod, frontier_empty]
    exact measure_empty

theorem angular_Ioc_mass_tendsto (s t : ℝ) :
    Tendsto (fun n => (J.finiteMeasure n : Measure Plane).real (Ioc s t ×ˢ univ))
      (sourceLimitFilter : Filter ℕ) (𝓝 ((J.measure : Measure Plane).real (Ioc s t ×ˢ univ))) :=
  finiteMeasure_tendsto_real_apply_of_null_frontier J.converges
    (J.angular_Ioc_frontier_eq_zero s t)

theorem angular_Ioc_real_eq_curvature
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m) :
    (J.measure : Measure Plane).real (Ioc s t ×ˢ univ) =
      (upperCurvature target).real (Ioc s t) :=
  tendsto_nhds_unique (J.angular_Ioc_mass_tendsto s t)
    (J.angular_mass_tendsto hTarget hheight haffine hTargetBox hleft hright hst hregular)

theorem angular_Ioc_eq_curvature
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m) :
    (J.measure : Measure Plane) (Ioc s t ×ˢ univ) = upperCurvature target (Ioc s t) := by
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) measure_Ioc_lt_top.ne).mp
  exact J.angular_Ioc_real_eq_curvature hTarget hheight haffine hTargetBox hleft hright hst hregular

/-- The marginal retains the literal full upper-normal coordinate. -/
def angularMeasure : Measure ℝ := (J.measure : Measure Plane).map Prod.fst

instance angularMeasure_isFinite : IsFiniteMeasure J.angularMeasure :=
  (J.measure : Measure Plane).isFiniteMeasure_map Prod.fst

theorem angularMeasure_apply {E : Set ℝ} (hE : MeasurableSet E) :
    J.angularMeasure E = (J.measure : Measure Plane) (E ×ˢ univ) := by
  rw [angularMeasure, Measure.map_apply measurable_fst hE, prod_univ]

theorem angularMeasure_restrict_Ioc_eq_curvature
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hregular : Icc s t ⊆ regularCurvatureDomain m) :
    J.angularMeasure.restrict (Ioc s t) = (upperCurvature target).restrict (Ioc s t) := by
  apply Measure.ext_of_Ioc
  intro x y _hxy
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
  have hinter : Ioc x y ∩ Ioc s t = Ioc (max x s) (min y t) := by
    ext z
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [hinter]
  by_cases hspan : max x s ≤ min y t
  · rw [J.angularMeasure_apply measurableSet_Ioc]
    exact J.angular_Ioc_eq_curvature hTarget hheight haffine hTargetBox hleft hright hspan
      (fun z hz => hregular ⟨(le_max_right _ _).trans hz.1, hz.2.trans (min_le_right _ _)⟩)
  · simp only [Ioc_eq_empty_of_le (le_of_not_ge hspan), measure_empty]

theorem angularMeasure_restrict_Ioo_eq_curvature
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hregular : Ioo s t ⊆ regularCurvatureDomain m) :
    J.angularMeasure.restrict (Ioo s t) = (upperCurvature target).restrict (Ioo s t) := by
  apply measure_restrict_Ioo_eq_of_closed_subintervals
  intro x y hxy
  exact J.angularMeasure_restrict_Ioc_eq_curvature hTarget hheight haffine hTargetBox
    hleft hright (hxy.trans hregular)

/-- The marginal equality holds on the entire literal regular domain,
with its actual top and affine normals removed. -/
theorem angularMeasure_restrict_regular_eq_curvature
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    J.angularMeasure.restrict (regularCurvatureDomain m) =
      (upperCurvature target).restrict (regularCurvatureDomain m) := by
  rw [regularCurvatureDomain_eq_three, Measure.restrict_union_congr,
    Measure.restrict_union_congr]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply J.angularMeasure_restrict_Ioo_eq_curvature hTarget hheight haffine hTargetBox
      hleft hright
    intro x hx
    rw [regularCurvatureDomain_eq_three]
    exact Or.inl (Or.inl hx)
  · apply J.angularMeasure_restrict_Ioo_eq_curvature hTarget hheight haffine hTargetBox
      hleft hright
    intro x hx
    rw [regularCurvatureDomain_eq_three]
    exact Or.inl (Or.inr hx)
  · apply J.angularMeasure_restrict_Ioo_eq_curvature hTarget hheight haffine hTargetBox
      hleft hright
    intro x hx
    rw [regularCurvatureDomain_eq_three]
    exact Or.inr hx

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
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) :=
  (J.angularMeasure_restrict_regular_eq_curvature hTarget hheight haffine hTargetBox
    hleft hright).trans heq

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
