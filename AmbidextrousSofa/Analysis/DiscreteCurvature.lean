module

public import AmbidextrousSofa.Analysis.FacetCurvature
public import MovingSofaOptimality.Balanced.CapGeometry

@[expose] public section

/-!
# Surface-area measure of an actual finite half-plane intersection

On every gap in its defining normal angles, the two supporting lines of
a compact convex half-plane intersection meet at an actual common corner.
The actual support vertex is constant there, so its Stieltjes surface-area
measure vanishes on the gap. Local nullity on the complement of the finite
normal set proves concentration on that set. The mass of any upper angular
interval is therefore exactly a finite sum of actual supporting-face atoms.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem sigma_Ioo_eq_zero_of_halfplane_gap {K : Set Plane}
    (hK : MovingSofaOptimality.IsConvexBody K) {ι : Type*} (angle height : ι → ℝ)
    (hKpoly : K = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i))
    (hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi) (hab : a < b) (hspan : b - a < Real.pi)
    (hgap : ∀ i, angle i ∉ Ioo a b) : MovingSofaOptimality.sigma K (Ioo a b) = 0 := by
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) hspan
  have hsinGap (i : ι) : ¬(0 < Real.sin (angle i - a) ∧ Real.sin (angle i - b) < 0) := by
    refine MovingSofaOptimality.mpc_not_gap hab ?_
    rcases le_or_gt (angle i) a with hia | hai
    · exact Or.inr ⟨by linarith [(hangle i).1, Real.pi_pos], hia⟩
    · exact Or.inl ⟨le_of_not_gt fun hib => hgap i ⟨hai, hib⟩, by linarith [(hangle i).2]⟩
  obtain ⟨q, hq, hqa, hqb⟩ := MovingSofaOptimality.mpc_corner hK hKpoly hsin hsinGap
  obtain ⟨hqa', -, -, hinterior⟩ := MovingSofaOptimality.mpc_corner_props hK hq hsin hqa hqb
  refine MovingSofaOptimality.sigma_Ioo_eq_zero_of_vplus_const hK hab (q := q) fun t ht => ?_
  rcases ht.1.eq_or_lt with rfl | hat
  · exact hqa'
  · exact (hinterior t (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith [ht.2]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr ht.2) (by linarith))).1

/-- The actual Stieltjes measure of a finite half-plane intersection is
zero away from its defining directions in the open upper semicircle. -/
theorem sigma_upper_sdiff_range_eq_zero {K : Set Plane}
    (hK : MovingSofaOptimality.IsConvexBody K) {ι : Type*} [Finite ι] (angle height : ι → ℝ)
    (hKpoly : K = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i))
    (hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi)) :
    MovingSofaOptimality.sigma K (Ioo 0 Real.pi \ range angle) = 0 := by
  refine measure_null_of_locally_null _ fun θ hθ => ?_
  -- a short open interval around `θ` that misses every defining direction
  obtain ⟨l, u, hθlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (((isOpen_Ioo.sdiff (finite_range angle).isClosed).inter isOpen_Ioo).mem_nhds
      (⟨hθ, by linarith, by linarith⟩ : θ ∈ (Ioo 0 Real.pi \ range angle) ∩ Ioo (θ - 1) (θ + 1)))
  have hlu := hθlu.1.trans hθlu.2
  obtain ⟨hl, hu⟩ := (Ioo_subset_Ioo_iff hlu).1 (hsub.trans (inter_subset_left.trans sdiff_subset))
  obtain ⟨hl', hu'⟩ := (Ioo_subset_Ioo_iff hlu).1 (hsub.trans inter_subset_right)
  exact ⟨Ioo l u, mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hθlu.1 hθlu.2),
    sigma_Ioo_eq_zero_of_halfplane_gap hK angle height hKpoly hangle hl hu hlu
      (by linarith [Real.pi_gt_three]) fun i hi => (hsub hi).1.2 (mem_range_self i)⟩

namespace FinitePolygon

variable {ι : Type*}

/-- All literal halfplanes of the polygon, including its four fixed box
walls. The extra directions are not hidden in a facet certificate. -/
def fullPolygonAngle (angle : ι → ℝ) : Fin 4 ⊕ ι → ℝ
  | Sum.inl i => ![0, Real.pi / 2, Real.pi, 3 * Real.pi / 2] i
  | Sum.inr i => angle i

def fullPolygonHeight (l r : ℝ) (height : ι → ℝ) : Fin 4 ⊕ ι → ℝ
  | Sum.inl i => ![r, 1, -l, 0] i
  | Sum.inr i => height i

theorem upperPolygon_eq_iInter_halfMinus (l r : ℝ) (angle height : ι → ℝ) :
    upperPolygon l r (fun i => unitNormal (angle i)) height =
      ⋂ i, MovingSofaOptimality.halfMinus (fullPolygonAngle angle i) (fullPolygonHeight l r height i) := by
  ext p
  simp [mem_upperPolygon_iff, Fin.forall_fin_succ, fullPolygonAngle, fullPolygonHeight,
    MovingSofaOptimality.halfMinus, MovingSofaOptimality.dot_uvec_zero,
    MovingSofaOptimality.dot_uvec_pi_div_two, MovingSofaOptimality.dot_uvec_pi,
    MovingSofaOptimality.dot_uvec_three_pi_div_two]
  exact ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ => ⟨⟨h2, h4, h1, h3⟩, h5⟩,
    fun ⟨⟨h2, h4, h1, h3⟩, h5⟩ => ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩⟩

theorem fullPolygonAngle_mem (angle : ι → ℝ)
    (hangle : ∀ i, angle i ∈ Icc 0 Real.pi) (i : Fin 4 ⊕ ι) :
    fullPolygonAngle angle i ∈ Icc 0 (2 * Real.pi) := by
  rcases i with i | i
  · fin_cases i <;> constructor <;> norm_num [fullPolygonAngle] <;> linarith [Real.pi_pos]
  · exact ⟨(hangle i).1, (hangle i).2.trans (by linarith [Real.pi_pos])⟩

def fullPolygonAngles [Fintype ι] (angle : ι → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fullPolygonAngle angle)

open Classical in
/-- Any upper angular set, including half-open intervals, has exactly the
sum of its actual polygon face atoms. Axes and the top were included when
proving concentration; intersecting with the set handles them literally. -/
theorem upperCurvature_eq_sum_fullPolygonAngles [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (angle : ι → ℝ)
    (hangle : ∀ i, angle i ∈ Icc 0 Real.pi)
    (hpoly : U = circumscription U (fun i => unitNormal (angle i)))
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi) :
    upperCurvature U s = ∑ t ∈ (fullPolygonAngles angle).filter (fun t => t ∈ s),
      upperCurvature U {t} := by
  have hnull : upperCurvature U (Ioo 0 Real.pi \ (fullPolygonAngles angle : Set ℝ)) = 0 := by
    rw [fullPolygonAngles, Finset.coe_image, Finset.coe_univ, image_univ]
    exact sigma_upper_sdiff_range_eq_zero hU.imported_isConvexBody _
      (fullPolygonHeight (horizontalLeft U) (horizontalRight U)
        (fun i => support U (unitNormal (angle i))))
      (hpoly.trans (upperPolygon_eq_iInter_halfMinus _ _ _ _)) (fullPolygonAngle_mem angle hangle)
  -- the measure is carried by the finitely many atoms in `s`
  rw [← measure_inter_conull' (measure_mono_null (sdiff_subset_sdiff_left hs) hnull),
    ← measure_biUnion_finset (fun x _ y _ hxy => disjoint_singleton.mpr hxy)
      fun t _ => measurableSet_singleton t]
  congr 1
  ext x
  simp [and_comm]

end FinitePolygon

end AmbidextrousSofa
