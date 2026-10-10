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
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr hab) hspan
  have hsinGap : ∀ i, ¬(0 < Real.sin (angle i - a) ∧ Real.sin (angle i - b) < 0) := by
    intro i
    apply MovingSofaOptimality.mpc_not_gap hab
    by_cases hia : angle i ≤ a
    · right
      exact ⟨by linarith [(hangle i).1, Real.pi_pos], hia⟩
    · have hai : a < angle i := lt_of_not_ge hia
      have hbi : b ≤ angle i := le_of_not_gt (fun hib => hgap i ⟨hai, hib⟩)
      left
      exact ⟨hbi, by linarith [(hangle i).2]⟩
  obtain ⟨q, hq, hqa, hqb⟩ := MovingSofaOptimality.mpc_corner hK hKpoly hsin hsinGap
  obtain ⟨hqaVertex, hqbVertex, hsupport, hinterior⟩ :=
    MovingSofaOptimality.mpc_corner_props hK hq hsin hqa hqb
  apply MovingSofaOptimality.sigma_Ioo_eq_zero_of_vplus_const hK hab
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact hqaVertex
  · exact (hinterior t
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith [ht.2]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr ht.2) (by linarith))).1

/-- The actual Stieltjes measure of a finite half-plane intersection is
zero away from its defining directions in the open upper semicircle. -/
theorem sigma_upper_sdiff_range_eq_zero {K : Set Plane}
    (hK : MovingSofaOptimality.IsConvexBody K) {ι : Type*} [Finite ι] (angle height : ι → ℝ)
    (hKpoly : K = ⋂ i, MovingSofaOptimality.halfMinus (angle i) (height i))
    (hangle : ∀ i, angle i ∈ Icc 0 (2 * Real.pi)) :
    MovingSofaOptimality.sigma K (Ioo 0 Real.pi \ range angle) = 0 := by
  let S := Ioo 0 Real.pi \ range angle
  have hopen : IsOpen S := isOpen_Ioo.sdiff (finite_range angle).isClosed
  apply measure_null_of_locally_null S
  intro θ hθ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen θ hθ
  let δ := min r (min θ (Real.pi - θ)) / 2
  have hθ0 : 0 < θ := hθ.1.1
  have hθπ : θ < Real.pi := hθ.1.2
  have hmin : 0 < min r (min θ (Real.pi - θ)) :=
    lt_min hr (lt_min hθ0 (sub_pos.mpr hθπ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by
    dsimp [δ]; linarith [min_le_left r (min θ (Real.pi - θ))]
  have hδθ : δ ≤ θ / 2 := by
    dsimp [δ]
    linarith [(min_le_right r (min θ (Real.pi - θ))).trans (min_le_left θ (Real.pi - θ))]
  have hδπ : δ ≤ (Real.pi - θ) / 2 := by
    dsimp [δ]
    linarith [(min_le_right r (min θ (Real.pi - θ))).trans (min_le_right θ (Real.pi - θ))]
  have hinterval : Ioo (θ - δ) (θ + δ) ⊆ S := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hy.1, hy.2]
  refine ⟨Ioo (θ - δ) (θ + δ),
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  apply sigma_Ioo_eq_zero_of_halfplane_gap hK angle height hKpoly hangle
    (by linarith) (by linarith) (by linarith) (by linarith)
  intro i hi
  exact (hinterval hi).2 (mem_range_self i)

open Classical in
/-- A finite support description gives a literal sum of singleton masses.
The argument uses monotonicity and countable additivity, including zero atoms. -/
theorem measure_eq_sum_singletons_of_sdiff_null (μ : Measure ℝ) (F : Finset ℝ)
    (s : Set ℝ) [DecidablePred (fun t => t ∈ s)] (hnull : μ (s \ (F : Set ℝ)) = 0) :
    μ s = ∑ t ∈ F.filter (fun t => t ∈ s), μ {t} := by
  classical
  have hinter : μ (s ∩ (F : Set ℝ)) = μ s := by
    apply le_antisymm (measure_mono inter_subset_left)
    have h := measure_le_inter_add_sdiff (μ := μ) s (F : Set ℝ)
    simpa only [hnull, add_zero] using h
  have hset : s ∩ (F : Set ℝ) = ⋃ t ∈ F.filter (fun t => t ∈ s), ({t} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, Finset.mem_coe, mem_iUnion, Finset.mem_filter,
      mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht.2, ht.1⟩
  rw [← hinter, hset]
  apply measure_biUnion_finset
  · intro x hx y hy hxy
    exact disjoint_singleton.mpr hxy
  · intro t ht
    exact measurableSet_singleton t

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
  rw [mem_upperPolygon_iff]
  simp only [mem_iInter, Sum.forall]
  constructor
  · rintro ⟨hpx, hpy, hsupport⟩
    constructor
    · intro i
      fin_cases i <;>
        simp [fullPolygonAngle, fullPolygonHeight,
          MovingSofaOptimality.halfMinus, MovingSofaOptimality.dot_uvec_zero,
          MovingSofaOptimality.dot_uvec_pi_div_two, MovingSofaOptimality.dot_uvec_pi,
          MovingSofaOptimality.dot_uvec_three_pi_div_two] <;>
        linarith [hpx.1, hpx.2, hpy.1, hpy.2]
    · intro i
      exact hsupport i
  · rintro ⟨hbox, hsupport⟩
    have hright := hbox 0
    have htop := hbox 1
    have hleft := hbox 2
    have hbottom := hbox 3
    simp [fullPolygonAngle, fullPolygonHeight,
      MovingSofaOptimality.halfMinus, MovingSofaOptimality.dot_uvec_zero,
      MovingSofaOptimality.dot_uvec_pi_div_two, MovingSofaOptimality.dot_uvec_pi,
      MovingSofaOptimality.dot_uvec_three_pi_div_two] at hright htop hleft hbottom
    exact ⟨⟨by linarith, hright⟩, ⟨by linarith, htop⟩, hsupport⟩

theorem fullPolygonAngle_mem (angle : ι → ℝ)
    (hangle : ∀ i, angle i ∈ Icc 0 Real.pi) (i : Fin 4 ⊕ ι) :
    fullPolygonAngle angle i ∈ Icc 0 (2 * Real.pi) := by
  cases i with
  | inl i =>
    fin_cases i <;> constructor <;> norm_num [fullPolygonAngle] <;>
      linarith [Real.pi_pos]
  | inr i =>
    exact ⟨(hangle i).1, (hangle i).2.trans (by linarith [Real.pi_pos])⟩

def fullPolygonAngles [Fintype ι] (angle : ι → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fullPolygonAngle angle)

theorem coe_fullPolygonAngles [Fintype ι] (angle : ι → ℝ) :
    (fullPolygonAngles angle : Set ℝ) = range (fullPolygonAngle angle) := by
  classical
  simp only [fullPolygonAngles, Finset.coe_image, Finset.coe_univ, image_univ]

theorem upperCurvature_sdiff_fullPolygonAngles [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (angle : ι → ℝ)
    (hangle : ∀ i, angle i ∈ Icc 0 Real.pi)
    (hpoly : U = circumscription U (fun i => unitNormal (angle i))) :
    upperCurvature U (Ioo 0 Real.pi \ (fullPolygonAngles angle : Set ℝ)) = 0 := by
  rw [coe_fullPolygonAngles]
  apply sigma_upper_sdiff_range_eq_zero hU.imported_isConvexBody
    (fullPolygonAngle angle)
    (fullPolygonHeight (horizontalLeft U) (horizontalRight U)
      (fun i => support U (unitNormal (angle i))))
  · exact hpoly.trans (upperPolygon_eq_iInter_halfMinus _ _ _ _)
  · exact fullPolygonAngle_mem angle hangle

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
  apply measure_eq_sum_singletons_of_sdiff_null
  exact measure_mono_null (sdiff_subset_sdiff_left hs)
    (upperCurvature_sdiff_fullPolygonAngles hU angle hangle hpoly)

end FinitePolygon

end AmbidextrousSofa
