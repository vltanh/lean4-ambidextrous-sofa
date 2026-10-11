module

public import AmbidextrousSofa.Reference.Support
public import AmbidextrousSofa.Geometry.Reflection

@[expose] public section

/-!
# The explicit reference half-plane intersection

The candidate hull is the intersection of all four reflected upper-quarter
families prescribed by `referenceF` and `referenceG`. Its nonemptiness,
compactness, convexity, and literal reflection symmetry are proved here.

The point `(k, 1 / 2)` is an actual witness. Endpoint normals supply the closed
bounding rectangle. These conclusions do not assume that every prescribed
support value is attained. The reverse support inequalities remain a separate
support-realization obligation.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

/-- The explicit center of the displayed reference coordinates. -/
def center : Plane := (k, 1 / 2)

/-- The two upper-quarter halfplanes at one parameter value. -/
def upperHalfPlanes (t : ℝ) : Set Plane :=
  {p | coordDot p (unitNormal t) ≤ referenceF t ∧
    coordDot p (unitNormal (t + Real.pi / 2)) ≤ referenceG t}

/-- The complete four-family intersection, with all endpoint normals included. -/
def referenceHull : Set Plane :=
  ⋂ t ∈ Icc (0 : ℝ) (Real.pi / 2),
    upperHalfPlanes t ∩ reflect ⁻¹' upperHalfPlanes t

/-- The exact endpoint rectangle forced by the prescribed support values. -/
def referenceBox : Set Plane :=
  Icc (1 - 8 / 3 * A) 1 ×ˢ Icc (0 : ℝ) 1

/-- The intrinsic upper downward cap of the explicit intersection. -/
def referenceCap : Set Plane := upperCap referenceHull

theorem mem_referenceHull_iff (p : Plane) :
    p ∈ referenceHull ↔ ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      p ∈ upperHalfPlanes t ∧ reflect p ∈ upperHalfPlanes t := by
  simp only [referenceHull, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]

/-- Nonemptiness is supplied by an explicit point, not by a realization assumption. -/
theorem center_mem_referenceHull : center ∈ referenceHull := by
  have hc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : center ∈ upperHalfPlanes t := by
    refine ⟨referenceF_ge_center ht, ?_⟩
    simpa only [coordDot, center, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      mul_neg, neg_mul] using referenceG_ge_center ht
  have hr : reflect center = center := by norm_num [reflect, center]
  exact (mem_referenceHull_iff center).2 fun t ht => ⟨hc ht, by rw [hr]; exact hc ht⟩

theorem referenceHull_nonempty : referenceHull.Nonempty :=
  ⟨center, center_mem_referenceHull⟩

theorem isClosed_referenceHull : IsClosed referenceHull := by
  have h (t : ℝ) : IsClosed (upperHalfPlanes t) :=
    (isClosed_le (continuous_coordDot_right _) continuous_const).inter
      (isClosed_le (continuous_coordDot_right _) continuous_const)
  exact isClosed_biInter fun t _ => (h t).inter ((h t).preimage continuous_reflect)

theorem convex_referenceHull : Convex ℝ referenceHull := by
  have h (t : ℝ) : Convex ℝ (upperHalfPlanes t) :=
    (convex_coordDot_halfspace _ _).inter (convex_coordDot_halfspace _ _)
  exact convex_iInter₂ fun t _ => (h t).inter (convex_preimage_reflect (h t))

/-- Endpoint normals give an actual closed rectangle containing the intersection. -/
theorem referenceHull_subset_box : referenceHull ⊆ referenceBox := fun p hp => by
  have h0 := (mem_referenceHull_iff p).1 hp 0 ⟨le_rfl, by positivity⟩
  have h1 := ((mem_referenceHull_iff p).1 hp (Real.pi / 2) ⟨by positivity, le_rfl⟩).1.2
  simp only [upperHalfPlanes, mem_ofPred_eq, coordDot, unitNormal, reflect, zero_add, add_halves,
    Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi,
    Real.sin_pi, mul_one, mul_zero, add_zero, mul_neg, referenceF_zero, referenceG_zero,
    referenceG_pi_div_two] at h0 h1
  exact ⟨⟨by linarith, h0.1.1⟩, by linarith, h0.1.2⟩

theorem referenceHull_subset_unitStrip : referenceHull ⊆ unitStrip :=
  fun _ hp => (referenceHull_subset_box hp).2

/-- Compactness follows from closedness and the proved coordinate bounds. -/
theorem isCompact_referenceHull : IsCompact referenceHull :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_referenceHull
    referenceHull_subset_box

/-- Reflection exchanges the two retained members of each half-plane family. -/
theorem reflect_mem_referenceHull (p : Plane) :
    reflect p ∈ referenceHull ↔ p ∈ referenceHull := by
  simp only [mem_referenceHull_iff, reflect_reflect, and_comm]

/-- Literal set symmetry, including every boundary point. -/
theorem image_reflect_referenceHull : reflect '' referenceHull = referenceHull :=
  (image_reflect_eq_preimage _).trans (ext reflect_mem_referenceHull)

/-- The actual upper cap meets the broad intrinsic cap definition. -/
theorem isDownwardCap_referenceCap : IsDownwardCap referenceCap :=
  isDownwardCap_upperCap referenceHull_nonempty isCompact_referenceHull
    convex_referenceHull referenceHull_subset_unitStrip

theorem referenceHull_subset_referenceCap : referenceHull ⊆ referenceCap :=
  subset_upperCap (fun _ hp => (referenceHull_subset_unitStrip hp).1)

theorem horizontalProjection_referenceCap :
    horizontalProjection referenceCap = horizontalProjection referenceHull :=
  horizontalProjection_upperCap (fun _ hp => (referenceHull_subset_unitStrip hp).1)

/-- Symmetry and convexity recover this hull from its actual downward cap. -/
theorem referenceHull_eq_inter_caps : referenceHull = referenceCap ∩ reflect '' referenceCap := by
  simpa only [image_reflect_referenceHull, referenceCap] using
    eq_upperCap_inter_reflectedCap convex_referenceHull referenceHull_subset_unitStrip

/-- Downward filling preserves actual upward support of the constructed hull. -/
theorem angleSupport_referenceCap {t : ℝ} (ht : 0 ≤ Real.sin t) :
    angleSupport referenceCap t = angleSupport referenceHull t :=
  angleSupport_upperCap isCompact_referenceHull referenceHull_nonempty
    (fun _ hp => (referenceHull_subset_unitStrip hp).1) ht

end AmbidextrousSofa.Reference
