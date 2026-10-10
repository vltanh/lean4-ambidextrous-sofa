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

This source is an uncompiled draft.
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

theorem reflect_center : reflect center = center := by
  norm_num [reflect, center]

theorem coordDot_center_unitNormal (t : ℝ) :
    coordDot center (unitNormal t) = k * Real.cos t + 1 / 2 * Real.sin t := rfl

theorem coordDot_center_companion (t : ℝ) :
    coordDot center (unitNormal (t + Real.pi / 2)) =
      -k * Real.sin t + 1 / 2 * Real.cos t := by
  simp only [coordDot, center, unitNormal, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two]
  ring

theorem center_mem_upperHalfPlanes {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : center ∈ upperHalfPlanes t := by
  constructor
  · rw [coordDot_center_unitNormal]
    exact referenceF_ge_center ht
  · rw [coordDot_center_companion]
    exact referenceG_ge_center ht

/-- Nonemptiness is supplied by an explicit point, not by a realization assumption. -/
theorem center_mem_referenceHull : center ∈ referenceHull := by
  apply (mem_referenceHull_iff center).mpr
  intro t ht
  have hcenter := center_mem_upperHalfPlanes ht
  exact ⟨hcenter, by simpa only [reflect_center] using hcenter⟩

theorem referenceHull_nonempty : referenceHull.Nonempty :=
  ⟨center, center_mem_referenceHull⟩

theorem isClosed_upperHalfPlanes (t : ℝ) : IsClosed (upperHalfPlanes t) :=
  (isClosed_le (continuous_coordDot_right (unitNormal t)) continuous_const).inter
    (isClosed_le (continuous_coordDot_right (unitNormal (t + Real.pi / 2))) continuous_const)

theorem convex_upperHalfPlanes (t : ℝ) : Convex ℝ (upperHalfPlanes t) :=
  (convex_coordDot_halfspace (unitNormal t) (referenceF t)).inter
    (convex_coordDot_halfspace (unitNormal (t + Real.pi / 2)) (referenceG t))

theorem isClosed_referenceHull : IsClosed referenceHull := by
  unfold referenceHull
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    (isClosed_upperHalfPlanes t).inter
      ((isClosed_upperHalfPlanes t).preimage continuous_reflect)

theorem convex_referenceHull : Convex ℝ referenceHull := by
  unfold referenceHull
  exact convex_iInter fun t => convex_iInter fun _ =>
    (convex_upperHalfPlanes t).inter
      (convex_preimage_reflect (convex_upperHalfPlanes t))

/-- Endpoint normals give an actual closed rectangle containing the intersection. -/
theorem referenceHull_subset_box : referenceHull ⊆ referenceBox := by
  intro p hp
  have hzero := (mem_referenceHull_iff p).mp hp 0
    ⟨le_rfl, le_of_lt (by linarith [Real.pi_pos])⟩
  have htop := (mem_referenceHull_iff p).mp hp (Real.pi / 2)
    ⟨le_of_lt (by linarith [Real.pi_pos]), le_rfl⟩
  have hxright : p.1 ≤ 1 := by
    simpa only [coordDot, unitNormal, Real.cos_zero, Real.sin_zero,
      mul_one, mul_zero, add_zero, referenceF_zero] using hzero.1.1
  have hytop : p.2 ≤ 1 := by
    simpa only [zero_add, coordDot, unitNormal, Real.cos_pi_div_two,
      Real.sin_pi_div_two, mul_zero, mul_one, referenceG_zero] using hzero.1.2
  have hybottom : 0 ≤ p.2 := by
    have hreflect : 1 - p.2 ≤ 1 := by
      simpa only [zero_add, coordDot, unitNormal, reflect, Real.cos_pi_div_two,
        Real.sin_pi_div_two, mul_zero, mul_one, referenceG_zero] using hzero.2.2
    linarith
  have hxleft : 1 - 8 / 3 * A ≤ p.1 := by
    have hangle : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
    have hleft : -p.1 ≤ 8 / 3 * A - 1 := by
      simpa only [hangle, coordDot, unitNormal, Real.cos_pi, Real.sin_pi,
        mul_neg_one, mul_zero, add_zero, referenceG_pi_div_two] using htop.1.2
    linarith
  exact ⟨⟨hxleft, hxright⟩, ⟨hybottom, hytop⟩⟩

theorem referenceHull_subset_unitStrip : referenceHull ⊆ unitStrip := by
  intro p hp
  exact (referenceHull_subset_box hp).2

theorem isCompact_referenceBox : IsCompact referenceBox := isCompact_Icc.prod isCompact_Icc

/-- Compactness follows from closedness and the proved coordinate bounds. -/
theorem isCompact_referenceHull : IsCompact referenceHull :=
  isCompact_referenceBox.of_isClosed_subset isClosed_referenceHull referenceHull_subset_box

theorem isConnected_referenceHull : IsConnected referenceHull :=
  convex_referenceHull.isConnected referenceHull_nonempty

theorem measurableSet_referenceHull : MeasurableSet referenceHull :=
  isClosed_referenceHull.measurableSet

/-- Reflection exchanges the two retained members of each half-plane family. -/
theorem reflect_mem_referenceHull (p : Plane) :
    reflect p ∈ referenceHull ↔ p ∈ referenceHull := by
  rw [mem_referenceHull_iff, mem_referenceHull_iff]
  constructor
  · intro h t ht
    have hp := h t ht
    exact ⟨by simpa only [reflect_reflect] using hp.2, hp.1⟩
  · intro h t ht
    have hp := h t ht
    exact ⟨hp.2, by simpa only [reflect_reflect] using hp.1⟩

theorem preimage_reflect_referenceHull : reflect ⁻¹' referenceHull = referenceHull := by
  ext p
  exact reflect_mem_referenceHull p

/-- Literal set symmetry, including every boundary point. -/
theorem image_reflect_referenceHull : reflect '' referenceHull = referenceHull := by
  rw [image_reflect_eq_preimage, preimage_reflect_referenceHull]

theorem actualHull_referenceHull : actualHull referenceHull = referenceHull := by
  apply Set.Subset.antisymm
  · exact convexHull_min (Set.Subset.refl _) convex_referenceHull
  · exact subset_actualHull referenceHull

/-- The actual upper cap meets the broad intrinsic cap definition. -/
theorem isDownwardCap_referenceCap : IsDownwardCap referenceCap :=
  isDownwardCap_upperCap referenceHull_nonempty isCompact_referenceHull
    convex_referenceHull referenceHull_subset_unitStrip

theorem referenceHull_subset_referenceCap : referenceHull ⊆ referenceCap :=
  subset_upperCap (fun p hp => (referenceHull_subset_unitStrip hp).1)

theorem horizontalProjection_referenceCap :
    horizontalProjection referenceCap = horizontalProjection referenceHull :=
  horizontalProjection_upperCap (fun p hp => (referenceHull_subset_unitStrip hp).1)

theorem upperHullCap_referenceHull : upperHullCap referenceHull = referenceCap := by
  unfold upperHullCap referenceCap
  rw [actualHull_referenceHull]

theorem reflectedHullCap_referenceHull : reflectedHullCap referenceHull = referenceCap := by
  unfold reflectedHullCap referenceCap
  rw [actualHull_referenceHull, image_reflect_referenceHull]

/-- Symmetry and convexity recover this hull from its actual downward cap. -/
theorem referenceHull_eq_inter_caps : referenceHull = referenceCap ∩ reflect '' referenceCap := by
  have h := eq_upperCap_inter_reflectedCap convex_referenceHull referenceHull_subset_unitStrip
  simpa only [image_reflect_referenceHull, referenceCap] using h

/-- Prescribed support is an upper bound; the converse is not assumed. -/
theorem angleSupport_referenceHull_le_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull t ≤ referenceF t := by
  apply support_le_of_forall referenceHull_nonempty
  intro p hp
  exact ((mem_referenceHull_iff p).mp hp t ht).1.1

/-- The companion upper bound retains the complete second quarter. -/
theorem angleSupport_referenceHull_le_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull (t + Real.pi / 2) ≤ referenceG t := by
  apply support_le_of_forall referenceHull_nonempty
  intro p hp
  exact ((mem_referenceHull_iff p).mp hp t ht).1.2

/-- The actual hull support has the precise reflected vertical correction. -/
theorem angleSupport_referenceHull_neg (t : ℝ) :
    angleSupport referenceHull (-t) = angleSupport referenceHull t - Real.sin t := by
  have h := angleSupport_reflect isCompact_referenceHull referenceHull_nonempty t
  rw [image_reflect_referenceHull] at h
  linarith

/-- Downward filling preserves actual upward support of the constructed hull. -/
theorem angleSupport_referenceCap {t : ℝ} (ht : 0 ≤ Real.sin t) :
    angleSupport referenceCap t = angleSupport referenceHull t :=
  angleSupport_upperCap isCompact_referenceHull referenceHull_nonempty
    (fun p hp => (referenceHull_subset_unitStrip hp).1) ht

end AmbidextrousSofa.Reference
