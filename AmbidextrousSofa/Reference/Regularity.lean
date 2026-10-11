module

public import AmbidextrousSofa.Reference.Body

@[expose] public section

/-!
# The reference body's actual hull and regular closedness

The support maxima retained by the physical body determine its full convex
hull, including downward directions by literal reflection. Regular closedness
is proved independently of area: first move a point vertically toward the
midline, making both niche inequalities strict, and then use the density of
the interior of the convex hull inside every such open band.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

theorem support_referenceSofa_eq_hull_of_upward {v : Plane} (hv : 0 ≤ v.2) :
    support referenceSofa v = support referenceHull v := by
  obtain ⟨r, hr, t, ht, rfl | rfl⟩ := exists_upper_polar hv <;>
    rw [support_smul_direction isCompact_referenceSofa referenceSofa_nonempty _ hr,
      support_smul_direction isCompact_referenceHull referenceHull_nonempty _ hr]
  · rw [support_referenceSofa_eq_of_attained (fBoundary_mem_referenceHull ht)
      (referenceNiche_fBoundary ht)
      ((coordDot_fBoundary_self t).trans (angleSupport_referenceHull_eq_f ht).symm)]
  · rw [companionNormal_eq_unitNormal, support_referenceSofa_eq_of_attained
      (gBoundary_mem_referenceHull ht) (referenceNiche_gBoundary ht)
      ((coordDot_gBoundary_self t).trans (angleSupport_referenceHull_eq_g ht).symm)]

/-- Every directional support of the original convex body survives the cuts. -/
theorem support_referenceSofa_eq_hull (v : Plane) :
    support referenceSofa v = support referenceHull v := by
  by_cases hv : 0 ≤ v.2
  · exact support_referenceSofa_eq_hull_of_upward hv
  · rw [← image_reflect_referenceSofa, ← image_reflect_referenceHull,
      support_reflect isCompact_referenceSofa referenceSofa_nonempty,
      support_reflect isCompact_referenceHull referenceHull_nonempty,
      support_referenceSofa_eq_hull_of_upward (neg_nonneg.mpr (le_of_not_ge hv))]

/-- This is the literal convex hull of the physical reference sofa. -/
theorem actualHull_referenceSofa : actualHull referenceSofa = referenceHull :=
  eq_of_support_eq (isCompact_actualHull isCompact_referenceSofa)
    (actualHull_nonempty referenceSofa_nonempty) (convex_actualHull referenceSofa)
    isCompact_referenceHull referenceHull_nonempty convex_referenceHull fun v => by
      rw [support_actualHull isCompact_referenceSofa referenceSofa_nonempty,
        support_referenceSofa_eq_hull]

/-- Reflection of the top face and convexity fill an actual rectangle. -/
theorem topRectangle_subset_referenceHull : topInterval ×ˢ Icc (0 : ℝ) 1 ⊆ referenceHull := by
  rintro p ⟨hx, hy⟩
  have htop := topFace_mem_referenceHull hx
  have hbottom : (p.1, (0 : ℝ)) ∈ referenceHull := by
    simpa only [reflect, sub_self] using (reflect_mem_referenceHull (p.1, 1)).mpr htop
  refine convex_referenceHull.segment_subset hbottom htop ?_
  rw [← Prod.image_mk_segment_right, segment_eq_Icc zero_le_one]
  exact ⟨p.2, hy, rfl⟩

theorem center_mem_interior_referenceHull : center ∈ interior referenceHull :=
  mem_interior.mpr ⟨Ioo topLeft topRight ×ˢ Ioo (0 : ℝ) 1, fun p hp =>
    topRectangle_subset_referenceHull ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩,
    isOpen_Ioo.prod isOpen_Ioo, by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [center, topLeft, topRight, k] <;>
        linarith [A_pos]⟩

theorem closure_interior_referenceHull : closure (interior referenceHull) = referenceHull := by
  rw [convex_referenceHull.closure_interior_eq_closure_of_nonempty_interior
    ⟨center, center_mem_interior_referenceHull⟩, isClosed_referenceHull.closure_eq]

def strictReferenceBand : Set Plane :=
  {p | referenceNiche p.1 < p.2 ∧ referenceNiche p.1 < 1 - p.2}

theorem isOpen_strictReferenceBand : IsOpen strictReferenceBand := by
  have hn : Continuous (fun p : Plane => referenceNiche p.1) :=
    continuous_referenceNiche.comp continuous_fst
  exact (isOpen_lt hn continuous_snd).inter
    (isOpen_lt hn (continuous_const.sub continuous_snd))

theorem strictBand_inter_hull_subset_closure_interior :
    strictReferenceBand ∩ referenceHull ⊆ closure (interior referenceSofa) := by
  have hs : strictReferenceBand ∩ interior referenceHull ⊆ interior referenceSofa := by
    rw [← (isOpen_strictReferenceBand.inter isOpen_interior).interior_eq]
    exact interior_mono fun p ⟨hp, hK⟩ => ⟨interior_subset hK, hp.1.le, hp.2.le⟩
  intro p hp
  exact closure_mono hs (isOpen_strictReferenceBand.inter_closure
    ⟨hp.1, closure_interior_referenceHull.symm ▸ hp.2⟩)

/-- The explicit physical body is regular closed, with every boundary point
approximated by actual interior points. -/
theorem closure_interior_referenceSofa : closure (interior referenceSofa) = referenceSofa := by
  apply Subset.antisymm isClosed_referenceSofa.closure_interior_subset
  intro p hp
  let F : ℝ → Plane := fun t => (p.1, (1 - t) * p.2 + t * (1 / 2))
  -- every positive vertical move toward the midline makes both cuts strict
  have hsub : F '' Ioc (0 : ℝ) 1 ⊆ closure (interior referenceSofa) := by
    rintro q ⟨t, ht, rfl⟩
    have hm := referenceNiche_lt_half p.1
    refine strictBand_inter_hull_subset_closure_interior
      ⟨⟨?_, ?_⟩, (vertical_to_midline_mem_referenceSofa hp ⟨ht.1.le, ht.2⟩).1⟩ <;>
      simp only [F] <;> linarith [mul_le_mul_of_nonneg_left hp.2.1 (sub_nonneg.mpr ht.2),
        mul_le_mul_of_nonneg_left hp.2.2 (sub_nonneg.mpr ht.2), mul_lt_mul_of_pos_left hm ht.1]
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by simp [closure_Ioc zero_ne_one]
  exact closure_minimal hsub isClosed_closure
    (image_closure_subset_closure_image (by fun_prop) ⟨0, hzero, by simp [F]⟩)

end AmbidextrousSofa.Reference
