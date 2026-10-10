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

/-- Every vector in the first quadrant has an actual nonnegative polar
representation, including the vertical and zero vectors. -/
theorem exists_quarter_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      (a, b) = r • unitNormal t := by
  by_cases ha0 : a = 0
  · refine ⟨b, hb, Real.pi / 2, ⟨by linarith [Real.pi_pos], le_rfl⟩, ?_⟩
    simp [ha0, unitNormal]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let t := Real.arctan (b / a)
    have hc : 0 < Real.cos t := Real.cos_arctan_pos _
    have ht : t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.arctan_nonneg.mpr (div_nonneg hb ha), (Real.arctan_lt_pi_div_two _).le⟩
    have htan : Real.sin t / Real.cos t = b / a := by
      simpa only [Real.tan_eq_sin_div_cos] using Real.tan_arctan (b / a)
    have hs : Real.sin t = b / a * Real.cos t := (div_eq_iff hc.ne').mp htan
    refine ⟨a / Real.cos t, (div_pos hap hc).le, t, ht, ?_⟩
    apply Prod.ext
    · change a = a / Real.cos t * Real.cos t
      exact (div_mul_cancel₀ a hc.ne').symm
    · change b = a / Real.cos t * Real.sin t
      rw [hs]
      field_simp [ha0, hc.ne'] <;> ring

/-- The two displayed support quarters cover all upward-facing directions. -/
theorem exists_upper_polar {v : Plane} (hv : 0 ≤ v.2) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      v = r • unitNormal t ∨ v = r • companionNormal t := by
  by_cases hx : 0 ≤ v.1
  · obtain ⟨r, hr, t, ht, h⟩ := exists_quarter_polar hx hv
    exact ⟨r, hr, t, ht, Or.inl (by simpa only [Prod.mk.eta] using h)⟩
  · obtain ⟨r, hr, t, ht, h⟩ := exists_quarter_polar hv (neg_nonneg.mpr (le_of_not_ge hx))
    refine ⟨r, hr, t, ht, Or.inr ?_⟩
    have hx' := congrArg Prod.snd h
    have hy' := congrArg Prod.fst h
    apply Prod.ext
    · change v.1 = r * -Real.sin t
      change -v.1 = r * Real.sin t at hx'
      linarith
    · change v.2 = r * Real.cos t
      exact hy'

theorem support_referenceSofa_eq_hull_of_upward {v : Plane} (hv : 0 ≤ v.2) :
    support referenceSofa v = support referenceHull v := by
  obtain ⟨r, hr, t, ht, hv | hv⟩ := exists_upper_polar hv
  · rw [hv, support_smul_direction isCompact_referenceSofa referenceSofa_nonempty _ hr,
      support_smul_direction isCompact_referenceHull referenceHull_nonempty _ hr]
    rw [show support referenceSofa (unitNormal t) = referenceF t from
      angleSupport_referenceSofa_eq_f ht,
      show support referenceHull (unitNormal t) = referenceF t from
      angleSupport_referenceHull_eq_f ht]
  · rw [hv, support_smul_direction isCompact_referenceSofa referenceSofa_nonempty _ hr,
      support_smul_direction isCompact_referenceHull referenceHull_nonempty _ hr,
      companionNormal_eq_unitNormal]
    rw [show support referenceSofa (unitNormal (t + Real.pi / 2)) = referenceG t from
      angleSupport_referenceSofa_eq_g ht,
      show support referenceHull (unitNormal (t + Real.pi / 2)) = referenceG t from
      angleSupport_referenceHull_eq_g ht]

/-- Every directional support of the original convex body survives the cuts. -/
theorem support_referenceSofa_eq_hull (v : Plane) :
    support referenceSofa v = support referenceHull v := by
  by_cases hv : 0 ≤ v.2
  · exact support_referenceSofa_eq_hull_of_upward hv
  · have hu : 0 ≤ -v.2 := neg_nonneg.mpr (le_of_not_ge hv)
    have hS := support_reflect isCompact_referenceSofa referenceSofa_nonempty v
    have hK := support_reflect isCompact_referenceHull referenceHull_nonempty v
    rw [image_reflect_referenceSofa] at hS
    rw [image_reflect_referenceHull] at hK
    rw [hS, hK, support_referenceSofa_eq_hull_of_upward hu]

/-- This is the literal convex hull of the physical reference sofa. -/
theorem actualHull_referenceSofa : actualHull referenceSofa = referenceHull := by
  apply eq_of_support_eq (isCompact_actualHull isCompact_referenceSofa)
    (actualHull_nonempty referenceSofa_nonempty) (convex_actualHull referenceSofa)
    isCompact_referenceHull referenceHull_nonempty convex_referenceHull
  intro v
  rw [support_actualHull isCompact_referenceSofa referenceSofa_nonempty,
    support_referenceSofa_eq_hull]

/-- Reflection of the top face and convexity fill an actual rectangle. -/
theorem topRectangle_subset_referenceHull : topInterval ×ˢ Icc (0 : ℝ) 1 ⊆ referenceHull := by
  rintro p ⟨hx, hy⟩
  have htop := topFace_mem_referenceHull hx
  have hbottom : (p.1, (0 : ℝ)) ∈ referenceHull := by
    simpa only [reflect, sub_self] using (reflect_mem_referenceHull (p.1, 1)).mpr htop
  have h := convex_referenceHull hbottom htop (sub_nonneg.mpr hy.2) hy.1
    (show 1 - p.2 + p.2 = 1 by ring)
  have hpoint : (1 - p.2) • (p.1, (0 : ℝ)) + p.2 • (p.1, (1 : ℝ)) = p := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring
  rwa [hpoint] at h

theorem center_mem_interior_referenceHull : center ∈ interior referenceHull := by
  apply mem_interior.mpr
  refine ⟨Ioo topLeft topRight ×ˢ Ioo (0 : ℝ) 1, ?_, isOpen_Ioo.prod isOpen_Ioo, ?_⟩
  · intro p hp
    exact topRectangle_subset_referenceHull ⟨⟨hp.1.1.le, hp.1.2.le⟩,
      ⟨hp.2.1.le, hp.2.2.le⟩⟩
  · change (topLeft < k ∧ k < topRight) ∧ (0 < (1 / 2 : ℝ) ∧ 1 / 2 < (1 : ℝ))
    unfold topLeft topRight k
    constructor
    · constructor <;> linarith [A_pos]
    · norm_num

theorem closure_interior_referenceHull : closure (interior referenceHull) = referenceHull := by
  rw [convex_referenceHull.closure_interior_eq_closure_of_nonempty_interior
    ⟨center, center_mem_interior_referenceHull⟩, isClosed_referenceHull.closure_eq]

def strictReferenceBand : Set Plane :=
  {p | referenceNiche p.1 < p.2 ∧ referenceNiche p.1 < 1 - p.2}

theorem isOpen_strictReferenceBand : IsOpen strictReferenceBand := by
  have hn := continuous_referenceNiche.comp continuous_fst
  exact (isOpen_lt hn continuous_snd).inter
    (isOpen_lt hn (continuous_const.sub continuous_snd))

theorem strictBand_inter_interior_hull_subset :
    strictReferenceBand ∩ interior referenceHull ⊆ interior referenceSofa := by
  have hs : strictReferenceBand ∩ interior referenceHull ⊆ referenceSofa := by
    rintro p ⟨hp, hK⟩
    exact ⟨interior_subset hK, hp.1.le, hp.2.le⟩
  simpa only [(isOpen_strictReferenceBand.inter isOpen_interior).interior_eq] using interior_mono hs

theorem strictBand_inter_hull_subset_closure_interior :
    strictReferenceBand ∩ referenceHull ⊆ closure (interior referenceSofa) := by
  intro p hp
  have hK : p ∈ closure (interior referenceHull) := by
    rw [closure_interior_referenceHull]
    exact hp.2
  exact closure_mono strictBand_inter_interior_hull_subset
    (isOpen_strictReferenceBand.inter_closure ⟨hp.1, hK⟩)

/-- Every positive vertical move toward the midline makes both cuts strict. -/
theorem vertical_to_midline_mem_strictBand {p : Plane} (hp : p ∈ referenceSofa)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (p.1, (1 - t) * p.2 + t * (1 / 2)) ∈ strictReferenceBand := by
  have hm := referenceNiche_lt_half p.1
  have hleft := mul_le_mul_of_nonneg_left hp.2.1 (sub_nonneg.mpr ht.2)
  have hright := mul_lt_mul_of_pos_left hm ht.1
  have hleft' := mul_le_mul_of_nonneg_left hp.2.2 (sub_nonneg.mpr ht.2)
  constructor <;> change referenceNiche p.1 < _ <;> nlinarith

/-- The explicit physical body is regular closed, with every boundary point
approximated by actual interior points. -/
theorem closure_interior_referenceSofa : closure (interior referenceSofa) = referenceSofa := by
  apply Subset.antisymm isClosed_referenceSofa.closure_interior_subset
  intro p hp
  let F : ℝ → Plane := fun t => (p.1, (1 - t) * p.2 + t * (1 / 2))
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hsub : F '' Ioc (0 : ℝ) 1 ⊆ closure (interior referenceSofa) := by
    rintro q ⟨t, ht, rfl⟩
    apply strictBand_inter_hull_subset_closure_interior
    exact ⟨vertical_to_midline_mem_strictBand hp ht,
      (vertical_to_midline_mem_referenceSofa hp ⟨ht.1.le, ht.2⟩).1⟩
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hpimage : p ∈ F '' closure (Ioc (0 : ℝ) 1) :=
    ⟨0, hzero, by simp [F]⟩
  have hpclosure := image_closure_subset_closure_image hF hpimage
  exact (closure_minimal hsub isClosed_closure) hpclosure

end AmbidextrousSofa.Reference
