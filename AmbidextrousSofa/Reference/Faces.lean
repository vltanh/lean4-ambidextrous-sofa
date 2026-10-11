module

public import AmbidextrousSofa.Reference.Niche
public import AmbidextrousSofa.Reference.Momenta
public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# Projection, top face, and confinement of the reference niche

The realized endpoint supports give the exact horizontal projection. The two
upper boundary arcs give the endpoints of the middle top face. A tangent
unit-disk comparison follows from the proved curvature bound and shows that the
actual niche vanishes beyond the right end of that face; by the mirror symmetry
of the niche it also vanishes beyond the left end.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

def topLeft : ℝ := 1 - 2 * A

def topRight : ℝ := 1 - 2 / 3 * A

def topInterval : Set ℝ := Icc topLeft topRight

theorem topLeft_lt_topRight : topLeft < topRight := by
  unfold topLeft topRight; linarith [A_pos]

theorem horizontalLeft_referenceCap : horizontalLeft referenceCap = 1 - 8 / 3 * A := by
  have h := angleSupport_referenceHull_eq_g (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
  simp only [add_halves, angleSupport, unitNormal, Real.cos_pi, Real.sin_pi,
    referenceG_pi_div_two, support_horizontal_left isCompact_referenceHull
      referenceHull_nonempty] at h
  unfold horizontalLeft at h ⊢
  rw [horizontalProjection_referenceCap]
  linarith

theorem horizontalRight_referenceCap : horizontalRight referenceCap = 1 := by
  have h := angleSupport_referenceHull_eq_f (t := 0) ⟨le_rfl, by positivity⟩
  simp only [angleSupport, unitNormal, Real.cos_zero, Real.sin_zero, support_horizontal_right,
    referenceF_zero] at h
  rwa [horizontalRight, horizontalProjection_referenceCap]

theorem capWidth_referenceCap : capWidth referenceCap = 8 / 3 * A := by
  rw [capWidth, horizontalLeft_referenceCap, horizontalRight_referenceCap]; ring

theorem middleHalfInterval_referenceCap :
    middleHalfInterval (horizontalLeft referenceCap) (horizontalRight referenceCap) =
      topInterval := by
  rw [horizontalLeft_referenceCap, horizontalRight_referenceCap]
  unfold middleHalfInterval topInterval topLeft topRight
  congr 1 <;> ring

/-- The whole top segment consists of actual points of the reference hull. -/
theorem topFace_mem_referenceHull {x : ℝ} (hx : x ∈ topInterval) : (x, 1) ∈ referenceHull := by
  have hr : (topRight, (1 : ℝ)) ∈ referenceHull := by
    simpa only [fBoundary_pi_div_two, topRight] using
      fBoundary_mem_referenceHull (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
  -- the left end is the mirror image of the right end
  have hl : (topLeft, (1 : ℝ)) ∈ referenceHull := by
    convert (mirror_mem_referenceHull _).2 hr using 2; unfold topLeft topRight k; ring
  apply convex_referenceHull.segment_subset hl hr
  rw [← Prod.image_mk_segment_left, segment_eq_Icc topLeft_lt_topRight.le]
  exact mem_image_of_mem _ hx

theorem capRoof_referenceCap_eq_one {x : ℝ} (hx : x ∈ topInterval) :
    capRoof referenceCap x = 1 :=
  le_antisymm (capRoof_le_one isDownwardCap_referenceCap.isCompact
    isDownwardCap_referenceCap.inStrip x) (le_capRoof isDownwardCap_referenceCap.isCompact
      (referenceHull_subset_referenceCap (topFace_mem_referenceHull hx)))

theorem referenceF_le_topRight_disk {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t ≤ 1 + topRight * Real.cos t := by
  have hf := continuous_referenceF
  have hfD := continuous_referenceFD
  have h := supportProjection_le_self (h := fun x => 1 + topRight * Real.cos x - referenceF x)
    (hD := fun x => -topRight * Real.sin x - referenceFD x)
    (hDD := fun x => -topRight * Real.cos x - referenceFSecond x) (by fun_prop) (by fun_prop)
    (fun x => (((hasDerivAt_const x 1).add ((Real.hasDerivAt_cos x).const_mul topRight)).sub
      (hasDerivAt_referenceF x)).hasDerivWithinAt.congr_deriv (by ring))
    (fun x => ((Real.hasDerivAt_sin x).const_mul (-topRight)).hasDerivWithinAt.sub
      (hasDerivWithinAt_referenceFD_right x))
    (fun x _ => by linarith [(referenceF_right_curvature x).2])
    (by linarith [Real.pi_pos]) ⟨by positivity, le_rfl⟩ ht
  simpa [supportProjection, referenceF_pi_div_two, referenceFD_pi_div_two, topRight] using h

theorem referenceNiche_eq_zero_of_topRight_le {x : ℝ} (hx : topRight ≤ x) :
    referenceNiche x = 0 := by
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) le_rfl fun t ht => ?_)
    (referenceNiche_nonneg x)
  refine (min_le_left _ _).trans ?_
  rw [firstWall_referenceHull ⟨ht.1.le, ht.2.le⟩]
  refine div_nonpos_of_nonpos_of_nonneg ?_
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos]))
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
  linarith [referenceF_le_topRight_disk ⟨ht.1.le, ht.2.le⟩, mul_le_mul_of_nonneg_right hx hc]

theorem referenceNiche_eq_zero_of_le_topLeft {x : ℝ} (hx : x ≤ topLeft) : referenceNiche x = 0 := by
  rw [← sub_sub_cancel (2 * k) x, referenceNiche_mirror]
  exact referenceNiche_eq_zero_of_topRight_le (by unfold topLeft topRight k at *; linarith)

theorem referenceNiche_eq_zero_outside {x : ℝ} (hx : x ∉ topInterval) : referenceNiche x = 0 := by
  rcases le_total x topLeft with hl | hl
  · exact referenceNiche_eq_zero_of_le_topLeft hl
  · exact referenceNiche_eq_zero_of_topRight_le (not_lt.1 fun hr => hx ⟨hl, hr.le⟩)

theorem referenceNiche_fBoundary {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceNiche (fBoundary t).1 = 0 := by
  -- First-arc points lie on the right flank, including the right face endpoint.
  have h := supportProjection_le_of_ge continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x _ => (referenceF_right_curvature x).1)
    ht.2 ht.1 (show Real.pi / 2 - 0 ≤ Real.pi by linarith [Real.pi_pos])
  rw [← coordDot_fBoundary, ← coordDot_fBoundary, fBoundary_pi_div_two] at h
  refine referenceNiche_eq_zero_of_topRight_le ?_
  simpa [coordDot, unitNormal, topRight] using h

theorem referenceNiche_gBoundary {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceNiche (gBoundary t).1 = 0 := by
  rw [gBoundary_eq_mirror, referenceNiche_mirror]
  exact referenceNiche_fBoundary ⟨by linarith [ht.2], by linarith [ht.1]⟩

end AmbidextrousSofa.Reference
