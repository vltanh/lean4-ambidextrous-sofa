module

public import AmbidextrousSofa.Reference.Faces
public import AmbidextrousSofa.Geometry.AngularDomain

@[expose] public section

/-!
# The physical reference sofa and its two complete motions

The body retains exactly the hull points outside both open whole-angle niches.
The strict midline margin makes every original horizontal fiber nonempty.
Vertical segments followed by horizontal midline segments prove path
connectedness. The two explicit continuous paths use the support-tightened
corridors and include their actual incoming and outgoing arms.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

/-- The concrete body obtained by removing the two open canonical niches. -/
def referenceSofa : Set Plane :=
  {p | p ∈ referenceHull ∧ referenceNiche p.1 ≤ p.2 ∧ referenceNiche p.1 ≤ 1 - p.2}

theorem referenceSofa_subset_referenceHull : referenceSofa ⊆ referenceHull := fun _ hp => hp.1

theorem isClosed_referenceSofa : IsClosed referenceSofa := by
  have hn : Continuous (fun p : Plane => referenceNiche p.1) :=
    continuous_referenceNiche.comp continuous_fst
  exact isClosed_referenceHull.inter
    ((isClosed_le hn continuous_snd).inter
      (isClosed_le hn (continuous_const.sub continuous_snd)))

theorem isCompact_referenceSofa : IsCompact referenceSofa :=
  isCompact_referenceHull.of_isClosed_subset isClosed_referenceSofa referenceSofa_subset_referenceHull

theorem reflect_mem_referenceSofa (p : Plane) : reflect p ∈ referenceSofa ↔ p ∈ referenceSofa := by
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨(reflect_mem_referenceHull p).mp hp, ?_, ?_⟩
    · change referenceNiche p.1 ≤ 1 - (1 - p.2) at hhi
      linarith
    · exact hlo
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨(reflect_mem_referenceHull p).mpr hp, hhi, ?_⟩
    change referenceNiche p.1 ≤ 1 - (1 - p.2)
    linarith

theorem image_reflect_referenceSofa : reflect '' referenceSofa = referenceSofa := by
  rw [image_reflect_eq_preimage]
  ext p
  exact reflect_mem_referenceSofa p

theorem midline_mem_referenceHull {x : ℝ} (hx : x ∈ horizontalProjection referenceHull) :
    (x, 1 / 2) ∈ referenceHull := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hr := (reflect_mem_referenceHull p).mpr hp
  have h := convex_referenceHull hp hr (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hpoint : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • reflect p = (p.1, 1 / 2) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, reflect] <;> ring
  rwa [hpoint] at h

/-- Every abscissa of the original hull has a retained point on the midline. -/
theorem midline_mem_referenceSofa {x : ℝ} (hx : x ∈ horizontalProjection referenceHull) :
    (x, 1 / 2) ∈ referenceSofa := by
  refine ⟨midline_mem_referenceHull hx, (referenceNiche_lt_half x).le, ?_⟩
  change referenceNiche x ≤ 1 - 1 / 2
  linarith [referenceNiche_lt_half x]

theorem center_mem_referenceSofa : center ∈ referenceSofa := by
  exact midline_mem_referenceSofa ⟨center, center_mem_referenceHull, rfl⟩

theorem referenceSofa_nonempty : referenceSofa.Nonempty := ⟨center, center_mem_referenceSofa⟩

theorem fBoundary_mem_referenceSofa {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : fBoundary t ∈ referenceSofa := by
  have hp := fBoundary_mem_referenceHull ht
  have hstrip := referenceHull_subset_unitStrip hp
  refine ⟨hp, ?_, ?_⟩ <;> rw [referenceNiche_fBoundary ht]
  · exact hstrip.1
  · linarith [hstrip.2]

theorem gBoundary_mem_referenceSofa {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : gBoundary t ∈ referenceSofa := by
  have hp := gBoundary_mem_referenceHull ht
  have hstrip := referenceHull_subset_unitStrip hp
  refine ⟨hp, ?_, ?_⟩ <;> rw [referenceNiche_gBoundary ht]
  · exact hstrip.1
  · linarith [hstrip.2]

/-- Removing the niches preserves each first-quarter support maximum. -/
theorem angleSupport_referenceSofa_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : angleSupport referenceSofa t = referenceF t := by
  apply le_antisymm
  · exact (support_mono referenceSofa_subset_referenceHull referenceSofa_nonempty
      isCompact_referenceHull _).trans (angleSupport_referenceHull_eq_f ht).le
  · rw [← coordDot_fBoundary_self]
    exact coordDot_le_support isCompact_referenceSofa (fBoundary_mem_referenceSofa ht) _

/-- Every companion support maximum also survives as an actual boundary point. -/
theorem angleSupport_referenceSofa_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceSofa (t + Real.pi / 2) = referenceG t := by
  apply le_antisymm
  · exact (support_mono referenceSofa_subset_referenceHull referenceSofa_nonempty
      isCompact_referenceHull _).trans (angleSupport_referenceHull_eq_g ht).le
  · rw [← coordDot_gBoundary_self]
    exact coordDot_le_support isCompact_referenceSofa (gBoundary_mem_referenceSofa ht) _

/-- Vertical interpolation to the midline remains outside both niches. -/
theorem vertical_to_midline_mem_referenceSofa {p : Plane} (hp : p ∈ referenceSofa)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (p.1, (1 - t) * p.2 + t * (1 / 2)) ∈ referenceSofa := by
  have hproj : p.1 ∈ horizontalProjection referenceHull := ⟨p, hp.1, rfl⟩
  have hmid := midline_mem_referenceHull hproj
  have hconv := convex_referenceHull hp.1 hmid (sub_nonneg.mpr ht.2) ht.1
    (show 1 - t + t = 1 by ring)
  have hpoint : (1 - t) • p + t • (p.1, (1 / 2 : ℝ)) =
      (p.1, (1 - t) * p.2 + t * (1 / 2)) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring
  rw [hpoint] at hconv
  refine ⟨hconv, ?_, ?_⟩
  · have hleft := mul_le_mul_of_nonneg_left hp.2.1 (sub_nonneg.mpr ht.2)
    have hright := mul_le_mul_of_nonneg_left (referenceNiche_lt_half p.1).le ht.1
    nlinarith
  · have hleft := mul_le_mul_of_nonneg_left hp.2.2 (sub_nonneg.mpr ht.2)
    have hright := mul_le_mul_of_nonneg_left (referenceNiche_lt_half p.1).le ht.1
    nlinarith

theorem joinedIn_referenceSofa_midline {p : Plane} (hp : p ∈ referenceSofa) :
    JoinedIn referenceSofa p (p.1, 1 / 2) := by
  apply JoinedIn.ofLine (f := fun t : ℝ => (p.1, (1 - t) * p.2 + t * (1 / 2)))
  · fun_prop
  · simp
  · simp
  · rintro _ ⟨t, ht, rfl⟩
    exact vertical_to_midline_mem_referenceSofa hp ht

theorem joinedIn_referenceSofa_center_midline {p : Plane} (hp : p ∈ referenceSofa) :
    JoinedIn referenceSofa center (p.1, 1 / 2) := by
  have hmid := midline_mem_referenceHull (show p.1 ∈ horizontalProjection referenceHull from
    ⟨p, hp.1, rfl⟩)
  apply JoinedIn.ofLine (f := fun t : ℝ => ((1 - t) * k + t * p.1, (1 / 2 : ℝ)))
  · fun_prop
  · simp [center]
  · simp
  · rintro _ ⟨t, ht, rfl⟩
    apply midline_mem_referenceSofa
    have h := convex_referenceHull center_mem_referenceHull hmid
      (sub_nonneg.mpr ht.2) ht.1 (show 1 - t + t = 1 by ring)
    have hpoint : (1 - t) • center + t • (p.1, (1 / 2 : ℝ)) =
        ((1 - t) * k + t * p.1, (1 / 2 : ℝ)) := by
      apply Prod.ext <;> simp only [center, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] <;> ring
    rw [hpoint] at h
    exact ⟨_, h, rfl⟩

theorem isPathConnected_referenceSofa : IsPathConnected referenceSofa := by
  refine ⟨center, center_mem_referenceSofa, ?_⟩
  intro p hp
  exact (joinedIn_referenceSofa_center_midline hp).trans (joinedIn_referenceSofa_midline hp).symm

theorem isConnected_referenceSofa : IsConnected referenceSofa :=
  isPathConnected_referenceSofa.isConnected

/-- The lower path traverses the entire quarter turn with its actual support offsets. -/
def lowerReferencePath : RigidMotionPath where
  angle := fun t => -(Real.pi / 2 * t)
  shift := fun t => (1 - referenceF (Real.pi / 2 * t), 1 - referenceG (Real.pi / 2 * t))
  continuous_angle := by fun_prop
  continuous_shift := by
    have hf := continuous_referenceF
    have hg := continuous_referenceG
    fun_prop

/-- The reflected continuous path gives the independently permitted upper passage. -/
def upperReferencePath : RigidMotionPath := lowerReferencePath.reflected

theorem quarterAngle_mem {t : ℝ} (ht : t ∈ motionInterval) :
    Real.pi / 2 * t ∈ Icc (0 : ℝ) (Real.pi / 2) := by
  have hL : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨mul_nonneg hL ht.1, ?_⟩
  have h := mul_le_mul_of_nonneg_left ht.2 hL
  simpa only [mul_one] using h

theorem lowerReferencePath_eq_canonical {t : ℝ} (ht : t ∈ motionInterval) (p : Plane) :
    lowerReferencePath.placement t p = canonicalPlacement referenceHull (Real.pi / 2 * t) p := by
  rw [canonicalPlacement_eq_rigidMap]
  have hθ := quarterAngle_mem ht
  rw [show support referenceHull (unitNormal (Real.pi / 2 * t)) = referenceF (Real.pi / 2 * t) from
    angleSupport_referenceHull_eq_f hθ]
  rw [companionNormal_eq_unitNormal]
  rw [show support referenceHull (unitNormal (Real.pi / 2 * t + Real.pi / 2)) =
    referenceG (Real.pi / 2 * t) from angleSupport_referenceHull_eq_g hθ]
  rfl

theorem referenceSofa_subset_canonicalHall {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referenceSofa ⊆ canonicalHall referenceHull (unitNormal t) (companionNormal t) := by
  intro p hp
  apply (mem_canonicalHall referenceHull _ _ p).mpr
  refine ⟨coordDot_le_support isCompact_referenceHull hp.1 _,
    coordDot_le_support isCompact_referenceHull hp.1 _, ?_⟩
  by_cases ht0 : t = 0
  · right
    subst t
    have hy := (referenceHull_subset_unitStrip hp.1).1
    simpa only [companionNormal, Real.sin_zero, Real.cos_zero, neg_zero, coordDot,
      mul_zero, mul_one, zero_add, show support referenceHull (0, 1) = 1 by
        simpa only [angleSupport, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
          referenceF_pi_div_two] using angleSupport_referenceHull_eq_f
            (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) from
              ⟨by linarith [Real.pi_pos], le_rfl⟩), sub_self] using hy
  by_cases htL : t = Real.pi / 2
  · left
    subst t
    have hy := (referenceHull_subset_unitStrip hp.1).1
    rw [show support referenceHull (unitNormal (Real.pi / 2)) = 1 by
      simpa only [angleSupport, referenceF_pi_div_two] using angleSupport_referenceHull_eq_f
        (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) from
          ⟨by linarith [Real.pi_pos], le_rfl⟩)]
    simpa only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, sub_self] using hy
  · have hθ : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htL⟩
    apply (cornerWall_le_iff
      (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)).mp
    exact (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove isCompact_referenceHull le_rfl p.1) hθ).trans hp.2.1

theorem lowerReferencePath_start (p : Plane) : lowerReferencePath.placement 0 p = p := by
  simp [lowerReferencePath, RigidMotionPath.placement, referenceF_zero, referenceG_zero,
    Prod.mk_zero_zero]

theorem lowerReferencePath_finish (p : Plane) :
    lowerReferencePath.placement 1 p = (p.2, 2 - 8 / 3 * A - p.1) := by
  apply Prod.ext <;> simp [lowerReferencePath, RigidMotionPath.placement, rigidMap, rotate,
    referenceF_pi_div_two, referenceG_pi_div_two] <;> ring

theorem referenceSofa_lowerPassage :
    Passage referenceSofa lowerHall incomingArm lowerOutgoingArm lowerReferencePath := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rintro _ ⟨p, hp, rfl⟩
    rw [lowerReferencePath_eq_canonical ht]
    apply (canonicalPlacement_mem_lowerHall_iff _ _ _).mpr
    exact referenceSofa_subset_canonicalHall (quarterAngle_mem ht) hp
  · rintro _ ⟨p, hp, rfl⟩
    rw [lowerReferencePath_start]
    have hbox := referenceHull_subset_box hp.1
    exact ⟨hbox.1.2, hbox.2.1, hbox.2.2⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [lowerReferencePath_finish]
    have hbox := referenceHull_subset_box hp.1
    exact ⟨hbox.2.1, hbox.2.2, by linarith [hbox.1.1]⟩

theorem upperReferencePath_eq_reflect (t : ℝ) (p : Plane) :
    upperReferencePath.placement t p = reflect (lowerReferencePath.placement t (reflect p)) := by
  simpa only [upperReferencePath, reflect_reflect] using
    RigidMotionPath.reflected_placement lowerReferencePath t (reflect p)

theorem referenceSofa_upperPassage :
    Passage referenceSofa upperHall incomingArm upperOutgoingArm upperReferencePath := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rintro _ ⟨p, hp, rfl⟩
    rw [upperReferencePath_eq_reflect]
    have h := referenceSofa_lowerPassage.inside t ht
      (mem_image_of_mem _ ((reflect_mem_referenceSofa p).mpr hp))
    apply (reflect_mem_lowerHall _).mp
    simpa only [reflect_reflect] using h
  · rintro _ ⟨p, hp, rfl⟩
    rw [upperReferencePath_eq_reflect]
    apply (reflect_mem_incomingArm _).mpr
    exact referenceSofa_lowerPassage.start (mem_image_of_mem _ ((reflect_mem_referenceSofa p).mpr hp))
  · rintro _ ⟨p, hp, rfl⟩
    rw [upperReferencePath_eq_reflect]
    have h := referenceSofa_lowerPassage.finish
      (mem_image_of_mem _ ((reflect_mem_referenceSofa p).mpr hp))
    apply (reflect_mem_lowerOutgoingArm _).mp
    simpa only [reflect_reflect] using h

/-- The reference is an actual compact connected ambidextrous body with both full paths. -/
theorem isAmbidextrous_referenceSofa : IsAmbidextrous referenceSofa := by
  refine ⟨referenceSofa_nonempty, isCompact_referenceSofa, isConnected_referenceSofa,
    lowerReferencePath, upperReferencePath, ?_, referenceSofa_lowerPassage,
    referenceSofa_upperPassage⟩
  simp [SameInitialOrientation, upperReferencePath, lowerReferencePath, RigidMotionPath.reflected]

end AmbidextrousSofa.Reference
