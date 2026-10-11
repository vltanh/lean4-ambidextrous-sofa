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
  have hn : Continuous fun p : Plane => referenceNiche p.1 :=
    continuous_referenceNiche.comp continuous_fst
  exact isClosed_referenceHull.inter ((isClosed_le hn continuous_snd).inter
    (isClosed_le hn (continuous_const.sub continuous_snd)))

theorem isCompact_referenceSofa : IsCompact referenceSofa :=
  isCompact_referenceHull.of_isClosed_subset isClosed_referenceSofa
    referenceSofa_subset_referenceHull

theorem reflect_mem_referenceSofa (p : Plane) : reflect p ∈ referenceSofa ↔ p ∈ referenceSofa := by
  change reflect p ∈ referenceHull ∧ _ ↔ _
  rw [reflect_mem_referenceHull]
  simp only [referenceSofa, mem_ofPred_eq, reflect, sub_sub_cancel, and_comm]

theorem image_reflect_referenceSofa : reflect '' referenceSofa = referenceSofa :=
  (image_reflect_eq_preimage _).trans (ext reflect_mem_referenceSofa)

theorem midline_mem_referenceHull {x : ℝ} (hx : x ∈ horizontalProjection referenceHull) :
    (x, 1 / 2) ∈ referenceHull := by
  obtain ⟨p, hp, rfl⟩ := hx
  convert convex_referenceHull hp ((reflect_mem_referenceHull p).2 hp)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) using 1
  ext <;> simp [reflect] <;> ring

/-- Every abscissa of the original hull has a retained point on the midline. -/
theorem midline_mem_referenceSofa {x : ℝ} (hx : x ∈ horizontalProjection referenceHull) :
    (x, 1 / 2) ∈ referenceSofa :=
  ⟨midline_mem_referenceHull hx, (referenceNiche_lt_half x).le,
    (referenceNiche_lt_half x).le.trans (by norm_num)⟩

theorem center_mem_referenceSofa : center ∈ referenceSofa :=
  midline_mem_referenceSofa ⟨center, center_mem_referenceHull, rfl⟩

theorem referenceSofa_nonempty : referenceSofa.Nonempty := ⟨center, center_mem_referenceSofa⟩

/-- Removing the niches keeps every support value attained at a hull point over an abscissa
where the niche vanishes, since that point is retained. -/
theorem support_referenceSofa_eq_of_attained {p v : Plane} (hp : p ∈ referenceHull)
    (h0 : referenceNiche p.1 = 0) (hv : coordDot p v = support referenceHull v) :
    support referenceSofa v = support referenceHull v := by
  have hs := referenceHull_subset_unitStrip hp
  exact support_eq_of_mem isCompact_referenceSofa
    (fun q hq => coordDot_le_support isCompact_referenceHull hq.1 v)
    ⟨hp, h0 ▸ hs.1, by linarith [hs.2]⟩ hv

/-- Vertical interpolation to the midline remains outside both niches. -/
theorem vertical_to_midline_mem_referenceSofa {p : Plane} (hp : p ∈ referenceSofa)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (p.1, (1 - t) * p.2 + t * (1 / 2)) ∈ referenceSofa := by
  have h1 := mul_le_mul_of_nonneg_left hp.2.1 (sub_nonneg.2 ht.2)
  have h2 := mul_le_mul_of_nonneg_left hp.2.2 (sub_nonneg.2 ht.2)
  have h3 := mul_le_mul_of_nonneg_left (referenceNiche_lt_half p.1).le ht.1
  exact ⟨convex_verticalFiber convex_referenceHull p.1 hp.1
    (midline_mem_referenceHull ⟨p, hp.1, rfl⟩) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t),
    by dsimp only; linarith, by dsimp only; linarith⟩

theorem isConnected_referenceSofa : IsConnected referenceSofa := by
  -- Join the center to any point along the midline, then vertically.
  refine IsPathConnected.isConnected ⟨center, center_mem_referenceSofa, fun p hp => ?_⟩
  refine JoinedIn.trans (y := (p.1, 1 / 2)) ?_ (JoinedIn.symm ?_)
  · refine JoinedIn.ofLine (f := fun t : ℝ => ((1 - t) * k + t * p.1, (1 / 2 : ℝ)))
      (by fun_prop) (by simp [center]) (by simp) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact midline_mem_referenceSofa (convex_horizontalProjection convex_referenceHull
      ⟨center, center_mem_referenceHull, rfl⟩ ⟨p, hp.1, rfl⟩ (sub_nonneg.2 ht.2) ht.1
      (sub_add_cancel 1 t))
  · refine JoinedIn.ofLine (f := fun t : ℝ => (p.1, (1 - t) * p.2 + t * (1 / 2)))
      (by fun_prop) (by simp) (by simp) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact vertical_to_midline_mem_referenceSofa hp ht

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
    Real.pi / 2 * t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨mul_nonneg (by positivity) ht.1, mul_le_of_le_one_right (by positivity) ht.2⟩

theorem lowerReferencePath_eq_canonical {t : ℝ} (ht : t ∈ motionInterval) (p : Plane) :
    lowerReferencePath.placement t p = canonicalPlacement referenceHull (Real.pi / 2 * t) p := by
  rw [canonicalPlacement_eq_rigidMap, companionNormal_eq_unitNormal, ← angleSupport,
    ← angleSupport, angleSupport_referenceHull_eq_f (quarterAngle_mem ht),
    angleSupport_referenceHull_eq_g (quarterAngle_mem ht)]
  rfl

theorem referenceSofa_subset_canonicalHall {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referenceSofa ⊆ canonicalHall referenceHull (unitNormal t) (companionNormal t) := by
  intro p hp
  refine (mem_canonicalHall referenceHull _ _ p).2 ⟨coordDot_le_support isCompact_referenceHull
    hp.1 _, coordDot_le_support isCompact_referenceHull hp.1 _, ?_⟩
  -- At the two end angles the top support `1` is attained; inside, the niche bounds the wall.
  have htop : support referenceHull (0, 1) = 1 := by
    simpa [angleSupport, unitNormal, referenceF_pi_div_two] using
      angleSupport_referenceHull_eq_f (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
  have hy := (referenceHull_subset_unitStrip hp.1).1
  rcases ht.1.eq_or_lt with rfl | h0
  · right; simpa [companionNormal, coordDot, htop] using hy
  rcases ht.2.eq_or_lt with rfl | h1
  · left; simpa [unitNormal, coordDot, htop] using hy
  refine (cornerWall_le_iff (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)).1 ?_
  exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove isCompact_referenceHull le_rfl p.1)
    ⟨h0, h1⟩).trans hp.2.1

theorem lowerReferencePath_start (p : Plane) : lowerReferencePath.placement 0 p = p := by
  simp [lowerReferencePath, RigidMotionPath.placement, referenceF_zero, referenceG_zero,
    Prod.mk_zero_zero]

theorem lowerReferencePath_finish (p : Plane) :
    lowerReferencePath.placement 1 p = (p.2, 2 - 8 / 3 * A - p.1) := by
  ext <;> simp [lowerReferencePath, RigidMotionPath.placement, rigidMap, rotate,
    referenceF_pi_div_two, referenceG_pi_div_two]
  ring

theorem referenceSofa_lowerPassage :
    Passage referenceSofa lowerHall incomingArm lowerOutgoingArm lowerReferencePath := by
  refine ⟨fun t ht => ?_, ?_, ?_⟩ <;> rintro _ ⟨p, hp, rfl⟩ <;>
    have hbox := referenceHull_subset_box hp.1
  · rw [lowerReferencePath_eq_canonical ht]
    exact (canonicalPlacement_mem_lowerHall_iff _ _ _).2
      (referenceSofa_subset_canonicalHall (quarterAngle_mem ht) hp)
  · rw [lowerReferencePath_start]
    exact ⟨hbox.1.2, hbox.2.1, hbox.2.2⟩
  · rw [lowerReferencePath_finish]
    exact ⟨hbox.2.1, hbox.2.2, by linarith [hbox.1.1]⟩

theorem upperReferencePath_eq_reflect (t : ℝ) (p : Plane) :
    upperReferencePath.placement t p = reflect (lowerReferencePath.placement t (reflect p)) := by
  simpa only [upperReferencePath, reflect_reflect] using
    RigidMotionPath.reflected_placement lowerReferencePath t (reflect p)

theorem referenceSofa_upperPassage :
    Passage referenceSofa upperHall incomingArm upperOutgoingArm upperReferencePath := by
  have h := referenceSofa_lowerPassage
  refine ⟨fun t ht => ?_, ?_, ?_⟩ <;> rintro _ ⟨p, hp, rfl⟩ <;>
    have hp' := (reflect_mem_referenceSofa p).2 hp <;>
    rw [upperReferencePath_eq_reflect]
  · exact (reflect_mem_lowerHall _).1
      (by simpa only [reflect_reflect] using h.inside t ht (mem_image_of_mem _ hp'))
  · exact (reflect_mem_incomingArm _).2 (h.start (mem_image_of_mem _ hp'))
  · exact (reflect_mem_lowerOutgoingArm _).1
      (by simpa only [reflect_reflect] using h.finish (mem_image_of_mem _ hp'))

/-- The reference is an actual compact connected ambidextrous body with both full paths. -/
theorem isAmbidextrous_referenceSofa : IsAmbidextrous referenceSofa := by
  refine ⟨referenceSofa_nonempty, isCompact_referenceSofa, isConnected_referenceSofa,
    lowerReferencePath, upperReferencePath, ?_, referenceSofa_lowerPassage,
    referenceSofa_upperPassage⟩
  simp [SameInitialOrientation, upperReferencePath, lowerReferencePath, RigidMotionPath.reflected]

end AmbidextrousSofa.Reference
