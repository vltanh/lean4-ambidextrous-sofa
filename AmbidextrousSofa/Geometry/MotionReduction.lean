module

public import AmbidextrousSofa.Measure.RigidInvariance
public import AmbidextrousSofa.Measure.StripBounds
public import AmbidextrousSofa.Measure.CapAssembly

@[expose] public section

/-!
# Reduction of the original independent passages to the two actual caps

For area greater than `√2`, the wrong-handed frame is excluded by its exact
horizontal sections. The outgoing strip then forces the terminal frame past
`π/4`. A continuous angle lift either visits `π/2`, or has an actual terminal
angle strictly between `π/4` and `π/2`. This argument uses no monotonicity and
does not replace a proper terminal wall by an artificial quarter-turn wall.

The two passages are treated independently. Reflection converts the upper
passage to a lower one, while preserving the area of the actual body. Combined
with a common incoming rigid normalization, this supplies the actual two-cap
area bound from `IsAmbidextrous` itself.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Pull back an actual placement to the translated frame hallway, before any
support tightening. -/
theorem Passage.subset_frameHall_at {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    {t : ℝ} (ht : t ∈ motionInterval) :
    S ⊆ frameHall (unitNormal (-path.angle t)) (companionNormal (-path.angle t))
      (-(path.shift t).1) (-(path.shift t).2) := by
  intro p hp
  apply (rigidMap_mem_lowerHall_iff (-path.angle t) (path.shift t) p).mp
  simpa only [neg_neg, RigidMotionPath.placement] using
    h.inside t ht (mem_image_of_mem _ hp)

/-- The outgoing endpoint really supplies a whole-body unit strip. -/
theorem Passage.terminal_frameStrip {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path) :
    ∀ p ∈ S, -(path.shift 1).1 ≤ coordDot p (unitNormal (-path.angle 1)) ∧
      coordDot p (unitNormal (-path.angle 1)) ≤ -(path.shift 1).1 + 1 := by
  intro p hp
  have hfinish := h.finish (mem_image_of_mem _ hp)
  have h0 := hfinish.1
  have h1 := hfinish.2.1
  change 0 ≤ Real.cos (path.angle 1) * p.1 - Real.sin (path.angle 1) * p.2 +
    (path.shift 1).1 at h0
  change Real.cos (path.angle 1) * p.1 - Real.sin (path.angle 1) * p.2 +
    (path.shift 1).1 ≤ 1 at h1
  simp only [coordDot, unitNormal, Real.cos_neg, Real.sin_neg]
  constructor <;> nlinarith

theorem Passage.volumeReal_le_sqrt_two_of_wrongWay
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hstrip : S ⊆ unitStrip) {t : ℝ} (ht : t ∈ motionInterval)
    (hangle : -path.angle t = -(Real.pi / 4)) :
    volume.real S ≤ Real.sqrt 2 := by
  have hframe := h.subset_frameHall_at ht
  rw [hangle] at hframe
  exact volumeReal_le_sqrt_two_of_wrongWay_frameHall hstrip hframe

theorem Passage.volumeReal_le_sqrt_two_of_small_terminalAngle
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hstrip : S ⊆ unitStrip)
    (hangle : -path.angle 1 ∈ Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    volume.real S ≤ Real.sqrt 2 :=
  volumeReal_le_sqrt_two_of_unitStrip_and_smallAngleStrip hstrip hangle h.terminal_frameStrip

/-- A large sofa cannot even pass below the forbidden angle: continuity would
force it to visit that angle first. -/
theorem Passage.frameAngle_gt_neg_pi_div_four
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hstrip : S ⊆ unitStrip) (hstart : path.angle 0 = 0)
    (harea : Real.sqrt 2 < volume.real S) {t : ℝ} (ht : t ∈ motionInterval) :
    -(Real.pi / 4) < -path.angle t := by
  by_contra hnot
  have hle : -path.angle t ≤ -(Real.pi / 4) := le_of_not_gt hnot
  have hsub : Icc (0 : ℝ) t ⊆ motionInterval := by
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hcont := path.continuous_angle.neg.mono hsub
  have hbetween : -(Real.pi / 4) ∈ Icc (-path.angle t) (-path.angle 0) := by
    refine ⟨hle, ?_⟩
    rw [hstart, neg_zero]
    linarith [Real.pi_pos]
  obtain ⟨s, hs, hsangle⟩ := intermediate_value_Icc' ht.1 hcont hbetween
  exact (harea.not_ge (h.volumeReal_le_sqrt_two_of_wrongWay hstrip (hsub hs) hsangle))

/-- The terminal strip rules out all remaining endpoint angles up to `π/4`.
The argument is independent of any backtracking in the path. -/
theorem Passage.terminal_frameAngle_gt_pi_div_four
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hstrip : S ⊆ unitStrip) (hstart : path.angle 0 = 0)
    (harea : Real.sqrt 2 < volume.real S) :
    Real.pi / 4 < -path.angle 1 := by
  have hlow := h.frameAngle_gt_neg_pi_div_four hstrip hstart harea
    (show (1 : ℝ) ∈ motionInterval from ⟨by norm_num, le_rfl⟩)
  by_contra hnot
  have hhigh : -path.angle 1 ≤ Real.pi / 4 := le_of_not_gt hnot
  exact harea.not_ge
    (h.volumeReal_le_sqrt_two_of_small_terminalAngle hstrip ⟨hlow.le, hhigh⟩)

/-- Every large normalized lower passage supplies either a visited quarter
turn or its genuine proper terminal angle, together with all intervening
frames and the correct endpoint support wall. -/
theorem Passage.exists_effectiveAngle
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ unitStrip)
    (hstart : path.angle 0 = 0) (harea : Real.sqrt 2 < volume.real S) :
    ∃ α : ℝ, Real.pi / 4 < α ∧ α ≤ Real.pi / 2 ∧
      AngularConstraints S (actualHull S) α ∧
      ((α = Real.pi / 2 ∧ ∃ t ∈ motionInterval, -path.angle t = Real.pi / 2) ∨
        (α = -path.angle 1 ∧ α < Real.pi / 2)) := by
  by_cases hfull : ∃ t ∈ motionInterval, -path.angle t = Real.pi / 2
  · obtain ⟨t, ht, htangle⟩ := hfull
    refine ⟨Real.pi / 2, by linarith [Real.pi_pos], le_rfl,
      h.angularConstraints_of_reaches_pi_div_two hS hne hstrip hstart ht htangle,
      Or.inl ⟨rfl, t, ht, htangle⟩⟩
  · have hend := h.terminal_frameAngle_gt_pi_div_four hstrip hstart harea
    have hendL : -path.angle 1 < Real.pi / 2 := by
      by_contra hnot
      apply hfull
      exact RigidMotionPath.exists_frameAngle_of_terminal hstart rfl
        ⟨by linarith [Real.pi_pos], le_of_not_gt hnot⟩
    refine ⟨-path.angle 1, hend, hendL.le, ?_, Or.inr ⟨rfl, hendL⟩⟩
    exact h.angularConstraints_of_terminal hS hne hstart rfl
      (by linarith [Real.pi_pos]) hendL.le

/-- Both actual cap constraints are obtained from independent original paths.
The two selected endpoint angles may differ, and each selected proper angle
retains the outgoing wall of its own passage. -/
theorem hullCap_constraints_of_large_passages {S : Set Plane}
    (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ unitStrip)
    {lower upper : RigidMotionPath}
    (hlower : Passage S lowerHall incomingArm lowerOutgoingArm lower)
    (hupper : Passage S upperHall incomingArm upperOutgoingArm upper)
    (hlower0 : lower.angle 0 = 0) (hupper0 : upper.angle 0 = 0)
    (harea : Real.sqrt 2 < volume.real S) :
    ∃ α γ : ℝ, Real.pi / 4 < α ∧ Real.pi / 4 < γ ∧
      AngularConstraints S (upperHullCap S) α ∧
      AngularConstraints (reflect '' S) (reflectedHullCap S) γ := by
  obtain ⟨α, hα, _, hconstraintsU, _⟩ :=
    hlower.exists_effectiveAngle hS hne hstrip hlower0 harea
  have hSh := isCompact_image_reflect hS
  have hSn := hne.image reflect
  have hSstrip := image_reflect_subset_unitStrip hstrip
  have hupperRef0 : upper.reflected.angle 0 = 0 := by
    simp only [RigidMotionPath.reflected, hupper0, neg_zero]
  have hareaRef : Real.sqrt 2 < volume.real (reflect '' S) := by
    simpa only [volumeReal_image_reflect] using harea
  obtain ⟨γ, hγ, _, hconstraintsV, _⟩ :=
    hupper.reflected.exists_effectiveAngle hSh hSn hSstrip hupperRef0 hareaRef
  have hU := hconstraintsU.upperCap (isCompact_actualHull hS) (actualHull_nonempty hne)
    (fun p hp => (actualHull_subset_unitStrip hstrip hp).1)
  have hV := hconstraintsV.upperCap (isCompact_actualHull hSh) (actualHull_nonempty hSn)
    (fun p hp => (actualHull_subset_unitStrip hSstrip hp).1)
  refine ⟨α, γ, hα, hγ, hU, ?_⟩
  simpa only [reflectedHullCap, actualHull_reflect] using hV

/-- The large-area original domain admits an area-preserving incoming
normalization and the complete two-cap angular data. These are conclusions,
not hidden premises in the definition of an ambidextrous sofa. -/
theorem IsAmbidextrous.exists_normalized_angularConstraints
    {S : Set Plane} (hS : IsAmbidextrous S) (harea : Real.sqrt 2 < volume.real S) :
    ∃ (θ : ℝ) (v : Plane) (α γ : ℝ),
      let T := rigidMap θ v '' S
      IsAmbidextrous T ∧ T ⊆ unitStrip ∧ volume.real T = volume.real S ∧
        Real.pi / 4 < α ∧ Real.pi / 4 < γ ∧
        AngularConstraints T (upperHullCap T) α ∧
        AngularConstraints (reflect '' T) (reflectedHullCap T) γ := by
  obtain ⟨θ, v, lower, upper, hT, hstrip, hareaEq, hl0, hu0, hl, hu⟩ :=
    hS.exists_normalized
  have hTarea : Real.sqrt 2 < volume.real (rigidMap θ v '' S) := by
    rw [hareaEq]
    exact harea
  obtain ⟨α, γ, hα, hγ, hU, hV⟩ := hullCap_constraints_of_large_passages
    hT.isCompact hT.nonempty hstrip hl hu hl0 hu0 hTarea
  exact ⟨θ, v, α, γ, hT, hstrip, hareaEq, hα, hγ, hU, hV⟩

/-- End-to-end original-domain score reduction. Small sofas are already
bounded by `√2`; every larger sofa is bounded by the sum of the two actual cap
scores after an area-preserving rigid normalization. -/
theorem IsAmbidextrous.original_domain_score_reduction
    {S : Set Plane} (hS : IsAmbidextrous S) :
    volume.real S ≤ Real.sqrt 2 ∨
      ∃ (θ : ℝ) (v : Plane) (α γ : ℝ),
        let T := rigidMap θ v '' S
        IsAmbidextrous T ∧ T ⊆ unitStrip ∧ volume.real T = volume.real S ∧
          Real.pi / 4 < α ∧ Real.pi / 4 < γ ∧
          AngularConstraints T (upperHullCap T) α ∧
          AngularConstraints (reflect '' T) (reflectedHullCap T) γ ∧
          volume.real S ≤ capScore (upperHullCap T) α + capScore (reflectedHullCap T) γ := by
  by_cases hsmall : volume.real S ≤ Real.sqrt 2
  · exact Or.inl hsmall
  · obtain ⟨θ, v, α, γ, hT, hstrip, hareaEq, hα, hγ, hU, hV⟩ :=
      hS.exists_normalized_angularConstraints (lt_of_not_ge hsmall)
    refine Or.inr ⟨θ, v, α, γ, hT, hstrip, hareaEq, hα, hγ, hU, hV, ?_⟩
    rw [← hareaEq]
    exact volumeReal_le_actual_capScore_sum hT.isCompact hT.isConnected hstrip hU hV

end AmbidextrousSofa
