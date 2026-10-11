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

/-- The outgoing endpoint really supplies a whole-body unit strip. -/
theorem Passage.terminal_frameStrip {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path) :
    ∀ p ∈ S, -(path.shift 1).1 ≤ coordDot p (unitNormal (-path.angle 1)) ∧
      coordDot p (unitNormal (-path.angle 1)) ≤ -(path.shift 1).1 + 1 := fun p hp => by
  obtain ⟨h0, h1, -⟩ := h.finish (mem_image_of_mem _ hp)
  simp only [RigidMotionPath.placement, rigidMap, rotate, Prod.fst_add, coordDot, unitNormal,
    Real.cos_neg, Real.sin_neg] at h0 h1 ⊢
  constructor <;> linarith

/-- A large sofa cannot even pass below the forbidden angle: continuity would
force it to visit that angle first. -/
theorem Passage.frameAngle_gt_neg_pi_div_four
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hstrip : S ⊆ unitStrip) (hstart : path.angle 0 = 0)
    (harea : Real.sqrt 2 < volume.real S) {t : ℝ} (ht : t ∈ motionInterval) :
    -(Real.pi / 4) < -path.angle t := by
  by_contra! hle
  have hsub : Icc (0 : ℝ) t ⊆ motionInterval := Icc_subset_Icc_right ht.2
  obtain ⟨s, hs, hsangle⟩ := intermediate_value_Icc' ht.1 (path.continuous_angle.neg.mono hsub)
    (show -(Real.pi / 4) ∈ Icc (-path.angle t) (-path.angle 0) by
      rw [hstart, neg_zero]; exact ⟨hle, by linarith [Real.pi_pos]⟩)
  -- pull the placement at time `s` back to the translated frame hallway
  refine harea.not_ge (volumeReal_le_sqrt_two_of_wrongWay_frameHall hstrip
    (a := -(path.shift s).1) (b := -(path.shift s).2) fun p hp => ?_)
  rw [← hsangle]
  exact (rigidMap_mem_lowerHall_iff _ (path.shift s) p).mp <| by
    simpa only [Pi.neg_apply, neg_neg, RigidMotionPath.placement] using
      h.inside s (hsub hs) (mem_image_of_mem _ hp)

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
    exact ⟨Real.pi / 2, by linarith [Real.pi_pos], le_rfl,
      h.angularConstraints_of_reaches_pi_div_two hS hne hstrip hstart ht htangle,
      Or.inl ⟨rfl, t, ht, htangle⟩⟩
  -- the terminal strip rules out all remaining endpoint angles up to `π/4`
  have hend : Real.pi / 4 < -path.angle 1 := by
    by_contra! hhigh
    exact harea.not_ge (volumeReal_le_sqrt_two_of_unitStrip_and_smallAngleStrip hstrip
      ⟨(h.frameAngle_gt_neg_pi_div_four hstrip hstart harea ⟨zero_le_one, le_rfl⟩).le, hhigh⟩
      h.terminal_frameStrip)
  have hendL : -path.angle 1 < Real.pi / 2 := by
    by_contra! hnot
    exact hfull (RigidMotionPath.exists_frameAngle_of_terminal hstart rfl
      ⟨by linarith [Real.pi_pos], hnot⟩)
  exact ⟨-path.angle 1, hend, hendL.le, h.angularConstraints_of_terminal hS hne hstart rfl
    (by linarith [Real.pi_pos]) hendL.le, Or.inr ⟨rfl, hendL⟩⟩

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
  obtain ⟨α, hα, -, hU, -⟩ := hlower.exists_effectiveAngle hS hne hstrip hlower0 harea
  have hSh := isCompact_image_reflect hS
  have hSn := hne.image reflect
  have hSstrip := image_reflect_subset_unitStrip hstrip
  obtain ⟨γ, hγ, -, hV, -⟩ := hupper.reflected.exists_effectiveAngle hSh hSn hSstrip
    (by simp [RigidMotionPath.reflected, hupper0]) (by rwa [volumeReal_image_reflect])
  refine ⟨α, γ, hα, hγ, hU.upperCap (isCompact_actualHull hS) (actualHull_nonempty hne)
    (fun _ hp => (actualHull_subset_unitStrip hstrip hp).1), ?_⟩
  simpa only [reflectedHullCap, actualHull_reflect] using
    hV.upperCap (isCompact_actualHull hSh) (actualHull_nonempty hSn)
      (fun _ hp => (actualHull_subset_unitStrip hSstrip hp).1)

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
  obtain ⟨θ, v, lower, upper, hT, hstrip, hareaEq, hl0, hu0, hl, hu⟩ := hS.exists_normalized
  obtain ⟨α, γ, hα, hγ, hU, hV⟩ := hullCap_constraints_of_large_passages
    hT.isCompact hT.nonempty hstrip hl hu hl0 hu0 (hareaEq ▸ harea)
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
  refine (le_or_gt _ _).imp id fun harea => ?_
  obtain ⟨θ, v, α, γ, hT, hstrip, hareaEq, hα, hγ, hU, hV⟩ :=
    hS.exists_normalized_angularConstraints harea
  exact ⟨θ, v, α, γ, hT, hstrip, hareaEq, hα, hγ, hU, hV,
    hareaEq ▸ volumeReal_le_actual_capScore_sum hT.isCompact hT.isConnected hstrip hU hV⟩

end AmbidextrousSofa
