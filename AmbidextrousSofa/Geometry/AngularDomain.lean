module

public import AmbidextrousSofa.Geometry.Barriers
public import AmbidextrousSofa.Geometry.Reflection

@[expose] public section

/-!
# Continuous passages and their complete angular constraints

The intermediate value theorem, rather than monotonicity of a motion, supplies
every intervening angle. A genuine terminal angle in `(0, π/2]` retains its
outgoing whole-body support wall. A visited full quarter turn uses the incoming
unit strip for the endpoint wall. Reflection turns an independent upper passage
into a lower passage by an explicit continuous rigid motion.

These results do not claim that every original passage has one of the stated
angular reaches. The wrong-way exclusion and the reach dichotomy are separate
remaining steps of the original-domain reduction.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- All actual frame constraints, together with the whole outgoing support wall. -/
structure AngularConstraints (S K : Set Plane) (α : ℝ) : Prop where
  angle_pos : 0 < α
  angle_le : α ≤ Real.pi / 2
  inside : ∀ θ ∈ Ioo 0 α, S ⊆ canonicalHall K (unitNormal θ) (companionNormal θ)
  terminal : ∀ p ∈ S, support K (unitNormal α) - 1 ≤ coordDot p (unitNormal α)

/-- Each retained point satisfies the entire swept barrier, including its terminal wall. -/
theorem AngularConstraints.partialBarrier_le {S K : Set Plane} {α : ℝ}
    (h : AngularConstraints S K α) (hstrip : S ⊆ unitStrip) {p : Plane} (hp : p ∈ S) :
    partialBarrier K α p.1 ≤ p.2 :=
  partialBarrier_le_of_angular_constraints h.angle_pos h.angle_le (hstrip hp).1
    (fun θ hθ => h.inside θ hθ hp) (h.terminal p hp)

/-- Downward filling changes none of the upward-facing walls used by a passage. -/
theorem AngularConstraints.upperCap {S K : Set Plane} {α : ℝ}
    (h : AngularConstraints S K α) (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : AngularConstraints S (AmbidextrousSofa.upperCap K) α := by
  have hsin {θ : ℝ} (h0 : 0 < θ) (hθ : θ ≤ α) : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith [h.angle_le, Real.pi_pos])
  refine ⟨h.angle_pos, h.angle_le, fun θ hθ p hp => ?_, fun p hp => ?_⟩
  · have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, h.angle_le]⟩
    simpa only [canonicalHall, support_upperCap (v := unitNormal θ) hK hne hK0 (hsin hθ.1 hθ.2.le),
      support_upperCap (v := companionNormal θ) hK hne hK0 hc] using h.inside θ hθ hp
  · rw [support_upperCap hK hne hK0 (hsin h.angle_pos le_rfl)]; exact h.terminal p hp

/-- A continuous lifted angle visits every value between `0` and any value it reaches, in
either direction, even when the motion later reverses. -/
theorem RigidMotionPath.exists_frameAngle_of_reaches {path : RigidMotionPath}
    (hstart : path.angle 0 = 0) {τ α θ : ℝ} (hτ : τ ∈ motionInterval)
    (hreach : -path.angle τ = α) (hθ : θ ∈ uIcc 0 α) :
    ∃ t ∈ motionInterval, -path.angle t = θ := by
  have hsub : Icc (0 : ℝ) τ ⊆ motionInterval := Icc_subset_Icc_right hτ.2
  obtain ⟨t, ht, heq⟩ := intermediate_value_uIcc (a := 0) (b := τ) (f := fun t => -path.angle t)
    (by rw [uIcc_of_le hτ.1]; exact path.continuous_angle.neg.mono hsub)
    (by simpa only [hstart, neg_zero, hreach] using hθ)
  exact ⟨t, hsub (by rwa [uIcc_of_le hτ.1] at ht), heq⟩

/-- A continuous lifted angle visits every value between its initial and terminal values. -/
theorem RigidMotionPath.exists_frameAngle_of_terminal {path : RigidMotionPath}
    (hstart : path.angle 0 = 0) {α θ : ℝ} (hend : -path.angle 1 = α)
    (hθ : θ ∈ Icc 0 α) :
    ∃ t ∈ motionInterval, -path.angle t = θ :=
  exists_frameAngle_of_reaches hstart ⟨zero_le_one, le_rfl⟩ hend (Icc_subset_uIcc hθ)

/-- A normalized genuine proper-terminal passage supplies every angular constraint.
Backtracking of the original angle is unrestricted. -/
theorem Passage.angularConstraints_of_terminal {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) (hstart : path.angle 0 = 0)
    {α : ℝ} (hend : -path.angle 1 = α) (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2) :
    AngularConstraints S (actualHull S) α := by
  refine ⟨hα0, hαL, fun θ hθ => ?_, fun p hp => ?_⟩
  · obtain ⟨t, ht, hangle⟩ := RigidMotionPath.exists_frameAngle_of_terminal
      hstart hend ⟨hθ.1.le, hθ.2.le⟩
    simpa only [hangle] using h.subset_canonicalHall_at hS hne ht
  · simpa only [support_actualHull hS hne, hend] using h.terminal_support_lower hne hp

theorem Passage.angularConstraints_of_reaches_pi_div_two
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ unitStrip)
    (hstart : path.angle 0 = 0) {τ : ℝ} (hτ : τ ∈ motionInterval)
    (hreach : -path.angle τ = Real.pi / 2) :
    AngularConstraints S (actualHull S) (Real.pi / 2) := by
  refine ⟨by positivity, le_rfl, fun θ hθ => ?_, fun p hp => ?_⟩
  · obtain ⟨t, ht, hangle⟩ := RigidMotionPath.exists_frameAngle_of_reaches
      hstart hτ hreach (Icc_subset_uIcc ⟨hθ.1.le, hθ.2.le⟩)
    simpa only [hangle] using h.subset_canonicalHall_at hS hne ht
  · -- at a full turn the top-support wall follows from the actual incoming strip
    have htop : support S (0, 1) ≤ 1 :=
      support_le_of_forall hne fun q hq => by simpa [coordDot] using (hstrip hq).2
    simp only [support_actualHull hS hne, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      coordDot, mul_zero, mul_one, zero_add]
    linarith [(hstrip hp).1]

/-- Reflect both the body and its placements across the strip center line. -/
def RigidMotionPath.reflected (path : RigidMotionPath) : RigidMotionPath where
  angle := fun t => -path.angle t
  shift := fun t => ((path.shift t).1 - Real.sin (path.angle t),
    1 - Real.cos (path.angle t) - (path.shift t).2)
  continuous_angle := path.continuous_angle.neg
  continuous_shift :=
    (path.continuous_shift.fst.sub
        (Real.continuous_sin.comp_continuousOn path.continuous_angle)).prodMk
      ((continuousOn_const.sub (Real.continuous_cos.comp_continuousOn path.continuous_angle)).sub
        path.continuous_shift.snd)

theorem RigidMotionPath.reflected_placement (path : RigidMotionPath) (t : ℝ) (p : Plane) :
    path.reflected.placement t (reflect p) = reflect (path.placement t p) := by
  apply Prod.ext <;>
    simp only [RigidMotionPath.reflected, RigidMotionPath.placement, rigidMap, rotate,
      reflect, Real.cos_neg, Real.sin_neg, Prod.fst_add, Prod.snd_add] <;> ring

/-- The independent upper passage becomes an ordinary lower passage of the reflected body. -/
theorem Passage.reflected {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S upperHall incomingArm upperOutgoingArm path) :
    Passage (reflect '' S) lowerHall incomingArm lowerOutgoingArm path.reflected := by
  refine ⟨fun t ht => ?_, ?_, ?_⟩ <;> rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩ <;>
    rw [RigidMotionPath.reflected_placement]
  exacts [(reflect_mem_lowerHall _).2 (h.inside t ht (mem_image_of_mem _ hp)),
    (reflect_mem_incomingArm _).2 (h.start (mem_image_of_mem _ hp)),
    (reflect_mem_lowerOutgoingArm _).2 (h.finish (mem_image_of_mem _ hp))]

end AmbidextrousSofa
