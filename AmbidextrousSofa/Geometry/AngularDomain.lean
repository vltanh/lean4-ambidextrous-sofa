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
  refine ⟨h.angle_pos, h.angle_le, ?_, ?_⟩
  · intro θ hθ p hp
    have hs : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, h.angle_le, Real.pi_pos])).le
    have hc : 0 ≤ Real.cos θ := (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.trans_le h.angle_le⟩).le
    have hu : support (AmbidextrousSofa.upperCap K) (unitNormal θ) = support K (unitNormal θ) :=
      support_upperCap hK hne hK0 hs
    have hv : support (AmbidextrousSofa.upperCap K) (companionNormal θ) = support K (companionNormal θ) :=
      support_upperCap hK hne hK0 hc
    simpa only [canonicalHall, hu, hv] using h.inside θ hθ hp
  · intro p hp
    have hs : 0 ≤ Real.sin α := (Real.sin_pos_of_pos_of_lt_pi h.angle_pos
      (by linarith [h.angle_le, Real.pi_pos])).le
    rw [support_upperCap hK hne hK0 hs]
    exact h.terminal p hp

/-- A continuous lifted angle visits every value between its initial and terminal values. -/
theorem RigidMotionPath.exists_frameAngle_of_terminal {path : RigidMotionPath}
    (hstart : path.angle 0 = 0) {α θ : ℝ} (hend : -path.angle 1 = α)
    (hθ : θ ∈ Icc 0 α) :
    ∃ t ∈ motionInterval, -path.angle t = θ := by
  have hcont : ContinuousOn (fun t => -path.angle t) (Icc 0 1) :=
    path.continuous_angle.neg
  have hbetween : θ ∈ Icc (-path.angle 0) (-path.angle 1) := by
    simpa only [hstart, neg_zero, hend] using hθ
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hbetween

/-- A normalized genuine proper-terminal passage supplies every angular constraint.
Backtracking of the original angle is unrestricted. -/
theorem Passage.angularConstraints_of_terminal {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) (hstart : path.angle 0 = 0)
    {α : ℝ} (hend : -path.angle 1 = α) (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2) :
    AngularConstraints S (actualHull S) α := by
  refine ⟨hα0, hαL, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨t, ht, hangle⟩ := RigidMotionPath.exists_frameAngle_of_terminal
      hstart hend ⟨hθ.1.le, hθ.2.le⟩
    simpa only [hangle] using h.subset_canonicalHall_at hS hne ht
  · intro p hp
    have hwall := h.terminal_support_lower hne hp
    rw [hend] at hwall
    simpa only [support_actualHull hS hne] using hwall

/-- A visited quarter turn supplies all earlier frames, even when the motion later reverses. -/
theorem RigidMotionPath.exists_frameAngle_of_reaches {path : RigidMotionPath}
    (hstart : path.angle 0 = 0) {τ α θ : ℝ} (hτ : τ ∈ motionInterval)
    (hreach : -path.angle τ = α) (hθ : θ ∈ Icc 0 α) :
    ∃ t ∈ motionInterval, -path.angle t = θ := by
  have hsub : Icc (0 : ℝ) τ ⊆ motionInterval := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hτ.2⟩
  have hcont := path.continuous_angle.neg.mono hsub
  have hbetween : θ ∈ Icc (-path.angle 0) (-path.angle τ) := by
    simpa only [hstart, neg_zero, hreach] using hθ
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hτ.1 hcont hbetween
  exact ⟨t, hsub ht, heq⟩

/-- At a full turn the top-support wall follows from the actual incoming strip. -/
theorem support_terminal_pi_div_two_of_strip {S K : Set Plane} (hne : K.Nonempty)
    (hKstrip : K ⊆ unitStrip) (hSstrip : S ⊆ unitStrip) {p : Plane} (hp : p ∈ S) :
    support K (unitNormal (Real.pi / 2)) - 1 ≤
      coordDot p (unitNormal (Real.pi / 2)) := by
  have htop : support K (0, 1) ≤ 1 := by
    apply support_le_of_forall hne
    intro q hq
    simpa only [coordDot, mul_zero, mul_one, zero_add] using (hKstrip hq).2
  simp only [unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two, coordDot,
    mul_zero, mul_one, zero_add]
  linarith [(hSstrip hp).1]

theorem Passage.angularConstraints_of_reaches_pi_div_two
    {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ unitStrip)
    (hstart : path.angle 0 = 0) {τ : ℝ} (hτ : τ ∈ motionInterval)
    (hreach : -path.angle τ = Real.pi / 2) :
    AngularConstraints S (actualHull S) (Real.pi / 2) := by
  refine ⟨by linarith [Real.pi_pos], le_rfl, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨t, ht, hangle⟩ := RigidMotionPath.exists_frameAngle_of_reaches
      hstart hτ hreach ⟨hθ.1.le, hθ.2.le⟩
    simpa only [hangle] using h.subset_canonicalHall_at hS hne ht
  · intro p hp
    exact support_terminal_pi_div_two_of_strip (actualHull_nonempty hne)
      (actualHull_subset_unitStrip hstrip) hstrip hp

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
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [RigidMotionPath.reflected_placement]
    exact (reflect_mem_lowerHall _).mpr (h.inside t ht (mem_image_of_mem _ hp))
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [RigidMotionPath.reflected_placement]
    exact (reflect_mem_incomingArm _).mpr (h.start (mem_image_of_mem _ hp))
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [RigidMotionPath.reflected_placement]
    exact (reflect_mem_lowerOutgoingArm _).mpr (h.finish (mem_image_of_mem _ hp))

end AmbidextrousSofa
