import AmbidextrousSofa.Geometry.Motions

/-!
# Rigid changes of body coordinates

The coordinate plane has the product norm, so the rotations below are handled
as explicit linear homeomorphisms. No assertion that they are isometries for
that norm is used. Rebasing a motion subtracts its initial real angle lift;
the common incoming orientation is needed only as equality of rotation maps.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem rotate_rotate (θ φ : ℝ) (p : Plane) :
    rotate θ (rotate φ p) = rotate (θ + φ) p := by
  apply Prod.ext <;> simp only [rotate, Real.cos_add, Real.sin_add] <;> ring

theorem rotate_add_vector (θ : ℝ) (p q : Plane) :
    rotate θ (p + q) = rotate θ p + rotate θ q := by
  apply Prod.ext <;> simp only [rotate, Prod.fst_add, Prod.snd_add] <;> ring

theorem rotate_sub_vector (θ : ℝ) (p q : Plane) :
    rotate θ (p - q) = rotate θ p - rotate θ q := by
  apply Prod.ext <;> simp only [rotate, Prod.fst_sub, Prod.snd_sub] <;> ring

@[simp]
theorem rotate_neg_rotate (θ : ℝ) (p : Plane) :
    rotate (-θ) (rotate θ p) = p := by
  rw [rotate_rotate, neg_add_cancel, rotate_zero]

@[simp]
theorem rotate_rotate_neg (θ : ℝ) (p : Plane) :
    rotate θ (rotate (-θ) p) = p := by
  rw [rotate_rotate, add_neg_cancel, rotate_zero]

theorem continuous_rotate (θ : ℝ) : Continuous (rotate θ) := by
  unfold rotate
  fun_prop

theorem continuous_rigidMap (θ : ℝ) (v : Plane) : Continuous (rigidMap θ v) :=
  (continuous_rotate θ).add continuous_const

/-- A coordinate rotation as a linear map, with a fixed two-vector basis. -/
def rotationLinearMap (θ : ℝ) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

@[simp]
theorem rotationLinearMap_apply (θ : ℝ) (p : Plane) :
    rotationLinearMap θ p = rotate θ p := by
  simp [rotationLinearMap, Matrix.toLin_finTwoProd_apply, rotate, sub_eq_add_neg]

@[simp]
theorem coe_rotationLinearMap (θ : ℝ) :
    (rotationLinearMap θ : Plane → Plane) = rotate θ :=
  funext (rotationLinearMap_apply θ)

/-- The determinant calculation does not depend on the product norm. -/
@[simp]
theorem det_rotationLinearMap (θ : ℝ) : LinearMap.det (rotationLinearMap θ) = 1 := by
  simp only [rotationLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  nlinarith [Real.sin_sq_add_cos_sq θ]

def rotationHomeomorph (θ : ℝ) : Plane ≃ₜ Plane where
  toFun := rotate θ
  invFun := rotate (-θ)
  left_inv := rotate_neg_rotate θ
  right_inv := rotate_rotate_neg θ
  continuous_toFun := continuous_rotate θ
  continuous_invFun := continuous_rotate (-θ)

def rigidHomeomorph (θ : ℝ) (v : Plane) : Plane ≃ₜ Plane where
  toFun := rigidMap θ v
  invFun := fun p => rotate (-θ) (p - v)
  left_inv := by
    intro p
    simp only [rigidMap, add_sub_cancel_right, rotate_neg_rotate]
  right_inv := by
    intro p
    simp only [rigidMap, rotate_rotate_neg, sub_add_cancel]
  continuous_toFun := continuous_rigidMap θ v
  continuous_invFun := (continuous_rotate (-θ)).comp (continuous_id.sub continuous_const)

theorem rigidMap_injective (θ : ℝ) (v : Plane) : Function.Injective (rigidMap θ v) :=
  (rigidHomeomorph θ v).injective

theorem rigidMap_surjective (θ : ℝ) (v : Plane) : Function.Surjective (rigidMap θ v) :=
  (rigidHomeomorph θ v).surjective

theorem rigidMap_eq_of_rotate_eq {θ φ : ℝ} (h : rotate θ = rotate φ) (v : Plane) :
    rigidMap θ v = rigidMap φ v := by
  funext p
  simp only [rigidMap, h]

/-- Express an old path in body coordinates obtained by a fixed rigid map. -/
def RigidMotionPath.rebase (path : RigidMotionPath) (β : ℝ) (v : Plane) :
    RigidMotionPath where
  angle := fun t => path.angle t - β
  shift := fun t => path.shift t - rotate (path.angle t - β) v
  continuous_angle := path.continuous_angle.sub continuousOn_const
  continuous_shift := by
    have ha := path.continuous_angle
    have hs := path.continuous_shift
    unfold rotate
    fun_prop

@[simp]
theorem RigidMotionPath.rebase_angle_zero (path : RigidMotionPath) (v : Plane) :
    (path.rebase (path.angle 0) v).angle 0 = 0 := by
  simp [RigidMotionPath.rebase]

/-- The rebased path places the transformed body at the same physical points. -/
theorem RigidMotionPath.rebase_placement (path : RigidMotionPath)
    (β : ℝ) (v : Plane) (t : ℝ) (p : Plane) :
    (path.rebase β v).placement t (rigidMap β v p) = path.placement t p := by
  simp only [RigidMotionPath.rebase, RigidMotionPath.placement, rigidMap,
    rotate_add_vector, rotate_rotate, sub_add_cancel]
  abel

theorem Passage.rebase {S hall incoming outgoing : Set Plane} {path : RigidMotionPath}
    (h : Passage S hall incoming outgoing path) (β : ℝ) (v : Plane) :
    Passage (rigidMap β v '' S) hall incoming outgoing (path.rebase β v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [RigidMotionPath.rebase_placement]
    exact h.inside t ht ⟨p, hp, rfl⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [RigidMotionPath.rebase_placement]
    exact h.start ⟨p, hp, rfl⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [RigidMotionPath.rebase_placement]
    exact h.finish ⟨p, hp, rfl⟩

theorem Passage.rebase_of_same_rotation
    {S hall incoming outgoing : Set Plane} {path : RigidMotionPath}
    (h : Passage S hall incoming outgoing path) {β γ : ℝ}
    (hβγ : rotate β = rotate γ) (v : Plane) :
    Passage (rigidMap β v '' S) hall incoming outgoing (path.rebase γ v) := by
  rw [rigidMap_eq_of_rotate_eq hβγ]
  exact h.rebase γ v

/-- A shared incoming placement puts the actual body in the unit strip.
The two original translations remain independent after the change of body
coordinates, and both new real angle lifts start at zero. -/
theorem IsAmbidextrous.exists_normalized_passages {S : Set Plane}
    (hS : IsAmbidextrous S) :
    ∃ (θ : ℝ) (v : Plane) (lower upper : RigidMotionPath),
      let T := rigidMap θ v '' S
      IsAmbidextrous T ∧ T ⊆ unitStrip ∧
        lower.angle 0 = 0 ∧ upper.angle 0 = 0 ∧
        Passage T lowerHall incomingArm lowerOutgoingArm lower ∧
        Passage T upperHall incomingArm upperOutgoingArm upper := by
  obtain ⟨lower, upper, horient, hlower, hupper⟩ := hS.passages
  let θ := lower.angle 0
  let v := lower.shift 0
  let T := rigidMap θ v '' S
  let lower' := lower.rebase (lower.angle 0) v
  let upper' := upper.rebase (upper.angle 0) v
  have hl : Passage T lowerHall incomingArm lowerOutgoingArm lower' :=
    hlower.rebase θ v
  have hu : Passage T upperHall incomingArm upperOutgoingArm upper' :=
    hupper.rebase_of_same_rotation horient v
  have hl0 : lower'.angle 0 = 0 := lower.rebase_angle_zero v
  have hu0 : upper'.angle 0 = 0 := upper.rebase_angle_zero v
  have hT : IsAmbidextrous T := by
    refine ⟨hS.nonempty.image _, hS.isCompact.image (continuous_rigidMap θ v),
      hS.isConnected.image _ (continuous_rigidMap θ v).continuousOn,
      lower', upper', ?_, hl, hu⟩
    simp only [SameInitialOrientation, hl0, hu0]
  refine ⟨θ, v, lower', upper', hT, ?_, hl0, hu0, hl, hu⟩
  intro p hp
  have hp' : p ∈ incomingArm := hlower.start hp
  exact ⟨hp'.2.1, hp'.2.2⟩

end AmbidextrousSofa
