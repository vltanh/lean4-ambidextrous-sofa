module

public import AmbidextrousSofa.Geometry.Motions

@[expose] public section

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

theorem rotate_rotate (θ φ : ℝ) (p : Plane) : rotate θ (rotate φ p) = rotate (θ + φ) p := by
  apply Prod.ext <;> simp only [rotate, Real.cos_add, Real.sin_add] <;> ring

theorem rotate_add_vector (θ : ℝ) (p q : Plane) :
    rotate θ (p + q) = rotate θ p + rotate θ q := by
  apply Prod.ext <;> simp only [rotate, Prod.fst_add, Prod.snd_add] <;> ring

theorem rotate_sub_vector (θ : ℝ) (p q : Plane) :
    rotate θ (p - q) = rotate θ p - rotate θ q := by
  apply Prod.ext <;> simp only [rotate, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem continuous_rigidMap (θ : ℝ) (v : Plane) : Continuous (rigidMap θ v) := by
  unfold rigidMap rotate; fun_prop

/-- A coordinate rotation as a linear map, with a fixed two-vector basis. -/
def rotationLinearMap (θ : ℝ) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

@[simp]
theorem coe_rotationLinearMap (θ : ℝ) : (rotationLinearMap θ : Plane → Plane) = rotate θ :=
  funext fun p => by simp [rotationLinearMap, Matrix.toLin_finTwoProd_apply, rotate, sub_eq_add_neg]

/-- The determinant calculation does not depend on the product norm. -/
@[simp]
theorem det_rotationLinearMap (θ : ℝ) : LinearMap.det (rotationLinearMap θ) = 1 := by
  simp [rotationLinearMap, Matrix.det_fin_two_of, ← sq]

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
  have e (t : ℝ) :
      (path.rebase β v).placement t '' (rigidMap β v '' S) = path.placement t '' S := by
    simp only [image_image, RigidMotionPath.rebase_placement]
  exact ⟨fun t ht => e t ▸ h.inside t ht, e 0 ▸ h.start, e 1 ▸ h.finish⟩

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
  have hrot : rigidMap (lower.angle 0) = rigidMap (upper.angle 0) := by
    unfold rigidMap; rw [horient]
  have hl := hlower.rebase (lower.angle 0) (lower.shift 0)
  have hu := hupper.rebase (upper.angle 0) (lower.shift 0)
  rw [← hrot] at hu
  refine ⟨lower.angle 0, lower.shift 0, _, _, ⟨hS.nonempty.image _,
    hS.isCompact.image (continuous_rigidMap _ _),
    hS.isConnected.image _ (continuous_rigidMap _ _).continuousOn, _, _, ?_, hl, hu⟩,
    fun _ hp => (hlower.start hp).2, lower.rebase_angle_zero _, upper.rebase_angle_zero _, hl, hu⟩
  simp [SameInitialOrientation]

end AmbidextrousSofa
