module

public import AmbidextrousSofa.Analysis.SupportDensityCalculus
public import AmbidextrousSofa.Analysis.NegativeCornerCurvature
public import AmbidextrousSofa.Analysis.LevelSetDerivative

@[expose] public section

/-!
# Actual attached-corner velocities and floor-contact flatness

The corner is built from the actual two support values. Its coordinate
derivatives follow from the support/tangent identities on regular
intervals. The two velocity derivatives follow from the actual curvature
density equations. Applying the proved level-set derivative theorem
twice gives both zero vertical velocity and zero vertical acceleration
at almost every floor contact.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def cornerVelocityX (U : Set Plane) (t : ℝ) : ℝ :=
  -secondCornerVelocity U t * Real.cos t - firstCornerVelocity U t * Real.sin t

def cornerVelocityY (U : Set Plane) (t : ℝ) : ℝ :=
  -secondCornerVelocity U t * Real.sin t + firstCornerVelocity U t * Real.cos t

theorem attachedCorner_fst_eq_support (U : Set Plane) (t : ℝ) :
    (attachedCorner U t).1 = (angleSupport U t - 1) * Real.cos t -
      (angleSupport U (t + Real.pi / 2) - 1) * Real.sin t := by
  simp only [attachedCorner, angleSupport, companionNormal_eq_unitNormal]

theorem attachedCorner_snd_eq_support (U : Set Plane) (t : ℝ) :
    (attachedCorner U t).2 = (angleSupport U t - 1) * Real.sin t +
      (angleSupport U (t + Real.pi / 2) - 1) * Real.cos t := by
  simp only [attachedCorner, angleSupport, companionNormal_eq_unitNormal]

theorem IsDownwardCap.hasDerivAt_angleSupport_shift_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b d x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Icc (a + d) (b + d) ⊆ S) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t => angleSupport U (t + d)) (supportTangent U (x + d)) x :=
  (hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hsub
    ⟨add_lt_add_left hx.1 _, add_lt_add_left hx.2 _⟩).comp_add_const x d

theorem IsDownwardCap.hasDerivAt_attachedCorner_fst_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t => (attachedCorner U t).1) (cornerVelocityX U x) x := by
  have hf := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hbase hx
  have hg := hU.hasDerivAt_angleSupport_shift_of_density hρ hρ0 hρC heq hshift hx
  rw [funext (attachedCorner_fst_eq_support U)]
  refine (((hf.sub_const 1).mul (Real.hasDerivAt_cos x)).sub
    ((hg.sub_const 1).mul (Real.hasDerivAt_sin x))).congr_deriv ?_
  simp only [cornerVelocityX, firstCornerVelocity, secondCornerVelocity, supportTangent,
    ← angleSupport_eq_imported_supp]
  ring

theorem IsDownwardCap.hasDerivAt_attachedCorner_snd_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t => (attachedCorner U t).2) (cornerVelocityY U x) x := by
  have hf := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hbase hx
  have hg := hU.hasDerivAt_angleSupport_shift_of_density hρ hρ0 hρC heq hshift hx
  rw [funext (attachedCorner_snd_eq_support U)]
  refine (((hf.sub_const 1).mul (Real.hasDerivAt_sin x)).add
    ((hg.sub_const 1).mul (Real.hasDerivAt_cos x))).congr_deriv ?_
  simp only [cornerVelocityY, firstCornerVelocity, secondCornerVelocity, supportTangent,
    ← angleSupport_eq_imported_supp]
  ring

/-- The actual corner has zero vertical velocity and acceleration at
almost every floor contact in each regular interval. This includes
arbitrary closed or disconnected floor-contact sets. -/
theorem IsDownwardCap.ae_corner_floor_flatness_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), (attachedCorner U x).2 = 0 →
      cornerVelocityY U x = 0 ∧
      ρ x * Real.sin x + ρ (x + Real.pi / 2) * Real.cos x -
        Real.sin x - Real.cos x + 2 * cornerVelocityX U x = 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (ae_two_derivatives_eq_zero_on_level
      (fun t => (attachedCorner U t).2) (cornerVelocityY U)),
    hU.ae_hasDerivAt_cornerVelocities_of_density hρ hρ0 hρC heq hab hbase hshift]
    with x hx hlevel hv hfloor
  have hy : cornerVelocityY U x = 0 := (hU.hasDerivAt_attachedCorner_snd_of_density
    hρ hρ0 hρC heq hbase hshift hx).deriv.symm.trans (hlevel.1 hfloor)
  -- The vertical velocity is differentiable with the stated acceleration.
  have hd : HasDerivAt (cornerVelocityY U) (ρ x * Real.sin x + ρ (x + Real.pi / 2) * Real.cos x -
      Real.sin x - Real.cos x + 2 * cornerVelocityX U x) x := by
    refine ((hv.2.neg.mul (Real.hasDerivAt_sin x)).add
      (hv.1.mul (Real.hasDerivAt_cos x))).congr_deriv ?_
    simp only [cornerVelocityX, Pi.neg_apply]
    ring
  exact ⟨hy, hd.deriv.symm.trans (hlevel.2 hy)⟩

end AmbidextrousSofa
