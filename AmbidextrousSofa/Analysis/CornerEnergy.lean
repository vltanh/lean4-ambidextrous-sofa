import AmbidextrousSofa.Analysis.PositivePartCalculus
import AmbidextrousSofa.Analysis.ShadowCurvature

/-!
# A clipped energy for one regular corner quarter

Write `p = -secondCornerVelocity` and `q = firstCornerVelocity`.
The actual support equations are `p' = u - 1 - q` and
`q' = v - 1 + p`. The same-sign source law makes the quadratic
energy decrease where both velocities are positive. Clipping `p` at
zero extends this to an energy barrier without classifying connected
components of the positive-velocity set.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def clippedCornerEnergy (p q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (max (p t) 0 - 1 / 2) ^ 2 + (q t + 1) ^ 2

theorem absolutelyContinuousOnInterval_clippedCornerEnergy
    {p q : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) :
    AbsolutelyContinuousOnInterval (clippedCornerEnergy p q) a b := by
  have hc (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hp' := (absolutelyContinuousOnInterval_max_const hp 0).sub (hc (1 / 2))
  have hq' := hq.add (hc 1)
  simpa only [clippedCornerEnergy, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, pow_two] using
    (hp'.mul hp').add (hq'.mul hq')

/-- The clipping-level derivative is included in this formula; it is
zero almost everywhere there, rather than being assigned arbitrarily. -/
theorem ae_hasDerivAt_clippedCornerEnergy
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b) (hab : a ≤ b)
    (hode : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      HasDerivAt (clippedCornerEnergy p q)
        (2 * (max (p t) 0 - 1 / 2) *
            (if 0 < p t then u t - 1 - q t else 0) +
          2 * (q t + 1) * (v t - 1 + p t)) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hode,
    ae_restrict_of_ae (ae_hasDerivAt_max_const hp 0)] with t ht hd hclip
  have ht' : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨ht.1.le, ht.2.le⟩
  have hclip' : HasDerivAt (fun x => max (p x) 0)
      (if 0 < p t then u t - 1 - q t else 0) t := by
    simpa only [hd.1.deriv] using hclip ht'
  have he := ((hclip'.sub_const (1 / 2)).pow 2).add ((hd.2.add_const 1).pow 2)
  change HasDerivAt (clippedCornerEnergy p q) _ t at he
  apply he.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]

theorem sourceKappa_le_one_of_bounds {q : ℝ} (hql : -1 ≤ q) (hqr : q ≤ 1) :
    sourceKappa q ≤ 1 := by
  have habs : |q| ≤ 1 := abs_le.mpr ⟨hql, hqr⟩
  unfold sourceKappa
  exact max_le habs (by linarith)

/-- The right sides of the support equations have a fixed negative
drift in the two mixed sign half-planes. -/
theorem corner_velocity_drift {p q u v : ℝ}
    (hu : u ≤ sourceKappa q) (hv : v ≤ sourceKappa p) :
    (0 < q → u - 1 - q ≤ -1 / 2) ∧
      (p < 0 → v - 1 + p ≤ -1 / 2) := by
  constructor
  · intro hq
    have hbound : sourceKappa q ≤ q + 1 / 2 := by
      rw [sourceKappa, abs_of_pos hq]
      apply max_le <;> linarith
    linarith
  · intro hp
    have hbound : sourceKappa p ≤ -p + 1 / 2 := by
      rw [sourceKappa, abs_of_neg hp]
      apply max_le <;> linarith
    linarith

/-- Above `17/4` the energy derivative is nonpositive. The bound
`p ≤ 1`, `q ≥ -1` comes from nonnegative actual support arms. -/
theorem clippedCornerEnergy_derivative_nonpos_above
    {p q u v : ℝ} (hp : p ≤ 1) (hq : -1 ≤ q)
    (hv : v ≤ sourceKappa p)
    (hshadow : 0 < p → 0 < q → u = 0 ∧ v ≤ 1 / 2)
    (hE : 17 / 4 < (max p 0 - 1 / 2) ^ 2 + (q + 1) ^ 2) :
    2 * (max p 0 - 1 / 2) * (if 0 < p then u - 1 - q else 0) +
      2 * (q + 1) * (v - 1 + p) ≤ 0 := by
  have hqpos : 0 < q := by
    by_contra hnot
    have hq0 : q ≤ 0 := le_of_not_gt hnot
    have hm0 : 0 ≤ max p 0 := le_max_right _ _
    have hm1 : max p 0 ≤ 1 := max_le hp (by norm_num)
    have hmprod := mul_nonneg hm0 (sub_nonneg.mpr hm1)
    have hqprod := mul_nonneg (neg_nonneg.mpr hq0) (by linarith : 0 ≤ q + 1)
    nlinarith
  by_cases hppos : 0 < p
  · obtain ⟨hu0, hvhalf⟩ := hshadow hppos hqpos
    rw [max_eq_left hppos.le, if_pos hppos, hu0]
    have hprod := mul_nonneg (by linarith : 0 ≤ q + 1)
      (by linarith : 0 ≤ 1 / 2 - v)
    nlinarith
  · have hp0 : p ≤ 0 := le_of_not_gt hppos
    have hvhalf : v - 1 + p ≤ -1 / 2 := by
      have hbound : sourceKappa p ≤ -p + 1 / 2 := by
        rw [sourceKappa, abs_of_nonpos hp0]
        apply max_le <;> linarith
      linarith
    rw [max_eq_right hp0, if_neg hppos, mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem clippedCornerEnergy_le_of_initial
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hstart : clippedCornerEnergy p q a ≤ 17 / 4)
    (hode : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), p t ≤ 1 ∧ -1 ≤ q t)
    (hκ : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ 17 / 4 := by
  apply absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab hstart _ ht
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy hp hab hode, hbound, hκ, hshadow]
    with x hd hb hk hs
  intro hE
  rw [hd.deriv]
  exact clippedCornerEnergy_derivative_nonpos_above hb.1 hb.2 hk hs hE

theorem curvature_le_one_of_clippedCornerEnergy
    {p q u : ℝ} (hq : -1 ≤ q) (hu : u ≤ sourceKappa q)
    (hshadow : 0 < p → 0 < q → u = 0)
    (hE : (max p 0 - 1 / 2) ^ 2 + (q + 1) ^ 2 ≤ 17 / 4) :
    u ≤ 1 := by
  by_cases hq1 : q ≤ 1
  · exact hu.trans (sourceKappa_le_one_of_bounds hq hq1)
  · have hqgt : 1 < q := lt_of_not_ge hq1
    have hppos : 0 < p := by
      by_contra hnot
      rw [max_eq_right (le_of_not_gt hnot)] at hE
      nlinarith [sq_nonneg (q - 1)]
    rw [hshadow hppos (by linarith)]
    norm_num

/-- A complete one-quarter ODE implication. The hypotheses here are
ordinary differential identities and pointwise source laws, rather
than a hypothesis asserting the desired unit-curvature conclusion. -/
theorem ae_curvature_le_one_of_cornerEnergy
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hstart : clippedCornerEnergy p q a ≤ 17 / 4)
    (hode : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), p t ≤ 1 ∧ -1 ≤ q t)
    (hκ : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      u t ≤ sourceKappa (q t) ∧ v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), u t ≤ 1 := by
  have hE := clippedCornerEnergy_le_of_initial hp hq hab hstart hode hbound
    (hκ.mono (fun _ ht => ht.2)) hshadow
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hbound, hκ, hshadow]
    with t ht hb hk hs
  exact curvature_le_one_of_clippedCornerEnergy hb.2 hk.1
    (fun hp hq => (hs hp hq).1) (hE ⟨ht.1.le, ht.2.le⟩)

def actualCornerEnergy (U : Set Plane) : ℝ → ℝ :=
  clippedCornerEnergy (fun t => -secondCornerVelocity U t) (firstCornerVelocity U)

theorem IsDownwardCap.firstCornerVelocity_ge_neg_one
    {U : Set Plane} (hU : IsDownwardCap U) (t : ℝ) :
    -1 ≤ firstCornerVelocity U t := by
  rw [firstCornerVelocity_eq_gPlus]
  linarith [(Imported.inj_arm_nonneg hU.imported_isConvexBody t).2.2.1]

theorem IsDownwardCap.neg_secondCornerVelocity_le_one
    {U : Set Plane} (hU : IsDownwardCap U) (t : ℝ) :
    -secondCornerVelocity U t ≤ 1 := by
  rw [secondCornerVelocity_eq_fPlus]
  linarith [(Imported.inj_arm_nonneg hU.imported_isConvexBody t).1]

/-- Application to the literal curvature density of an actual full
maximizer. The interval avoids both actual exceptional normals. All
support equations, arm bounds, and same-sign laws are discharged here. -/
theorem IsFullCapMaximizer.ae_density_le_one_of_cornerEnergy_on_interval
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c C a b : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hsub : Icc a b ⊆ regularCornerDomain m)
    (hstart : actualCornerEnergy U a ≤ 17 / 4) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), ρ t ≤ 1 := by
  have hbase : Icc a b ⊆ regularCurvatureDomain m := fun t ht => (hsub ht).2.1
  have hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ regularCurvatureDomain m := by
    intro t ht
    have hm : t - Real.pi / 2 ∈ Icc a b := by
      constructor <;> linarith [ht.1, ht.2]
    simpa only [sub_add_cancel] using (hsub hm).2.2
  have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hab hbase hshift
  have hode : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      HasDerivAt (fun x => -secondCornerVelocity U x)
        (ρ t - 1 - firstCornerVelocity U t) t ∧
      HasDerivAt (firstCornerVelocity U)
        (ρ (t + Real.pi / 2) - 1 + -secondCornerVelocity U t) t := by
    filter_upwards [hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
      hρ hρ0 hρC heq hab hbase hshift] with t ht
    constructor
    · exact ht.2.neg.congr_deriv (by ring)
    · exact ht.1.congr_deriv (by ring)
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      -secondCornerVelocity U t ≤ 1 ∧ -1 ≤ firstCornerVelocity U t :=
    Eventually.of_forall (fun t =>
      ⟨hU.isCap.neg_secondCornerVelocity_le_one t, hU.isCap.firstCornerVelocity_ge_neg_one t⟩)
  have hk : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      ρ t ≤ sourceKappa (firstCornerVelocity U t) ∧
      ρ (t + Real.pi / 2) ≤ sourceKappa (-secondCornerVelocity U t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htq := (hsub (Ioo_subset_Icc_self ht)).1
    have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith [htq.1]
    constructor
    · simpa only [upperCornerVelocity, if_pos htq.2] using hκ t
    · simpa only [upperCornerVelocity, if_neg hnot, add_sub_cancel_right,
        sourceKappa_neg] using hκ (t + Real.pi / 2)
  have hs : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      0 < -secondCornerVelocity U t → 0 < firstCornerVelocity U t →
        ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Icc_self.trans hsub)
      (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρC heq)] with t ht
    intro hp hq
    exact ht.1 ⟨hq, by linarith⟩
  exact ae_curvature_le_one_of_cornerEnergy hac.2.neg hac.1 hab hstart hode hb hk hs

/-- The density and its source laws are produced by the actual
maximizer; only the starting scalar energy and the regular interval
remain as explicit geometric inputs. -/
theorem IsFullCapMaximizer.curvature_density_unit_on_interval_of_cornerEnergy
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c a b : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hab : a ≤ b) (hsub : Icc a b ⊆ regularCornerDomain m)
    (hstart : actualCornerEnergy U a ≤ 17 / 4) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), ρ t ≤ 1) := by
  obtain ⟨ρ, hρ, hb, hC, heq, _⟩ := hU.curvature_density_corner_controls hheight haffine
  exact ⟨ρ, hρ, hb, hC, heq,
    hU.ae_density_le_one_of_cornerEnergy_on_interval haffine hρ
      (fun t => (hb t).1) hC (fun t => (hb t).2) heq hab hsub hstart⟩

end AmbidextrousSofa
