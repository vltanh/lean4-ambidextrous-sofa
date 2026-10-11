module

public import AmbidextrousSofa.Analysis.PositivePartCalculus
public import AmbidextrousSofa.Analysis.ShadowCurvature

@[expose] public section

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
  have hp' := (absolutelyContinuousOnInterval_max_const hp 0).fun_sub (hc (1 / 2))
  have hq' := hq.fun_add (hc 1)
  convert (hp'.fun_mul hp').fun_add (hq'.fun_mul hq') using 2
  simp only [clippedCornerEnergy, sq]

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
  have hclip := hclip (by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self ht)
  rw [hd.1.deriv] at hclip
  exact (((hclip.sub_const (1 / 2)).pow 2).add ((hd.2.add_const 1).pow 2)).congr_deriv (by simp)

theorem sourceKappa_le_one_of_bounds {q : ℝ} (hql : -1 ≤ q) (hqr : q ≤ 1) :
    sourceKappa q ≤ 1 :=
  max_le (abs_le.mpr ⟨hql, hqr⟩) (by linarith [abs_le.mpr ⟨hql, hqr⟩])

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
    by_contra! hq0
    linarith [mul_nonneg (le_max_right p 0) (sub_nonneg.mpr (max_le hp zero_le_one)),
      mul_nonneg (neg_nonneg.mpr hq0) (by linarith : 0 ≤ q + 1)]
  split_ifs with hppos
  · obtain ⟨rfl, hv⟩ := hshadow hppos hqpos
    rw [max_eq_left hppos.le]
    linarith [mul_nonneg (by linarith : 0 ≤ q + 1) (by linarith : 0 ≤ 1 / 2 - v)]
  · rw [sourceKappa, abs_of_nonpos (not_lt.mp hppos)] at hv
    have hv' : v ≤ -p + 1 / 2 := hv.trans (max_le (by linarith) (by linarith))
    linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ q + 1) (by linarith : v - 1 + p ≤ 0)]

theorem curvature_le_one_of_clippedCornerEnergy
    {p q u : ℝ} (hq : -1 ≤ q) (hu : u ≤ sourceKappa q)
    (hshadow : 0 < p → 0 < q → u = 0)
    (hE : (max p 0 - 1 / 2) ^ 2 + (q + 1) ^ 2 ≤ 17 / 4) :
    u ≤ 1 := by
  rcases le_or_gt q 1 with hq1 | hq1
  · exact hu.trans (sourceKappa_le_one_of_bounds hq hq1)
  rcases le_or_gt p 0 with hp | hp
  · rw [max_eq_right hp] at hE
    linarith [sq_nonneg (q - 1)]
  · linarith [hshadow hp (by linarith)]

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
  have hE {t : ℝ} (ht : t ∈ Icc a b) : clippedCornerEnergy p q t ≤ 17 / 4 := by
    refine absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
      (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab hstart ?_ ht
    filter_upwards [ae_hasDerivAt_clippedCornerEnergy hp hab hode, hbound, hκ, hshadow]
      with x hd hb hk hs hE
    exact hd.deriv.le.trans (clippedCornerEnergy_derivative_nonpos_above hb.1 hb.2 hk.2 hs hE)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hbound, hκ, hshadow] with t ht hb hk hs
  exact curvature_le_one_of_clippedCornerEnergy hb.2 hk.1 (fun hp hq => (hs hp hq).1)
    (hE (Ioo_subset_Icc_self ht))

def actualCornerEnergy (U : Set Plane) : ℝ → ℝ :=
  clippedCornerEnergy (fun t => -secondCornerVelocity U t) (firstCornerVelocity U)

theorem IsDownwardCap.firstCornerVelocity_ge_neg_one
    {U : Set Plane} (hU : IsDownwardCap U) (t : ℝ) :
    -1 ≤ firstCornerVelocity U t := by
  rw [firstCornerVelocity_eq_gPlus]
  linarith [(MovingSofaOptimality.inj_arm_nonneg hU.imported_isConvexBody t).2.2.1]

theorem IsDownwardCap.neg_secondCornerVelocity_le_one
    {U : Set Plane} (hU : IsDownwardCap U) (t : ℝ) :
    -secondCornerVelocity U t ≤ 1 := by
  rw [secondCornerVelocity_eq_fPlus]
  linarith [(MovingSofaOptimality.inj_arm_nonneg hU.imported_isConvexBody t).1]

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
  have hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ regularCurvatureDomain m :=
    fun t ht => by
      simpa using (hsub (show t - Real.pi / 2 ∈ Icc a b from
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2.2
  have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hab hbase hshift
  refine ae_curvature_le_one_of_cornerEnergy (v := fun t => ρ (t + Real.pi / 2)) hac.2.fun_neg
    hac.1 hab hstart ?_ (.of_forall fun t => ⟨hU.isCap.neg_secondCornerVelocity_le_one t,
      hU.isCap.firstCornerVelocity_ge_neg_one t⟩) ?_ ?_
  · filter_upwards [hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
      hρ hρ0 hρC heq hab hbase hshift] with t ht
    exact ⟨ht.2.neg.congr_deriv (by ring), ht.1.congr_deriv (by ring)⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htq := (hsub (Ioo_subset_Icc_self ht)).1
    have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith [htq.1]
    exact ⟨by simpa [upperCornerVelocity, htq.2] using hκ t,
      by simpa [upperCornerVelocity, hnot, sourceKappa_neg] using hκ (t + Real.pi / 2)⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub)
      (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρC heq)] with t ht hp hq
    exact ht.1 ⟨hq, by linarith⟩

end AmbidextrousSofa
