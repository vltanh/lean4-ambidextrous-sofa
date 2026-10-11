module

public import AmbidextrousSofa.Analysis.LeftCompanionCap
public import AmbidextrousSofa.Analysis.TerminalSupportTails
public import AmbidextrousSofa.Analysis.SurfaceAreaFacts
import MovingSofaOptimality.Convex.ConvexCurve

@[expose] public section

/-!
# The literal curvature of the left companion cut

After the affine middle normal, the left cut and the original cap have
the same actual right-continuous supporting endpoint. Before that normal
in positive tilt, the cut endpoint is constant at the low middle point.
At the joining normal, the actual middle-facet pinning gives that same
endpoint. Consequently the cut has no initial curvature mass through the
joining normal, including no atom at that normal.

The local Stieltjes-measure identity below transfers the unchanged
charged-wing curvature exactly. It neither removes nor approximates the
original middle-facet atom: that atom is outside the transferred Ioc arc.
-/

noncomputable section

open Set Filter MeasureTheory MovingSofaOptimality

namespace AmbidextrousSofa

theorem affineNormal_coefficient_identity (m t : ℝ) :
    Real.cos (Real.arctan m) * (Real.cos t + m * Real.sin t) =
      Real.sin (affineNormalAngle m - t) := by
  rw [affineNormalAngle, Real.sin_sub, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    Real.sin_arctan, Real.cos_arctan]
  ring

theorem affineNormal_coefficient_pos_before {m t : ℝ}
    (ht0 : 0 ≤ t) (htm : t < affineNormalAngle m) :
    0 < Real.cos t + m * Real.sin t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htm)
    (show affineNormalAngle m - t < Real.pi by linarith only [(affineNormalAngle_mem m).2, ht0])
  rw [← affineNormal_coefficient_identity] at hs
  exact pos_of_mul_pos_right hs (Real.cos_arctan_pos m).le

theorem affineNormal_coefficient_nonpos_after {m t : ℝ}
    (hmt : affineNormalAngle m ≤ t) (htπ : t ≤ Real.pi) :
    Real.cos t + m * Real.sin t ≤ 0 := by
  have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le (sub_nonpos.mpr hmt)
    (show -Real.pi ≤ affineNormalAngle m - t by linarith only [(affineNormalAngle_mem m).1, htπ])
  rw [← affineNormal_coefficient_identity] at hs
  exact nonpos_of_mul_nonpos_right hs (Real.cos_arctan_pos m)

/-- After the affine middle normal, the actual left endpoint of an upper supporting face
stays in the left cut, so it is also the endpoint of the cut. The joining coefficient is
allowed to be zero. -/
theorem IsDownwardCap.vplus_leftCompanionCap_eq_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hs : 0 < Real.sin t) (hcoef : Real.cos t + m * Real.sin t ≤ 0) :
    vplus (AmbidextrousSofa.leftCompanionCap U a) t = vplus U t := by
  have hV := hU.leftCompanionCap ha
  have hp := vplus_mem_edge hU.imported_isConvexBody t
  set p := vplus U t
  have hpV : p ∈ AmbidextrousSofa.leftCompanionCap U a := by
    refine ⟨hp.1, (hU.fst_mem_Icc hp.1).1, ?_⟩
    rcases le_or_gt p.1 a with hpa | hpa
    · exact hpa
    have hA := capRoof_mem hU.isCompact ha
    have hceiling := (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U from hp.1)).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
    have hdot : coordDot p (unitNormal t) ≤ coordDot (a, capRoof U a) (unitNormal t) := by
      simp only [coordDot, unitNormal, haffine a ⟨le_rfl, hab.le⟩]
      nlinarith [mul_le_mul_of_nonneg_right hceiling hs.le,
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpa.le) hcoef]
    have hprojection : a ∈ horizontalProjection (edge U t) :=
      ⟨_, ⟨hA, le_antisymm (coordDot_le_support hU.isCompact hA _) (hp.2.symm.trans_le hdot)⟩, rfl⟩
    rw [hU.horizontalProjection_edge hs.le] at hprojection
    exact hprojection.1
  have hsupport : angleSupport (AmbidextrousSofa.leftCompanionCap U a) t = angleSupport U t :=
    support_eq_of_mem hV.isCompact (fun q hq => coordDot_le_support hU.isCompact hq.1 _) hpV hp.2
  exact (cvx_eq_vplus hV.imported_isConvexBody ⟨hpV, hp.2.trans hsupport.symm⟩
    fun q hq => dot_le_dot_vplus hU.isCompact ⟨hq.1.1, hq.2.trans hsupport⟩).symm

theorem IsDownwardCap.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hs : 0 < Real.sin t) (hcoef : 0 < Real.cos t + m * Real.sin t) :
    vplus (AmbidextrousSofa.leftCompanionCap U a) t = (a, capRoof U a) := by
  have hV := hU.leftCompanionCap ha
  have hdot (p : Plane) (hp : p ∈ AmbidextrousSofa.leftCompanionCap U a) :
      coordDot p (unitNormal t) + (a - p.1) * (Real.cos t + m * Real.sin t) ≤
        coordDot (a, capRoof U a) (unitNormal t) := by
    have hceiling := (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U from hp.1)).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
    simp only [coordDot, unitNormal, haffine a ⟨le_rfl, hab.le⟩]
    nlinarith [mul_le_mul_of_nonneg_right hceiling hs.le]
  have hsupport : angleSupport (AmbidextrousSofa.leftCompanionCap U a) t =
      coordDot (a, capRoof U a) (unitNormal t) :=
    support_eq_of_mem hV.isCompact (fun p hp => (le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr hp.2.2) hcoef.le)).trans (hdot p hp))
      (hU.rightRoof_mem_leftCompanionCap ha) rfl
  have hp := vplus_mem_edge hV.imported_isConvexBody t
  set p := vplus (AmbidextrousSofa.leftCompanionCap U a) t
  have hpval : coordDot p (unitNormal t) = coordDot (a, capRoof U a) (unitNormal t) :=
    hp.2.trans hsupport
  have hpx : p.1 = a := le_antisymm hp.1.2.2 (sub_nonpos.mp
    (nonpos_of_mul_nonpos_left (by linarith [hdot p hp.1]) hcoef))
  refine Prod.ext hpx (mul_right_cancel₀ hs.ne' ?_)
  simp only [coordDot, unitNormal, hpx] at hpval
  linarith

/-- Positive tilt has no initial curvature through the middle normal,
including the joining atom. Pinning supplies its exact right endpoint. -/
theorem IsJointCapMaximizer.leftCompanion_initial_curvature_zero
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α) (hm : 0 < m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) (affineNormalAngle m)) = 0 := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (by linarith only [hU.width_bounds.1, one_lt_M])
  refine sigma_Ioc_eq_zero_of_vplus_const
    (hU.isCap.leftCompanionCap ha).imported_isConvexBody
    (le_add_of_nonneg_left (Real.arctan_pos.mpr hm).le)
    (p := (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)))
    fun t ht => ?_
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (by linarith only [ht.1, Real.pi_pos]) (ht.2.trans_lt (affineNormalAngle_mem m).2)
  rcases ht.2.eq_or_lt with rfl | htm
  · exact (hU.isCap.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine hs
      (affineNormal_coefficient_nonpos_after le_rfl (affineNormalAngle_mem m).2.le)).trans
      (hU.middle_support_vertices hm.ne' haffine).1
  · exact hU.isCap.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient
      ha hb hab haffine hs (affineNormal_coefficient_pos_before
        (by linarith only [ht.1, Real.pi_pos]) htm)

/-- Equality of the literal boundary endpoints on a closed angle arc
implies equality of the Stieltjes curvature measures on its Ioc arc. -/
theorem upperCurvature_restrict_Ioc_eq_of_vplus_eq
    {U V : Set Plane} (hU : IsDownwardCap U) (hV : IsDownwardCap V) {a b : ℝ}
    (hpoints : ∀ t ∈ Icc a b, vplus U t = vplus V t) :
    (upperCurvature U).restrict (Ioc a b) = (upperCurvature V).restrict (Ioc a b) := by
  refine Measure.ext_of_Ioc _ _ fun x y _ => ?_
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc]
  by_cases hspan : max x a ≤ min y b
  · have hsub : Icc (max x a) (min y b) ⊆ Icc a b :=
      Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    have hi : (∫ t in max x a..min y b, supp U t) = ∫ t in max x a..min y b, supp V t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [← dot_vplus_uvec U t, ← dot_vplus_uvec V t, hpoints t (hsub (uIcc_of_le hspan ▸ ht))]
    rw [hU.upperCurvature_Ioc, hV.upperCurvature_Ioc, sigmaFun_sub hU.imported_isConvexBody,
      sigmaFun_sub hV.imported_isConvexBody, hpoints _ (hsub ⟨le_rfl, hspan⟩),
      hpoints _ (hsub ⟨hspan, le_rfl⟩), hi]
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hspan), measure_empty, measure_empty]

-- `hxy` is part of the interface; the restriction to an empty arc is trivial.
set_option linter.unusedVariables false in
/-- The curvature after the middle normal is exactly the original
charged-wing curvature, with the original middle atom excluded. -/
theorem IsDownwardCap.leftCompanion_curvature_restrict_after_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x y : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ z ∈ Icc a b, capRoof U z = m * z + c)
    (hxy : x ≤ y) (hmx : affineNormalAngle m ≤ x) (hyπ : y < Real.pi) :
    (upperCurvature (AmbidextrousSofa.leftCompanionCap U a)).restrict (Ioc x y) =
      (upperCurvature U).restrict (Ioc x y) :=
  upperCurvature_restrict_Ioc_eq_of_vplus_eq (hU.leftCompanionCap ha) hU fun t ht =>
    hU.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine (Real.sin_pos_of_pos_of_lt_pi
      ((affineNormalAngle_mem m).1.trans_le (hmx.trans ht.1)) (ht.2.trans_lt hyπ))
      (affineNormal_coefficient_nonpos_after (hmx.trans ht.1) (ht.2.trans hyπ.le))

end AmbidextrousSofa
