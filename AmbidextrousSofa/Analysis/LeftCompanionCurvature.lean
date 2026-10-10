import AmbidextrousSofa.Analysis.LeftCompanionCap
import AmbidextrousSofa.Analysis.TerminalSupportTails

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

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem affineNormal_coefficient_identity (m t : ℝ) :
    Real.cos (Real.arctan m) * (Real.cos t + m * Real.sin t) =
      Real.sin (affineNormalAngle m - t) := by
  have hsin : Real.sin (Real.arctan m) = m * Real.cos (Real.arctan m) := by
    have h := Real.tan_arctan m
    rwa [Real.tan_eq_sin_div_cos, div_eq_iff (Real.cos_arctan_pos m).ne'] at h
  rw [affineNormalAngle, Real.sin_sub, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, hsin]
  ring

theorem affineNormal_coefficient_pos_before {m t : ℝ}
    (ht0 : 0 ≤ t) (htm : t < affineNormalAngle m) :
    0 < Real.cos t + m * Real.sin t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htm)
    (show affineNormalAngle m - t < Real.pi by linarith only [(affineNormalAngle_mem m).2, ht0])
  by_contra hbad
  have hprod := mul_nonpos_of_nonneg_of_nonpos (Real.cos_arctan_pos m).le
    (le_of_not_gt hbad)
  rw [affineNormal_coefficient_identity] at hprod
  exact (not_lt_of_ge hprod) hs

theorem affineNormal_coefficient_nonpos_after {m t : ℝ}
    (hmt : affineNormalAngle m ≤ t) (htπ : t ≤ Real.pi) :
    Real.cos t + m * Real.sin t ≤ 0 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hmt)
    (show t - affineNormalAngle m ≤ Real.pi by linarith only [(affineNormalAngle_mem m).1, htπ])
  have heq : Real.sin (affineNormalAngle m - t) = -Real.sin (t - affineNormalAngle m) := by
    rw [show affineNormalAngle m - t = -(t - affineNormalAngle m) by ring, Real.sin_neg]
  by_contra hbad
  have hprod := mul_pos (Real.cos_arctan_pos m) (lt_of_not_ge hbad)
  rw [affineNormal_coefficient_identity, heq] at hprod
  linarith only [hs, hprod]

/-- The actual left endpoint of an upper supporting face stays in the
left cut once the normal has passed the affine middle normal. The
joining coefficient is allowed to be zero. -/
theorem IsDownwardCap.vplus_mem_leftCompanionCap_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hs : 0 < Real.sin t) (hcoef : Real.cos t + m * Real.sin t ≤ 0) :
    Imported.vplus U t ∈ leftCompanionCap U a := by
  let p := Imported.vplus U t
  have hp := Imported.vplus_mem_edge hU.imported_isConvexBody t
  refine ⟨hp.1, (hU.fst_mem_Icc hp.1).1, ?_⟩
  by_cases hpa : p.1 ≤ a
  · exact hpa
  · have hceiling : p.2 ≤ m * p.1 + c :=
      (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa only [p, Prod.mk.eta] using hp.1)).trans
        (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
    have hheight := mul_le_mul_of_nonneg_right hceiling hs.le
    have hhorizontal := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (le_of_not_ge hpa)) hcoef
    have hline := haffine a ⟨le_rfl, hab.le⟩
    have hdot : coordDot p (unitNormal t) ≤ coordDot (a, capRoof U a) (unitNormal t) := by
      unfold coordDot unitNormal
      rw [hline]
      nlinarith only [hheight, hhorizontal]
    have hpA : (a, capRoof U a) ∈ Imported.edge U t := by
      refine ⟨capRoof_mem hU.isCompact ha, ?_⟩
      change coordDot (a, capRoof U a) (unitNormal t) = angleSupport U t
      apply le_antisymm (coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact ha) _)
      have hpval : coordDot p (unitNormal t) = angleSupport U t := hp.2
      rwa [hpval] at hdot
    have hprojection : a ∈ horizontalProjection (Imported.edge U t) :=
      ⟨(a, capRoof U a), hpA, rfl⟩
    rw [hU.horizontalProjection_edge hs.le] at hprojection
    exact hprojection.1

theorem IsDownwardCap.vplus_leftCompanionCap_eq_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hs : 0 < Real.sin t) (hcoef : Real.cos t + m * Real.sin t ≤ 0) :
    Imported.vplus (leftCompanionCap U a) t = Imported.vplus U t := by
  have hV := hU.leftCompanionCap ha
  have hp := Imported.vplus_mem_edge hU.imported_isConvexBody t
  have hpV := hU.vplus_mem_leftCompanionCap_of_affine ha hb hab haffine hs hcoef
  have hsupport : angleSupport (leftCompanionCap U a) t = angleSupport U t := by
    exact support_eq_of_mem hV.isCompact
      (fun p hp => coordDot_le_support hU.isCompact hp.1 (unitNormal t)) hpV hp.2
  symm
  apply Imported.cvx_eq_vplus hV.imported_isConvexBody
    (show Imported.vplus U t ∈ Imported.edge (leftCompanionCap U a) t from
      ⟨hpV, hp.2.trans hsupport.symm⟩)
  intro q hq
  apply Imported.dot_le_dot_vplus hU.isCompact
  refine ⟨hq.1.1, ?_⟩
  change coordDot q (unitNormal t) = angleSupport U t
  rw [← hsupport]
  exact hq.2

theorem IsDownwardCap.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hs : 0 < Real.sin t) (hcoef : 0 < Real.cos t + m * Real.sin t) :
    Imported.vplus (leftCompanionCap U a) t = (a, capRoof U a) := by
  have hV := hU.leftCompanionCap ha
  have hline := haffine a ⟨le_rfl, hab.le⟩
  have hceiling (p : Plane) (hp : p ∈ leftCompanionCap U a) : p.2 ≤ m * p.1 + c :=
    (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa only [Prod.mk.eta] using hp.1)).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
  have hsupport : angleSupport (leftCompanionCap U a) t =
      coordDot (a, capRoof U a) (unitNormal t) := by
    refine support_eq_of_mem hV.isCompact ?_ (hU.rightRoof_mem_leftCompanionCap ha) rfl
    intro p hp
    have hheight := mul_le_mul_of_nonneg_right (hceiling p hp) hs.le
    have hhorizontal := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp.2.2) hcoef.le
    unfold coordDot unitNormal
    rw [hline]
    nlinarith only [hheight, hhorizontal]
  let p := Imported.vplus (leftCompanionCap U a) t
  have hp := Imported.vplus_mem_edge hV.imported_isConvexBody t
  have hpval : p.1 * Real.cos t + p.2 * Real.sin t =
      a * Real.cos t + capRoof U a * Real.sin t := hp.2.trans hsupport
  have hheight := mul_le_mul_of_nonneg_right (hceiling p hp.1) hs.le
  have hax : a ≤ p.1 := by
    apply (mul_le_mul_left hcoef).mp
    rw [hline] at hpval
    nlinarith only [hpval, hheight]
  have hpx : p.1 = a := le_antisymm hp.1.2.2 hax
  apply Prod.ext hpx
  rw [hpx] at hpval
  apply le_antisymm
  · apply (mul_le_mul_right hs).mp
    linarith only [hpval]
  · apply (mul_le_mul_right hs).mp
    linarith only [hpval]

/-- Positive tilt has no initial curvature through the middle normal,
including the joining atom. Pinning supplies its exact right endpoint. -/
theorem IsJointCapMaximizer.leftCompanion_initial_curvature_zero
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α) (hm : 0 < m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) (affineNormalAngle m)) = 0 := by
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hV := hU.isCap.leftCompanionCap ha
  have hm0 : 0 < Real.arctan m := Real.arctan_pos.mpr hm
  have hLm : Real.pi / 2 ≤ affineNormalAngle m := by
    unfold affineNormalAngle
    linarith only [hm0]
  apply Imported.sigma_Ioc_eq_zero_of_vplus_const hV.imported_isConvexBody hLm
    (p := (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)))
  intro t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (by linarith only [ht.1, Real.pi_pos]) (ht.2.trans_lt (affineNormalAngle_mem m).2)
  rcases ht.2.eq_or_lt with htm | htm
  · rw [htm] at hs ⊢
    rw [hU.isCap.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine hs
      (affineNormal_coefficient_nonpos_after le_rfl (affineNormalAngle_mem m).2.le)]
    exact (hU.middle_support_vertices hm.ne' haffine).1
  · exact hU.isCap.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient
      ha hb hab haffine hs (affineNormal_coefficient_pos_before
        (by linarith only [ht.1, Real.pi_pos]) htm)

/-- Equality of the literal boundary endpoints on a closed angle arc
implies equality of the Stieltjes curvature measures on its Ioc arc. -/
theorem upperCurvature_restrict_Ioc_eq_of_vplus_eq
    {U V : Set Plane} (hU : IsDownwardCap U) (hV : IsDownwardCap V) {a b : ℝ}
    (hab : a ≤ b) (hpoints : ∀ t ∈ Icc a b, Imported.vplus U t = Imported.vplus V t) :
    (upperCurvature U).restrict (Ioc a b) = (upperCurvature V).restrict (Ioc a b) := by
  have hcurvature {x y : ℝ} (hxy : x ≤ y) (hx : a ≤ x) (hy : y ≤ b) :
      upperCurvature U (Ioc x y) = upperCurvature V (Ioc x y) := by
    have hsupp (t : ℝ) (ht : t ∈ Icc x y) : Imported.supp U t = Imported.supp V t := by
      rw [← Imported.dot_vplus_uvec U t, ← Imported.dot_vplus_uvec V t,
        hpoints t ⟨hx.trans ht.1, ht.2.trans hy⟩]
    have hi : (∫ t in x..y, Imported.supp U t) = ∫ t in x..y, Imported.supp V t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hxy] at ht
      exact hsupp t ht
    rw [hU.upperCurvature_Ioc, hV.upperCurvature_Ioc,
      Imported.sa_sigmaFun_sub hU.imported_isConvexBody,
      Imported.sa_sigmaFun_sub hV.imported_isConvexBody,
      hpoints x ⟨hx, hxy.trans hy⟩, hpoints y ⟨hx.trans hxy, hy⟩, hi]
  apply Measure.ext_of_Ioc
  intro x y _hxy
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
  have hinter : Ioc x y ∩ Ioc a b = Ioc (max x a) (min y b) := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [hinter]
  by_cases hspan : max x a ≤ min y b
  · exact hcurvature hspan (le_max_right _ _) (min_le_right _ _)
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hspan)]

/-- The curvature after the middle normal is exactly the original
charged-wing curvature, with the original middle atom excluded. -/
theorem IsDownwardCap.leftCompanion_curvature_restrict_after_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x y : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ z ∈ Icc a b, capRoof U z = m * z + c)
    (hxy : x ≤ y) (hmx : affineNormalAngle m ≤ x) (hyπ : y < Real.pi) :
    (upperCurvature (leftCompanionCap U a)).restrict (Ioc x y) =
      (upperCurvature U).restrict (Ioc x y) := by
  apply upperCurvature_restrict_Ioc_eq_of_vplus_eq (hU.leftCompanionCap ha) hU hxy
  intro t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    ((affineNormalAngle_mem m).1.trans_le (hmx.trans ht.1)) (ht.2.trans_lt hyπ)
  exact hU.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine hs
    (affineNormal_coefficient_nonpos_after (hmx.trans ht.1) (ht.2.trans hyπ.le))

end AmbidextrousSofa
