module

public import AmbidextrousSofa.Analysis.SupportCurvature

@[expose] public section

/-!
# Actual axis faces of a downward cap

The right face runs from the baseline to the attained roof; the left
face has the opposite tangent orientation. These identities identify the
axis curvature atoms with the actual endpoint heights, and express nearby
curvature masses through the literal Stieltjes distribution function.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem imported_supp_zero (U : Set Plane) : MovingSofaOptimality.supp U 0 = horizontalRight U := by
  change support U (unitNormal 0) = _
  simpa only [unitNormal, Real.cos_zero, Real.sin_zero] using support_horizontal_right U

theorem IsDownwardCap.imported_supp_pi {U : Set Plane} (hU : IsDownwardCap U) :
    MovingSofaOptimality.supp U Real.pi = -horizontalLeft U := by
  change support U (unitNormal Real.pi) = _
  simpa only [unitNormal, Real.cos_pi, Real.sin_pi] using
    support_horizontal_left hU.isCompact hU.nonempty

private theorem mem_suppLine_iff {S : Set Plane} {t : ℝ} {p : Plane} :
    p ∈ MovingSofaOptimality.suppLine S t ↔
      MovingSofaOptimality.dot p (MovingSofaOptimality.uvec t) = MovingSofaOptimality.supp S t :=
  Iff.rfl

theorem IsDownwardCap.axis_vplus_zero {U : Set Plane} (hU : IsDownwardCap U) :
    MovingSofaOptimality.vplus U 0 = (horizontalRight U, capRoof U (horizontalRight U)) := by
  have hp := MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody 0
  have hx : (MovingSofaOptimality.vplus U 0).1 = horizontalRight U := by
    simpa only [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_zero, imported_supp_zero]
      using hp.2
  have hroof : (horizontalRight U, capRoof U (horizontalRight U)) ∈ MovingSofaOptimality.edge U 0 :=
    ⟨capRoof_mem hU.isCompact (horizontalRight_mem hU.nonempty hU.isCompact), by
      rw [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_zero, imported_supp_zero]⟩
  have hlo : capRoof U (horizontalRight U) ≤ (MovingSofaOptimality.vplus U 0).2 := by
    simpa [MovingSofaOptimality.dot, MovingSofaOptimality.vvec] using MovingSofaOptimality.dot_le_dot_vplus hU.isCompact hroof
  have hhi : (MovingSofaOptimality.vplus U 0).2 ≤ capRoof U (MovingSofaOptimality.vplus U 0).1 :=
    le_capRoof hU.isCompact hp.1
  rw [hx] at hhi
  exact Prod.ext hx (le_antisymm hhi hlo)

theorem IsDownwardCap.axis_vminus_zero {U : Set Plane} (hU : IsDownwardCap U) :
    MovingSofaOptimality.vminus U 0 = (horizontalRight U, 0) := by
  have hp := MovingSofaOptimality.vminus_mem_edge hU.imported_isConvexBody 0
  have hx : (MovingSofaOptimality.vminus U 0).1 = horizontalRight U := by
    simpa only [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_zero, imported_supp_zero]
      using hp.2
  have hbase : (horizontalRight U, 0) ∈ MovingSofaOptimality.edge U 0 :=
    ⟨hU.baseline_mem (capRoof_mem hU.isCompact (horizontalRight_mem hU.nonempty hU.isCompact)), by
      rw [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_zero, imported_supp_zero]⟩
  have hhi : (MovingSofaOptimality.vminus U 0).2 ≤ 0 := by
    simpa [MovingSofaOptimality.dot, MovingSofaOptimality.vvec] using MovingSofaOptimality.dot_vminus_le_dot hU.isCompact hbase
  exact Prod.ext hx (le_antisymm hhi (hU.inStrip hp.1).1)

theorem IsDownwardCap.axis_vplus_pi {U : Set Plane} (hU : IsDownwardCap U) :
    MovingSofaOptimality.vplus U Real.pi = (horizontalLeft U, 0) := by
  have hp := MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody Real.pi
  have hx : (MovingSofaOptimality.vplus U Real.pi).1 = horizontalLeft U := by
    have h := hp.2
    rw [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_pi, hU.imported_supp_pi] at h
    linarith
  have hbase : (horizontalLeft U, 0) ∈ MovingSofaOptimality.edge U Real.pi :=
    ⟨hU.baseline_mem (capRoof_mem hU.isCompact (horizontalLeft_mem hU.nonempty hU.isCompact)), by
      rw [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_pi, hU.imported_supp_pi]⟩
  have hhi : (MovingSofaOptimality.vplus U Real.pi).2 ≤ 0 := by
    have h := MovingSofaOptimality.dot_le_dot_vplus hU.isCompact hbase
    simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi, Real.cos_pi,
      neg_zero, mul_zero, zero_mul, mul_neg, mul_one, zero_add] at h
    linarith
  exact Prod.ext hx (le_antisymm hhi (hU.inStrip hp.1).1)

theorem IsDownwardCap.axis_vminus_pi {U : Set Plane} (hU : IsDownwardCap U) :
    MovingSofaOptimality.vminus U Real.pi = (horizontalLeft U, capRoof U (horizontalLeft U)) := by
  have hp := MovingSofaOptimality.vminus_mem_edge hU.imported_isConvexBody Real.pi
  have hx : (MovingSofaOptimality.vminus U Real.pi).1 = horizontalLeft U := by
    have h := hp.2
    rw [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_pi, hU.imported_supp_pi] at h
    linarith
  have hroof : (horizontalLeft U, capRoof U (horizontalLeft U)) ∈ MovingSofaOptimality.edge U Real.pi :=
    ⟨capRoof_mem hU.isCompact (horizontalLeft_mem hU.nonempty hU.isCompact), by
      rw [mem_suppLine_iff, MovingSofaOptimality.dot_uvec_pi, hU.imported_supp_pi]⟩
  have hlo : capRoof U (horizontalLeft U) ≤ (MovingSofaOptimality.vminus U Real.pi).2 := by
    have h := MovingSofaOptimality.dot_vminus_le_dot hU.isCompact hroof
    simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi, Real.cos_pi,
      neg_zero, mul_zero, mul_neg, mul_one, zero_add] at h
    linarith
  have hhi : (MovingSofaOptimality.vminus U Real.pi).2 ≤
      capRoof U (MovingSofaOptimality.vminus U Real.pi).1 :=
    le_capRoof hU.isCompact hp.1
  rw [hx] at hhi
  exact Prod.ext hx (le_antisymm hhi hlo)

theorem IsDownwardCap.axis_curvature_zero {U : Set Plane} (hU : IsDownwardCap U) :
    (upperCurvature U {0}).toReal = capRoof U (horizontalRight U) := by
  change MovingSofaOptimality.sigmaAt U 0 = _
  rw [MovingSofaOptimality.sigmaAt_eq_dot_sub hU.imported_isConvexBody,
    hU.axis_vplus_zero, hU.axis_vminus_zero]
  simp [MovingSofaOptimality.dot, MovingSofaOptimality.vvec]

theorem IsDownwardCap.axis_curvature_pi {U : Set Plane} (hU : IsDownwardCap U) :
    (upperCurvature U {Real.pi}).toReal = capRoof U (horizontalLeft U) := by
  change MovingSofaOptimality.sigmaAt U Real.pi = _
  rw [MovingSofaOptimality.sigmaAt_eq_dot_sub hU.imported_isConvexBody,
    hU.axis_vplus_pi, hU.axis_vminus_pi]
  simp [MovingSofaOptimality.dot, MovingSofaOptimality.vvec]

theorem IsDownwardCap.sigmaFun_zero {U : Set Plane} (hU : IsDownwardCap U) :
    MovingSofaOptimality.sigmaFun U 0 = capRoof U (horizontalRight U) := by
  simp [MovingSofaOptimality.sigmaFun, hU.axis_vplus_zero, MovingSofaOptimality.dot, MovingSofaOptimality.vvec]

theorem IsDownwardCap.sigmaFun_leftLim_pi {U : Set Plane} (hU : IsDownwardCap U) :
    Function.leftLim (MovingSofaOptimality.sigmaFun U) Real.pi =
      (∫ t in (0 : ℝ)..Real.pi, MovingSofaOptimality.supp U t) - capRoof U (horizontalLeft U) := by
  rw [MovingSofaOptimality.leftLim_sigmaFun hU.imported_isConvexBody, hU.axis_vminus_pi]
  simp only [MovingSofaOptimality.dot, MovingSofaOptimality.vvec, Real.sin_pi, Real.cos_pi, neg_zero,
    mul_zero, mul_neg, mul_one, zero_add]
  ring

theorem IsDownwardCap.upperCurvature_real_Ioc {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) :
    (upperCurvature U).real (Ioc a b) = MovingSofaOptimality.sigmaFun U b - MovingSofaOptimality.sigmaFun U a := by
  rw [Measure.real, hU.upperCurvature_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (MovingSofaOptimality.monotone_sigmaFun hU.imported_isConvexBody hab))]

theorem IsDownwardCap.upperCurvature_real_Ioc_zero {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : 0 ≤ t) :
    (upperCurvature U).real (Ioc 0 t) =
      MovingSofaOptimality.sigmaFun U t - capRoof U (horizontalRight U) := by
  rw [hU.upperCurvature_real_Ioc ht, hU.sigmaFun_zero]

theorem IsDownwardCap.upperCurvature_real_Ioo_pi {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : t < Real.pi) :
    (upperCurvature U).real (Ioo t Real.pi) =
      (∫ s in (0 : ℝ)..Real.pi, MovingSofaOptimality.supp U s) - capRoof U (horizontalLeft U) -
        MovingSofaOptimality.sigmaFun U t := by
  have hK := hU.imported_isConvexBody
  have hmeasure : upperCurvature U (Ioo t Real.pi) =
      ENNReal.ofReal (Function.leftLim (MovingSofaOptimality.sigmaFun U) Real.pi - MovingSofaOptimality.sigmaFun U t) := by
    change MovingSofaOptimality.sigma U (Ioo t Real.pi) = _
    simp [MovingSofaOptimality.sigma, MovingSofaOptimality.sigmaStieltjes, hK, StieltjesFunction.measure_Ioo]
  have hnonneg : 0 ≤ Function.leftLim (MovingSofaOptimality.sigmaFun U) Real.pi - MovingSofaOptimality.sigmaFun U t :=
    sub_nonneg.mpr ((MovingSofaOptimality.monotone_sigmaFun hK).le_leftLim ht)
  rw [Measure.real, hmeasure, ENNReal.toReal_ofReal hnonneg, hU.sigmaFun_leftLim_pi]

end AmbidextrousSofa
