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

open Set MeasureTheory MovingSofaOptimality

namespace AmbidextrousSofa

theorem imported_supp_zero (U : Set Plane) : supp U 0 = horizontalRight U := by
  change support U (unitNormal 0) = _
  simpa only [unitNormal, Real.cos_zero, Real.sin_zero] using support_horizontal_right U

theorem imported_supp_pi_div_two (U : Set Plane) : supp U (Real.pi / 2) = capHeight U := by
  change support U (unitNormal (Real.pi / 2)) = support U (0, 1)
  simp only [unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem IsDownwardCap.imported_supp_pi {U : Set Plane} (hU : IsDownwardCap U) :
    supp U Real.pi = -horizontalLeft U := by
  change support U (unitNormal Real.pi) = _
  simpa only [unitNormal, Real.cos_pi, Real.sin_pi] using
    support_horizontal_left hU.isCompact hU.nonempty

private theorem dot_vvec_zero (p : Plane) : dot p (vvec 0) = p.2 := by simp [dot, vvec]

private theorem dot_vvec_pi (p : Plane) : dot p (vvec Real.pi) = -p.2 := by simp [dot, vvec]

/-- The edge at angle `0` is the right face of `U`. -/
private theorem mem_edge_zero {U : Set Plane} {p : Plane} :
    p ∈ edge U 0 ↔ p ∈ U ∧ p.1 = horizontalRight U := by
  rw [mem_edge_iff, dot_uvec_zero, imported_supp_zero]

/-- The edge at angle `π` is the left face of `U`. -/
private theorem IsDownwardCap.mem_edge_pi {U : Set Plane} (hU : IsDownwardCap U) {p : Plane} :
    p ∈ edge U Real.pi ↔ p ∈ U ∧ p.1 = horizontalLeft U := by
  rw [mem_edge_iff, dot_uvec_pi, hU.imported_supp_pi, neg_inj]

theorem IsDownwardCap.axis_vplus_zero {U : Set Plane} (hU : IsDownwardCap U) :
    vplus U 0 = (horizontalRight U, capRoof U (horizontalRight U)) := by
  obtain ⟨hp, hx⟩ := mem_edge_zero.1 (vplus_mem_edge hU.imported_isConvexBody 0)
  have hlo := dot_le_dot_vplus hU.isCompact (mem_edge_zero.2
    ⟨capRoof_mem hU.isCompact (horizontalRight_mem hU.nonempty hU.isCompact), rfl⟩)
  rw [dot_vvec_zero, dot_vvec_zero] at hlo
  exact Prod.ext hx (le_antisymm (hx ▸ le_capRoof hU.isCompact hp) hlo)

theorem IsDownwardCap.axis_vminus_pi {U : Set Plane} (hU : IsDownwardCap U) :
    vminus U Real.pi = (horizontalLeft U, capRoof U (horizontalLeft U)) := by
  obtain ⟨hp, hx⟩ := hU.mem_edge_pi.1 (vminus_mem_edge hU.imported_isConvexBody Real.pi)
  have hlo := dot_vminus_le_dot hU.isCompact (hU.mem_edge_pi.2
    ⟨capRoof_mem hU.isCompact (horizontalLeft_mem hU.nonempty hU.isCompact), rfl⟩)
  rw [dot_vvec_pi, dot_vvec_pi, neg_le_neg_iff] at hlo
  exact Prod.ext hx (le_antisymm (hx ▸ le_capRoof hU.isCompact hp) hlo)

theorem IsDownwardCap.axis_curvature_zero {U : Set Plane} (hU : IsDownwardCap U) :
    (upperCurvature U {0}).toReal = capRoof U (horizontalRight U) := by
  obtain ⟨hp, -⟩ := mem_edge_zero.1 (vminus_mem_edge hU.imported_isConvexBody 0)
  have h := dot_vminus_le_dot hU.isCompact (mem_edge_zero.2 ⟨hU.baseline_mem
    (capRoof_mem hU.isCompact (horizontalRight_mem hU.nonempty hU.isCompact)), rfl⟩)
  change sigmaAt U 0 = _
  rw [sigmaAt_eq_dot_sub hU.imported_isConvexBody, hU.axis_vplus_zero]
  simp only [dot_vvec_zero] at h ⊢
  linarith [(hU.inStrip hp).1]

theorem IsDownwardCap.axis_curvature_pi {U : Set Plane} (hU : IsDownwardCap U) :
    (upperCurvature U {Real.pi}).toReal = capRoof U (horizontalLeft U) := by
  obtain ⟨hp, -⟩ := hU.mem_edge_pi.1 (vplus_mem_edge hU.imported_isConvexBody Real.pi)
  have h := dot_le_dot_vplus hU.isCompact (hU.mem_edge_pi.2 ⟨hU.baseline_mem
    (capRoof_mem hU.isCompact (horizontalLeft_mem hU.nonempty hU.isCompact)), rfl⟩)
  change sigmaAt U Real.pi = _
  rw [sigmaAt_eq_dot_sub hU.imported_isConvexBody, hU.axis_vminus_pi]
  simp only [dot_vvec_pi] at h ⊢
  linarith [(hU.inStrip hp).1]

theorem IsDownwardCap.sigmaFun_zero {U : Set Plane} (hU : IsDownwardCap U) :
    sigmaFun U 0 = capRoof U (horizontalRight U) := by
  simp [sigmaFun, hU.axis_vplus_zero, dot_vvec_zero]

theorem IsDownwardCap.sigmaFun_leftLim_pi {U : Set Plane} (hU : IsDownwardCap U) :
    Function.leftLim (sigmaFun U) Real.pi =
      (∫ t in (0 : ℝ)..Real.pi, supp U t) - capRoof U (horizontalLeft U) := by
  rw [leftLim_sigmaFun hU.imported_isConvexBody, hU.axis_vminus_pi, dot_vvec_pi]
  ring

theorem IsDownwardCap.upperCurvature_real_Ioc {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) :
    (upperCurvature U).real (Ioc a b) = sigmaFun U b - sigmaFun U a := by
  rw [Measure.real, hU.upperCurvature_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_sigmaFun hU.imported_isConvexBody hab))]

theorem IsDownwardCap.upperCurvature_real_Ioc_zero {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : 0 ≤ t) :
    (upperCurvature U).real (Ioc 0 t) = sigmaFun U t - capRoof U (horizontalRight U) := by
  rw [hU.upperCurvature_real_Ioc ht, hU.sigmaFun_zero]

theorem IsDownwardCap.upperCurvature_real_Ioo_pi {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : t < Real.pi) :
    (upperCurvature U).real (Ioo t Real.pi) =
      (∫ s in (0 : ℝ)..Real.pi, supp U s) - capRoof U (horizontalLeft U) - sigmaFun U t := by
  have hK := hU.imported_isConvexBody
  rw [← hU.sigmaFun_leftLim_pi]
  simp [Measure.real, upperCurvature, sigma, sigmaStieltjes, hK, StieltjesFunction.measure_Ioo,
    (monotone_sigmaFun hK).le_leftLim ht]

end AmbidextrousSofa
