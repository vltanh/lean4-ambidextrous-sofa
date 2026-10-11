module

public import AmbidextrousSofa.Analysis.HorizontalTopFacet
public import AmbidextrousSofa.Analysis.TangencyLoci

@[expose] public section

/-!
# Actual horizontal top faces and one-sided tangency endpoints

The first inner tangency is the actual right supporting point minus
its unit normal; the second is the same construction in the companion
direction. The true top facet therefore has different left and right
supporting endpoints. One-sided limits below keep that facet and the
two axis faces, rather than replacing the support derivative at an atom.
-/

noncomputable section

open Set Filter MeasureTheory MovingSofaOptimality
open scoped Topology

namespace AmbidextrousSofa

theorem firstTangency_eq_vplus_sub_unitNormal (U : Set Plane) (t : ℝ) :
    firstTangency U t = MovingSofaOptimality.vplus U t - unitNormal t := by
  conv_rhs => rw [eq_dot_uvec_smul_add (vplus U t) t, dot_vplus_uvec]
  ext <;> simp [firstTangency_fst_eq_support, firstTangency_snd_eq_support, supportTangent,
    angleSupport_eq_imported_supp, unitNormal] <;> ring

theorem secondTangency_eq_vplus_sub_companionNormal (U : Set Plane) (t : ℝ) :
    secondTangency U t = vplus U (t + Real.pi / 2) - companionNormal t := by
  rw [companionNormal_eq_unitNormal, ← firstTangency_eq_vplus_sub_unitNormal]
  ext <;> simp only [firstTangency_fst_eq_support, firstTangency_snd_eq_support,
    secondTangency_fst_eq_support, secondTangency_snd_eq_support, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two] <;> ring

private theorem mem_edge_pi_div_two {U : Set Plane} (hheight : capHeight U = 1) {p : Plane} :
    p ∈ edge U (Real.pi / 2) ↔ p ∈ U ∧ p.2 = 1 := by
  simp [edge, suppLine, line, dot, imported_supp_pi_div_two, hheight]

theorem IsDownwardCap.firstTangency_tendsto_zero_right
    {U : Set Plane} (hU : IsDownwardCap U) :
    Tendsto (firstTangency U) (𝓝[>] (0 : ℝ))
      (𝓝 (horizontalRight U - 1, capRoof U (horizontalRight U))) := by
  simpa [funext (firstTangency_eq_vplus_sub_unitNormal U), hU.axis_vplus_zero, unitNormal] using
    (tendsto_vplus_right hU.imported_isConvexBody 0).sub
      continuous_unitNormal.continuousWithinAt.tendsto

theorem IsDownwardCap.secondTangency_tendsto_pi_div_two_left
    {U : Set Plane} (hU : IsDownwardCap U) :
    Tendsto (secondTangency U) (𝓝[<] (Real.pi / 2))
      (𝓝 (horizontalLeft U + 1, capRoof U (horizontalLeft U))) := by
  have hp := (tendsto_vplus_left hU.imported_isConvexBody (Real.pi / 2 + Real.pi / 2)).comp
    map_add_right_nhdsLT.le
  simpa [funext (secondTangency_eq_vplus_sub_companionNormal U), hU.axis_vminus_pi,
    companionNormal] using hp.sub continuous_companionNormal.continuousWithinAt.tendsto

/-- One-sided limits of the two corner velocities, from those of the supporting vertex at the
angle and at the companion angle. -/
private theorem tendsto_cornerVelocities {U : Set Plane} (hU : IsCompact U) {l : Filter ℝ}
    {a : ℝ} {P Q : Plane} (hl : l ≤ 𝓝 a) (hP : Tendsto (vplus U) l (𝓝 P))
    (hQ : Tendsto (fun t => vplus U (t + Real.pi / 2)) l (𝓝 Q)) :
    Tendsto (fun t => (firstCornerVelocity U t, secondCornerVelocity U t)) l
      (𝓝 (supp U a + dot Q (vvec (a + Real.pi / 2)) - 1,
        supp U (a + Real.pi / 2) - dot P (vvec a) - 1)) := by
  have := continuous_supp hU
  have hc : Continuous fun x : ℝ × Plane × Plane =>
      (supp U x.1 + dot x.2.2 (vvec (x.1 + Real.pi / 2)) - 1,
        supp U (x.1 + Real.pi / 2) - dot x.2.1 (vvec x.1) - 1) := by
    simp only [dot, vvec]
    fun_prop
  exact ((hc.tendsto (a, P, Q)).comp ((tendsto_id.mono_left hl).prodMk_nhds (hP.prodMk_nhds hQ)) :)

section FullMaximum

variable {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
  (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
include hU hheight hmiddle

theorem IsFullCapMaximizer.top_vplus_pi_div_two :
    MovingSofaOptimality.vplus U (Real.pi / 2) = (horizontalLeft U + capWidth U / 4, 1) := by
  obtain ⟨hp, hy⟩ :=
    (mem_edge_pi_div_two hheight).1 (vplus_mem_edge hU.isCap.imported_isConvexBody _)
  obtain ⟨hl, -, hlr⟩ := hU.isCap.middleChord_endpoints (by linarith [hU.two_lt_width])
  have h := dot_le_dot_vplus hU.isCap.isCompact ((mem_edge_pi_div_two hheight).2
    ⟨hmiddle _ ⟨le_rfl, hlr.le⟩ ▸ capRoof_mem hU.isCap.isCompact hl, rfl⟩)
  have hJ : horizontalLeft U + capWidth U / 4 ≤ _ ∧ _ :=
    hU.top_abscissa_mem_middle hheight hmiddle hp hy
  simp [dot, vvec] at h
  exact Prod.ext (by linarith [hJ.1]) hy

theorem IsFullCapMaximizer.top_vminus_pi_div_two :
    MovingSofaOptimality.vminus U (Real.pi / 2) = (horizontalRight U - capWidth U / 4, 1) := by
  obtain ⟨hp, hy⟩ :=
    (mem_edge_pi_div_two hheight).1 (vminus_mem_edge hU.isCap.imported_isConvexBody _)
  obtain ⟨-, hr, hlr⟩ := hU.isCap.middleChord_endpoints (by linarith [hU.two_lt_width])
  have h := dot_vminus_le_dot hU.isCap.isCompact ((mem_edge_pi_div_two hheight).2
    ⟨hmiddle _ ⟨hlr.le, le_rfl⟩ ▸ capRoof_mem hU.isCap.isCompact hr, rfl⟩)
  have hJ : _ ∧ _ ≤ horizontalRight U - capWidth U / 4 :=
    hU.top_abscissa_mem_middle hheight hmiddle hp hy
  simp [dot, vvec] at h
  exact Prod.ext (by linarith [hJ.2]) hy

theorem IsFullCapMaximizer.secondTangency_tendsto_zero_right :
    Tendsto (secondTangency U) (𝓝[>] (0 : ℝ)) (𝓝 (horizontalLeft U + capWidth U / 4, 0)) := by
  have hp := (tendsto_vplus_right hU.isCap.imported_isConvexBody (0 + Real.pi / 2)).comp
    map_add_right_nhdsGT.le
  simpa [funext (secondTangency_eq_vplus_sub_companionNormal U),
    hU.top_vplus_pi_div_two hheight hmiddle, companionNormal] using
    hp.sub continuous_companionNormal.continuousWithinAt.tendsto

theorem IsFullCapMaximizer.firstTangency_tendsto_pi_div_two_left :
    Tendsto (firstTangency U) (𝓝[<] (Real.pi / 2)) (𝓝 (horizontalRight U - capWidth U / 4, 0)) := by
  simpa [funext (firstTangency_eq_vplus_sub_unitNormal U),
    hU.top_vminus_pi_div_two hheight hmiddle, unitNormal] using
    (tendsto_vplus_left hU.isCap.imported_isConvexBody (Real.pi / 2)).sub
      continuous_unitNormal.continuousWithinAt.tendsto

theorem IsFullCapMaximizer.cornerVelocities_tendsto_zero_right :
    Tendsto (fun t => (firstCornerVelocity U t, secondCornerVelocity U t)) (𝓝[>] (0 : ℝ))
      (𝓝 (horizontalRight U - 1 - (horizontalLeft U + capWidth U / 4),
        -capRoof U (horizontalRight U))) := by
  have h := tendsto_cornerVelocities hU.isCap.isCompact nhdsWithin_le_nhds
    (tendsto_vplus_right hU.isCap.imported_isConvexBody 0)
    ((tendsto_vplus_right hU.isCap.imported_isConvexBody (0 + Real.pi / 2)).comp
      map_add_right_nhdsGT.le)
  rw [zero_add, hU.isCap.axis_vplus_zero, hU.top_vplus_pi_div_two hheight hmiddle,
    imported_supp_zero, imported_supp_pi_div_two, hheight] at h
  convert h using 3 <;> simp [dot, vvec]
  ring

theorem IsFullCapMaximizer.cornerVelocities_tendsto_pi_div_two_left :
    Tendsto (fun t => (firstCornerVelocity U t, secondCornerVelocity U t)) (𝓝[<] (Real.pi / 2))
      (𝓝 (-capRoof U (horizontalLeft U),
        horizontalRight U - capWidth U / 4 - horizontalLeft U - 1)) := by
  have h := tendsto_cornerVelocities hU.isCap.isCompact nhdsWithin_le_nhds
    (tendsto_vplus_left hU.isCap.imported_isConvexBody (Real.pi / 2))
    ((tendsto_vplus_left hU.isCap.imported_isConvexBody (Real.pi / 2 + Real.pi / 2)).comp
      map_add_right_nhdsLT.le)
  rw [add_halves, hU.isCap.axis_vminus_pi, hU.top_vminus_pi_div_two hheight hmiddle,
    hU.isCap.imported_supp_pi, imported_supp_pi_div_two, hheight] at h
  convert h using 3 <;> simp [dot, vvec]
  ring

end FullMaximum

end AmbidextrousSofa
