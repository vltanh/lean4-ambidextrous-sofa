module

public import AmbidextrousSofa.Analysis.PartialNeighborShadowing
public import AmbidextrousSofa.Analysis.ShadowCurvature

@[expose] public section

/-!
# Actual proper source shadowing at vanishing mesh

The neighboring support margins are evaluated at rescaled visited
angles. Their limits are the original cap's two corner velocities.
The actual selected atom inequalities keep the half-angle correction,
the middle source mass and every selection error.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem positive_shadow_source_bounds {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0)
    (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    (hmargin : 0 < positiveShadowMargin U (scaleAngle α t.val) δ) :
    innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t)) = ∅ ∧
      (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) ≤
        max (2 * Real.tan (δ / 2) -
          (upperCurvature U {(scaleAngle α t.val : ℝ) + Real.pi / 2}).toReal) 0 := by
  have hm := lt_min_iff.mp hmargin
  have htan : 0 < Real.tan δ := by rw [Real.tan_eq_sin_div_cos]; exact div_pos hs hc
  have hg1 := first_forward_shadow_gap U (scaleAngle α t.val) hs.ne' hh
  have hg2 := first_companion_forward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh
  have hg3 := second_companion_forward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh
  have hg4 := second_mixed_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh
  have hp1 := hm.1
  have hp2 := (lt_min_iff.mp hm.2).1
  have hp3 := (lt_min_iff.mp hm.2).2
  constructor
  · apply first_source_empty_of_forward_separation hU grid t hc hs hminus hplus
    · linarith only [hg1, hp1]
    · have hmul := mul_pos htan hp2
      linarith only [hg2, hmul]
  · apply integral_second_source_le_self_interval hU grid t hc hs hh hab hminus hplus
    · have hmul := mul_pos htan hp1
      linarith only [hg3, hmul]
    · linarith only [hg4, hp3]

theorem negative_shadow_source_bounds {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0)
    (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    (hmargin : 0 < negativeShadowMargin U (scaleAngle α t.val) δ) :
    innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t)) = ∅ ∧
      (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inl t)) x) ≤
        max (2 * Real.tan (δ / 2) - (upperCurvature U {((scaleAngle α t.val : QuarterAngle) : ℝ)}).toReal) 0 := by
  have hm := lt_min_iff.mp hmargin
  have htan : 0 < Real.tan δ := by rw [Real.tan_eq_sin_div_cos]; exact div_pos hs hc
  have hg1 := second_backward_shadow_gap U (scaleAngle α t.val) hs.ne' hh
  have hg2 := second_companion_backward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh
  have hg3 := first_companion_backward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh
  have hg4 := first_mixed_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh
  have hp1 := hm.1
  have hp2 := (lt_min_iff.mp hm.2).1
  have hp3 := (lt_min_iff.mp hm.2).2
  constructor
  · apply second_source_empty_of_backward_separation hU grid t hc hs hminus hplus
    · linarith only [hg1, hp2]
    · have hmul := mul_pos htan hp1
      linarith only [hg2, hmul]
  · apply integral_first_source_le_self_interval hU grid t hc hs hh hab hminus hplus
    · have hmul := mul_pos htan hp2
      linarith only [hg3, hmul]
    · linarith only [hg4, hp3]

theorem mesh_half_tan_nonneg (α : TerminalAngle) (n : ℕ) :
    0 ≤ Real.tan (mesh α n / 2) := by
  apply nonneg_of_mul_nonneg_left _ (mesh_sin_pos α n)
  rw [MovingSofaOptimality.tan_half_mul_sin (mesh_half_cos_ne α n)]
  linarith only [Real.cos_le_one (mesh α n)]

theorem IsSelectedPolygon.positive_shadow_atoms {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (t : InteriorPoint (dyadic level))
    (hmargin : 0 < positiveShadowMargin U (scaleAngle α t.val) (mesh α level)) :
    (upperCurvature U {((scaleAngle α t.val : QuarterAngle) : ℝ)}).toReal ≤
        middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) (Sum.inl t)) +
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) (Sum.inl t)) ∧
      (upperCurvature U {(scaleAngle α t.val : ℝ) + Real.pi / 2}).toReal ≤
        Real.tan (mesh α level / 2) +
        middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) (Sum.inr t)) +
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) (Sum.inr t)) := by
  obtain ⟨hm, hp⟩ := dyadic_neighbors α level t
  have hab : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth
    linarith only [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]
  have hsource := positive_shadow_source_bounds (hαL := hαL) hU.isCap (dyadic level) t
    (mesh_cos_pos α level) (mesh_sin_pos α level) (mesh_half_cos_ne α level) hab hm hp hmargin
  exact ⟨hU.curvature_atom_le_error_of_source_empty hc _ hsource.1,
    hU.curvature_atom_le_half_of_self_interval hc _ (mesh_half_tan_nonneg α level) hsource.2⟩

theorem IsSelectedPolygon.negative_shadow_atoms {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (t : InteriorPoint (dyadic level))
    (hmargin : 0 < negativeShadowMargin U (scaleAngle α t.val) (mesh α level)) :
    (upperCurvature U {(scaleAngle α t.val : ℝ) + Real.pi / 2}).toReal ≤
        middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) (Sum.inr t)) +
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) (Sum.inr t)) ∧
      (upperCurvature U {((scaleAngle α t.val : QuarterAngle) : ℝ)}).toReal ≤ Real.tan (mesh α level / 2) +
        middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) (Sum.inl t)) +
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) (Sum.inl t)) := by
  obtain ⟨hm, hp⟩ := dyadic_neighbors α level t
  have hab : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth
    linarith only [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]
  have hsource := negative_shadow_source_bounds (hαL := hαL) hU.isCap (dyadic level) t
    (mesh_cos_pos α level) (mesh_sin_pos α level) (mesh_half_cos_ne α level) hab hm hp hmargin
  exact ⟨hU.curvature_atom_le_error_of_source_empty hc _ hsource.1,
    hU.curvature_atom_le_half_of_self_interval hc _ (mesh_half_tan_nonneg α level) hsource.2⟩

theorem sourceQuarterAngle_scaledSource (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : AngularGrid.SourceIndex grid) :
    sourceQuarterAngle (fullAngle α grid (scaledSource α grid j)) =
      Sum.elim (fun t : InteriorPoint grid => (scaleAngle α t.val : ℝ))
        (fun t : InteriorPoint grid => (scaleAngle α t.val : ℝ)) j := by
  cases j with
  | inl t =>
    exact AngularGrid.sourceQuarterAngle_fullAngle (outerGrid α grid)
      (Sum.inl (scaledInterior α grid t))
  | inr t =>
    exact AngularGrid.sourceQuarterAngle_fullAngle (outerGrid α grid)
      (Sum.inr (scaledInterior α grid t))

theorem IsSelectedPolygon.curvature_scaled_atom_le_shadow {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (positive : Bool) (j : AngularGrid.SourceIndex (dyadic level))
    (hmargin : 0 < sameSignShadowMargin positive U
      (sourceQuarterAngle (fullAngle α (dyadic level) (scaledSource α (dyadic level) j)))
        (mesh α level)) :
    (upperCurvature U {fullAngle α (dyadic level) (scaledSource α (dyadic level) j)}).toReal ≤
      2 * sameSignCoefficient positive
          (fullAngle α (dyadic level) (scaledSource α (dyadic level) j)) * Real.tan (mesh α level / 2) +
        middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) j) +
          selectionDefect target U α level coefficient (scaledSource α (dyadic level) j) := by
  cases positive with
  | false =>
    cases j with
    | inl t =>
      have hm : 0 < negativeShadowMargin U (scaleAngle α t.val) (mesh α level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_scaledSource] using hmargin
      have h := (hU.negative_shadow_atoms hc t hm).2
      have ht := (scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t)).2.trans hαL
      have hval : (((scaledInterior α (dyadic level) t).val : QuarterAngle) : ℝ) =
          (scaleAngle α t.val : ℝ) := rfl
      simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, hval, ht] using h
    | inr t =>
      have hm : 0 < negativeShadowMargin U (scaleAngle α t.val) (mesh α level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_scaledSource] using hmargin
      have ht : ¬ (scaleAngle α t.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
        linarith only [(scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t)).1]
      have ht' : ¬ (scaleAngle α t.val : ℝ) < 0 := by
        linarith only [(scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t)).1]
      have hval : (((scaledInterior α (dyadic level) t).val : QuarterAngle) : ℝ) =
          (scaleAngle α t.val : ℝ) := rfl
      have h := (hU.negative_shadow_atoms hc t hm).1
      simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, hval, ht, ht'] using h
  | true =>
    cases j with
    | inl t =>
      have hm : 0 < positiveShadowMargin U (scaleAngle α t.val) (mesh α level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_scaledSource] using hmargin
      have h := (hU.positive_shadow_atoms hc t hm).1
      have ht := (scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t)).2.trans hαL
      have hval : (((scaledInterior α (dyadic level) t).val : QuarterAngle) : ℝ) =
          (scaleAngle α t.val : ℝ) := rfl
      simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, hval, ht] using h
    | inr t =>
      have hm : 0 < positiveShadowMargin U (scaleAngle α t.val) (mesh α level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_scaledSource] using hmargin
      have ht : ¬ (scaleAngle α t.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
        linarith only [(scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t)).1]
      have ht' : ¬ (scaleAngle α t.val : ℝ) < 0 := by
        linarith only [(scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t)).1]
      have hval : (((scaledInterior α (dyadic level) t).val : QuarterAngle) : ℝ) =
          (scaleAngle α t.val : ℝ) := rfl
      have h := (hU.positive_shadow_atoms hc t hm).2
      simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, hval, ht, ht'] using h

theorem eventually_sameSignShadowMargin_pos
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B) (positive : Bool)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) {t : ℝ}
    (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt K (sourceQuarterAngle t) = 0)
    (htcomp : MovingSofaOptimality.sigmaAt K (sourceQuarterAngle t + Real.pi / 2) = 0)
    (hmargin : 0 < sameSignVelocityMargin positive K (sourceQuarterAngle t)) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : AngularGrid.SourceIndex (dyadic (level n)),
      |fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j) - t| < δ →
        0 < sameSignShadowMargin positive (U n)
          (sourceQuarterAngle (fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j)))
            (mesh α (level n)) := by
  apply eventually_uniform_pos_of_moving_tendsto
    (fun n j => fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j))
    (fun n j => sameSignShadowMargin positive (U n)
      (sourceQuarterAngle (fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j)))
        (mesh α (level n))) hmargin
  intro ns hns j hangle
  have hsub : CapHausdorffTendsto (fun n => U (ns n)) K := h.comp hns
  exact hsub.sameSignShadowMargin_tendsto (fun n => hU (ns n)) hK hB
    (fun n => hbox (ns n)) positive (sourceQuarterAngle_tendsto hangle htop)
    ((mesh_tendsto α).comp (hlevel.comp hns)) (fun n => mesh_sin_pos α (level (ns n)))
    (fun n => (mesh_cos_pos α (level (ns n))).le) ht htcomp

theorem tan_half_div_mesh_tendsto (α : TerminalAngle)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => Real.tan (mesh α (level n) / 2) / mesh α (level n)) atTop (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun n => mesh α (level n) / 2) atTop (𝓝 0) := by
    simpa only [zero_div, Function.comp_apply] using ((mesh_tendsto α).comp hlevel).div_const 2
  have hratio := tan_div_self_tendsto hhalf
    (fun n => div_pos (mesh_pos α (level n)) (by norm_num))
  simpa only [div_div, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hratio.div_const 2

theorem eventually_shadow_atoms_le
    {target : Set Plane} {U : ℕ → Set Plane} {B : Set Plane}
    {boxLeft boxRight : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (positive : Bool) {t ε : ℝ} (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt target (sourceQuarterAngle t) = 0)
    (htcomp : MovingSofaOptimality.sigmaAt target (sourceQuarterAngle t + Real.pi / 2) = 0)
    (hmargin : 0 < sameSignVelocityMargin positive target (sourceQuarterAngle t))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : AngularGrid.SourceIndex (dyadic (level n)),
      |fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j) - t| < δ →
        (upperCurvature (U n)
          {fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j)}).toReal ≤
          (sameSignCoefficient positive t + ε) * mesh α (level n) +
            middleOuterMass (U n) α (dyadic (level n)) (scaledSource α (dyadic (level n)) j) +
              selectionDefect target (U n) α (level n) (coefficient n)
                (scaledSource α (dyadic (level n)) j) := by
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_sameSignShadowMargin_pos (α := α) hHausdorff
    (fun n => (hU n).isCap) hTarget hB hbox positive hlevel htop ht htcomp hmargin
  let gap := if t < Real.pi / 2 then Real.pi / 2 - t else t - Real.pi / 2
  have hgap : 0 < gap := by
    dsimp only [gap]
    split_ifs with hlt
    · exact sub_pos.mpr hlt
    · exact sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt hlt) htop.symm)
  let δ := min δ₀ gap
  have hδ : 0 < δ := lt_min hδ₀ hgap
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδgap : δ ≤ gap := min_le_right _ _
  have hsame : ∀ s : ℝ, |s - t| < δ →
      sameSignCoefficient positive s = sameSignCoefficient positive t := by
    intro s hs
    have hnear := abs_lt.mp hs
    by_cases ht' : t < Real.pi / 2
    · have hgap' : gap = Real.pi / 2 - t := if_pos ht'
      have hs' : s < Real.pi / 2 := by linarith only [hnear.2, hδgap, hgap']
      simp only [sameSignCoefficient, if_pos ht', if_pos hs']
    · have hgap' : gap = t - Real.pi / 2 := if_neg ht'
      have hs' : ¬ s < Real.pi / 2 := by linarith only [hnear.1, hδgap, hgap']
      simp only [sameSignCoefficient, if_neg ht', if_neg hs']
  have hratio := (tan_half_div_mesh_tendsto α hlevel).eventually_lt_const
    (show (1 / 2 : ℝ) < 1 / 2 + ε by linarith only [hε])
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hfinite, hratio] with n hn hratio
  intro j hj
  have hm := hn j (hj.trans_le hδ₀')
  have hatom := (hU n).curvature_scaled_atom_le_shadow (hc n) positive j hm
  rw [hsame _ hj] at hatom
  have htan : Real.tan (mesh α (level n) / 2) ≤ (1 / 2 + ε) * mesh α (level n) :=
    (div_le_iff₀ (mesh_pos α (level n))).mp hratio.le
  have hC0 := sameSignCoefficient_nonneg positive t
  have hC1 := sameSignCoefficient_le_half positive t
  have hweight := mul_le_mul_of_nonneg_right hC1 hε.le
  have hfactor : 2 * sameSignCoefficient positive t * (1 / 2 + ε) ≤
      sameSignCoefficient positive t + ε := by nlinarith only [hweight]
  have hscaled := mul_le_mul_of_nonneg_left htan
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0)
  have hfinal := mul_le_mul_of_nonneg_right hfactor (mesh_pos α (level n)).le
  nlinarith only [hatom, hscaled, hfinal]

end PartialGrid
end AmbidextrousSofa
