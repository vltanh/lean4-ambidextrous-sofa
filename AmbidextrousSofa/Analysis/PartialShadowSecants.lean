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
  obtain ⟨hp1, hp2, hp3⟩ := (lt_min_iff.mp hmargin).imp_right lt_min_iff.mp
  have htan : 0 < Real.tan δ := by rw [Real.tan_eq_sin_div_cos]; exact div_pos hs hc
  refine ⟨first_source_empty_of_forward_separation hU grid t hc hs hminus hplus ?_ ?_,
    integral_second_source_le_self_interval hU grid t hc hs hh hab hminus hplus ?_ ?_⟩
  · linarith [first_forward_shadow_gap U (scaleAngle α t.val) hs.ne' hh]
  · linarith [first_companion_forward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh,
      mul_pos htan hp2]
  · linarith [second_companion_forward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh,
      mul_pos htan hp1]
  · linarith [second_mixed_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh]

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
  obtain ⟨hp1, hp2, hp3⟩ := (lt_min_iff.mp hmargin).imp_right lt_min_iff.mp
  have htan : 0 < Real.tan δ := by rw [Real.tan_eq_sin_div_cos]; exact div_pos hs hc
  refine ⟨second_source_empty_of_backward_separation hU grid t hc hs hminus hplus ?_ ?_,
    integral_first_source_le_self_interval hU grid t hc hs hh hab hminus hplus ?_ ?_⟩
  · linarith [second_backward_shadow_gap U (scaleAngle α t.val) hs.ne' hh]
  · linarith [second_companion_backward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh,
      mul_pos htan hp1]
  · linarith [first_companion_backward_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh,
      mul_pos htan hp2]
  · linarith [first_mixed_shadow_gap U (scaleAngle α t.val) hc.ne' hs.ne' hh]

theorem mesh_half_tan_nonneg (α : TerminalAngle) (n : ℕ) :
    0 ≤ Real.tan (mesh α n / 2) := by
  apply nonneg_of_mul_nonneg_left _ (mesh_sin_pos α n)
  rw [MovingSofaOptimality.tan_half_mul_sin (mesh_half_cos_ne α n)]
  linarith [Real.cos_le_one (mesh α n)]

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
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) (Sum.inr t)) :=
  have h := positive_shadow_source_bounds (hαL := hαL) hU.isCap (dyadic level) t
    (mesh_cos_pos α level) (mesh_sin_pos α level) (mesh_half_cos_ne α level)
    hU.isCap.quarter_le (dyadic_neighbors α level t).1 (dyadic_neighbors α level t).2 hmargin
  ⟨hU.curvature_atom_le_error_of_source_empty hc _ h.1,
    hU.curvature_atom_le_half_of_self_interval hc _ (mesh_half_tan_nonneg α level) h.2⟩

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
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) (Sum.inl t)) :=
  have h := negative_shadow_source_bounds (hαL := hαL) hU.isCap (dyadic level) t
    (mesh_cos_pos α level) (mesh_sin_pos α level) (mesh_half_cos_ne α level)
    hU.isCap.quarter_le (dyadic_neighbors α level t).1 (dyadic_neighbors α level t).2 hmargin
  ⟨hU.curvature_atom_le_error_of_source_empty hc _ h.1,
    hU.curvature_atom_le_half_of_self_interval hc _ (mesh_half_tan_nonneg α level) h.2⟩

theorem sourceQuarterAngle_scaledSource (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : AngularGrid.SourceIndex grid) :
    sourceQuarterAngle (fullAngle α grid (scaledSource α grid j)) =
      Sum.elim (fun t : InteriorPoint grid => (scaleAngle α t.val : ℝ))
        (fun t : InteriorPoint grid => (scaleAngle α t.val : ℝ)) j := by
  cases j <;> exact AngularGrid.sourceQuarterAngle_fullAngle _ _

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
  rcases j with t | t <;> have ht := scaleAngle_mem_open α (interiorPoint_mem (dyadic level) t) <;>
    cases positive <;>
    simp only [sameSignShadowMargin, sourceQuarterAngle_scaledSource, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte] at hmargin
  · simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior,
      ht.2.trans hαL] using (hU.negative_shadow_atoms hc t hmargin).2
  · simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior,
      ht.2.trans hαL] using (hU.positive_shadow_atoms hc t hmargin).1
  · simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior,
      ht.1.not_gt] using (hU.negative_shadow_atoms hc t hmargin).1
  · simpa [sameSignCoefficient, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior,
      ht.1.not_gt] using (hU.positive_shadow_atoms hc t hmargin).2

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
            (mesh α (level n)) :=
  eventually_uniform_pos_of_moving_tendsto _ _ hmargin fun ns hns _ hangle =>
    CapHausdorffTendsto.sameSignShadowMargin_tendsto (h.comp hns) (fun n => hU (ns n)) hK hB
      (fun n => hbox (ns n)) positive (sourceQuarterAngle_tendsto hangle htop)
      ((mesh_tendsto α).comp (hlevel.comp hns)) (fun _ => mesh_sin_pos α _)
      (fun _ => (mesh_cos_pos α _).le) ht htcomp

theorem tan_half_div_mesh_tendsto (α : TerminalAngle)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => Real.tan (mesh α (level n) / 2) / mesh α (level n)) atTop (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun n => mesh α (level n) / 2) atTop (𝓝 0) := by
    simpa using ((mesh_tendsto α).comp hlevel).div_const 2
  simpa only [div_div, div_mul_cancel₀ _ (two_ne_zero' ℝ)] using
    (tan_div_self_tendsto hhalf fun n => half_pos (mesh_pos α (level n))).div_const 2

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
  -- Within `|t - π / 2|` of `t`, the coefficient does not change.
  have hsame (s : ℝ) (hs : |s - t| < |t - Real.pi / 2|) :
      sameSignCoefficient positive s = sameSignCoefficient positive t := by
    obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
    have hiff : s < Real.pi / 2 ↔ t < Real.pi / 2 := by
      rcases abs_cases (t - Real.pi / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> constructor <;> intro <;> linarith
    simp only [sameSignCoefficient, hiff]
  refine ⟨min δ₀ |t - Real.pi / 2|, lt_min hδ₀ (abs_pos.2 (sub_ne_zero.2 htop)), ?_⟩
  filter_upwards [hfinite, (tan_half_div_mesh_tendsto α hlevel).eventually_lt_const
    (by linarith : (1 / 2 : ℝ) < 1 / 2 + ε)] with n hn hratio j hj
  have hatom := (hU n).curvature_scaled_atom_le_shadow (hc n) positive j
    (hn j (hj.trans_le (min_le_left _ _)))
  rw [hsame _ (hj.trans_le (min_le_right _ _))] at hatom
  have hmesh := mesh_pos α (level n)
  linarith [mul_le_mul_of_nonneg_left ((div_le_iff₀ hmesh).mp hratio.le)
      (sameSignCoefficient_nonneg positive t),
    mul_le_mul_of_nonneg_right (sameSignCoefficient_le_half positive t) (mul_pos hε hmesh).le]

end PartialGrid
end AmbidextrousSofa
