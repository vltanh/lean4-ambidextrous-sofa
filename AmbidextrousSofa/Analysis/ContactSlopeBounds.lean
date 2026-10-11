module

public import AmbidextrousSofa.Analysis.ContactGraphSlope
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Corner slope bounds and exclusion of contacts in the equal-sign phases

To the right of an attached corner, its first wall is the lower wall;
to the left, its second wall is the lower wall. The actual niche lies
above both of these one-sided pieces. At a differentiable contact this
bounds its derivative between the two wall slopes. The corner chain
rule then prevents contact when both support momenta have the same
strict sign. The exact two residual identities are also retained for
transport of the common core measure.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.niche_derivative_bounds_at_attachedCorner
    {U : Set Plane} (hU : IsDownwardCap U) {t g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    -Real.cos t / Real.sin t ≤ g ∧ g ≤ Real.sin t / Real.cos t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hN := hasDerivAt_iff_tendsto_slope_left_right.mp hderiv
  have hwall (y : ℝ) :=
    cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht
  constructor
  · refine le_of_tendsto_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp
      (hasDerivAt_firstWall_spatial U t _)).2 hN.2 ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : _ < y)
    rw [slope_def_field, slope_def_field, firstWall_attachedCorner U hs.ne', ← hcontact]
    exact (div_le_div_iff_of_pos_right (sub_pos.mpr hy)).mpr (sub_le_sub_right
      ((cornerWall_eq_firstWall_of_corner_le hs hc hy.le).symm.trans_le (hwall y)) _)
  · refine le_of_tendsto_of_tendsto hN.1 (hasDerivAt_iff_tendsto_slope_left_right.mp
      (hasDerivAt_secondWall_spatial U t _)).1 ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < _)
    rw [slope_def_field, slope_def_field, secondWall_attachedCorner U hc.ne', ← hcontact]
    exact (div_le_div_right_of_neg (sub_neg.mpr hy)).mpr (sub_le_sub_right
      ((cornerWall_eq_secondWall_of_le_corner hs hc hy.le).symm.trans_le (hwall y)) _)

theorem corner_graph_first_residual_identity {p q g t : ℝ}
    (hchain : g * (p * Real.cos t - q * Real.sin t) =
      p * Real.sin t + q * Real.cos t) :
    (g * Real.sin t + Real.cos t) * (p * Real.cos t - q * Real.sin t) = p := by
  linear_combination Real.sin t * hchain + p * Real.sin_sq_add_cos_sq t

theorem corner_graph_second_residual_identity {p q g t : ℝ}
    (hchain : g * (p * Real.cos t - q * Real.sin t) =
      p * Real.sin t + q * Real.cos t) :
    (g * Real.cos t - Real.sin t) * (p * Real.cos t - q * Real.sin t) = q := by
  linear_combination Real.cos t * hchain + q * Real.sin_sq_add_cos_sq t

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_not_same_sign_at_attachedCorner_contact_after_affine
    {t g : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    ¬ ((0 < p t ∧ 0 < q t) ∨ (p t < 0 ∧ q t < 0)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  obtain ⟨h1, h2⟩ := hU.isCap.niche_derivative_bounds_at_attachedCorner ht hderiv hcontact
  -- the two graph residuals have opposite weak signs and never vanish simultaneously
  have hF : 0 ≤ g * Real.sin t + Real.cos t := by linarith [(div_le_iff₀ hs).mp h1]
  have hG : g * Real.cos t - Real.sin t ≤ 0 := by linarith [(le_div_iff₀ hc).mp h2]
  have hone : (g * Real.sin t + Real.cos t) * Real.cos t -
      (g * Real.cos t - Real.sin t) * Real.sin t = 1 := by
    linear_combination Real.cos_sq_add_sin_sq t
  have hbalance : p t * (g * Real.cos t - Real.sin t) = q t * (g * Real.sin t + Real.cos t) := by
    linear_combination fullTiltedSupportQuarterPair_niche_attachedCorner_slope_after_affine
      hU hm haffine hρ hρ0 hρK heq ht hmt hderiv hcontact
  rintro (⟨hp, hq⟩ | ⟨hp, hq⟩) <;>
  · have hF0 : g * Real.sin t + Real.cos t = 0 := by nlinarith only [hF, hG, hbalance, hp, hq]
    have hG0 : g * Real.cos t - Real.sin t = 0 := by nlinarith only [hF, hG, hbalance, hp, hq]
    simp [hF0, hG0] at hone

end ActualPair

end AmbidextrousSofa
