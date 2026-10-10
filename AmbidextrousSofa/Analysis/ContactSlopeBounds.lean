import AmbidextrousSofa.Analysis.ContactGraphSlope
import Mathlib.Analysis.Calculus.Deriv.Slope

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
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hN := hasDerivAt_iff_tendsto_slope_left_right.mp hderiv
  have hfirst := hasDerivAt_iff_tendsto_slope_left_right.mp
    (hasDerivAt_firstWall_spatial U t (attachedCorner U t).1)
  have hsecond := hasDerivAt_iff_tendsto_slope_left_right.mp
    (hasDerivAt_secondWall_spatial U t (attachedCorner U t).1)
  have hfirst_contact : firstWall U t (attachedCorner U t).1 =
      sweptNiche U (Real.pi / 2) (attachedCorner U t).1 :=
    (firstWall_attachedCorner U hs.ne').trans hcontact.symm
  have hsecond_contact : secondWall U t (attachedCorner U t).1 =
      sweptNiche U (Real.pi / 2) (attachedCorner U t).1 :=
    (secondWall_attachedCorner U hc.ne').trans hcontact.symm
  constructor
  · apply le_of_tendsto_of_tendsto hfirst.2 hN.2
    filter_upwards [self_mem_nhdsWithin] with y hy
    change (attachedCorner U t).1 < y at hy
    have hwall : firstWall U t y ≤ sweptNiche U (Real.pi / 2) y := by
      rw [← cornerWall_eq_firstWall_of_corner_le hs hc hy.le]
      exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht
    rw [slope_def_field, slope_def_field, hfirst_contact]
    exact (div_le_div_iff_of_pos_right (sub_pos.mpr hy)).mpr (sub_le_sub_right hwall _)
  · apply le_of_tendsto_of_tendsto hN.1 hsecond.1
    filter_upwards [self_mem_nhdsWithin] with y hy
    change y < (attachedCorner U t).1 at hy
    have hwall : secondWall U t y ≤ sweptNiche U (Real.pi / 2) y := by
      rw [← cornerWall_eq_secondWall_of_le_corner hs hc hy.le]
      exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht
    rw [slope_def_field, slope_def_field, hsecond_contact]
    exact (div_le_div_right_of_neg (sub_neg.mpr hy)).mpr (sub_le_sub_right hwall _)

theorem IsDownwardCap.niche_residual_signs_at_attachedCorner
    {U : Set Plane} (hU : IsDownwardCap U) {t g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    0 ≤ g * Real.sin t + Real.cos t ∧ g * Real.cos t - Real.sin t ≤ 0 := by
  have hbounds := hU.niche_derivative_bounds_at_attachedCorner ht hderiv hcontact
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hfirst := (div_le_iff₀ hs).mp hbounds.1
  have hsecond := (le_div_iff₀ hc).mp hbounds.2
  constructor <;> linarith only [hfirst, hsecond]

/-- The two graph residuals never vanish simultaneously. -/
theorem corner_graph_residual_projection_identity (g t : ℝ) :
    (g * Real.sin t + Real.cos t) * Real.cos t -
      (g * Real.cos t - Real.sin t) * Real.sin t = 1 := by
  calc
    _ = Real.cos t ^ 2 + Real.sin t ^ 2 := by ring
    _ = 1 := Real.cos_sq_add_sin_sq t

theorem corner_graph_first_residual_identity {p q g t : ℝ}
    (hchain : g * (p * Real.cos t - q * Real.sin t) =
      p * Real.sin t + q * Real.cos t) :
    (g * Real.sin t + Real.cos t) * (p * Real.cos t - q * Real.sin t) = p := by
  calc
    _ = (g * (p * Real.cos t - q * Real.sin t)) * Real.sin t +
        Real.cos t * (p * Real.cos t - q * Real.sin t) := by ring
    _ = (p * Real.sin t + q * Real.cos t) * Real.sin t +
        Real.cos t * (p * Real.cos t - q * Real.sin t) := by rw [hchain]
    _ = p * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = p := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem corner_graph_second_residual_identity {p q g t : ℝ}
    (hchain : g * (p * Real.cos t - q * Real.sin t) =
      p * Real.sin t + q * Real.cos t) :
    (g * Real.cos t - Real.sin t) * (p * Real.cos t - q * Real.sin t) = q := by
  calc
    _ = (g * (p * Real.cos t - q * Real.sin t)) * Real.cos t -
        Real.sin t * (p * Real.cos t - q * Real.sin t) := by ring
    _ = (p * Real.sin t + q * Real.cos t) * Real.cos t -
        Real.sin t * (p * Real.cos t - q * Real.sin t) := by rw [hchain]
    _ = q * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = q := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem corner_graph_residual_balance {p q g t : ℝ}
    (hchain : g * (p * Real.cos t - q * Real.sin t) =
      p * Real.sin t + q * Real.cos t) :
    p * (g * Real.cos t - Real.sin t) = q * (g * Real.sin t + Real.cos t) := by
  nlinarith only [hchain]

theorem false_of_corner_graph_residual_balance_of_same_sign {p q g t : ℝ}
    (hfirst : 0 ≤ g * Real.sin t + Real.cos t)
    (hsecond : g * Real.cos t - Real.sin t ≤ 0)
    (hbalance : p * (g * Real.cos t - Real.sin t) =
      q * (g * Real.sin t + Real.cos t))
    (hsame : (0 < p ∧ 0 < q) ∨ (p < 0 ∧ q < 0)) : False := by
  have hF : g * Real.sin t + Real.cos t = 0 := by
    apply le_antisymm ?_ hfirst
    by_contra hnot
    have hFpos : 0 < g * Real.sin t + Real.cos t := lt_of_not_ge hnot
    rcases hsame with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hleft := mul_nonpos_of_nonneg_of_nonpos hp.le hsecond
      have hright := mul_pos hq hFpos
      linarith only [hleft, hright, hbalance]
    · have hleft := mul_nonneg_of_nonpos_of_nonpos hp.le hsecond
      have hright := mul_neg_of_neg_of_pos hq hFpos
      linarith only [hleft, hright, hbalance]
  have hpne : p ≠ 0 := by
    rcases hsame with ⟨hp, _⟩ | ⟨hp, _⟩
    · exact hp.ne'
    · exact hp.ne
  have hG : g * Real.cos t - Real.sin t = 0 := by
    exact (mul_eq_zero.mp (show p * (g * Real.cos t - Real.sin t) = 0 by
      rw [hbalance, hF, mul_zero])).resolve_left hpne
  have hprojection := corner_graph_residual_projection_identity g t
  simp only [hF, hG, zero_mul, sub_self] at hprojection
  exact zero_ne_one hprojection

/-- In the original cap convention the two support momenta are
`-secondCornerVelocity` and `firstCornerVelocity`. A differentiable
core contact cannot belong to either of their equal-sign phases. -/
theorem IsDownwardCap.not_same_sign_momenta_at_attachedCorner_contact
    {U : Set Plane} (hU : IsDownwardCap U) {m K t g : ℝ} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ regularCornerDomain m)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    ¬ ((0 < -secondCornerVelocity U t ∧ 0 < firstCornerVelocity U t) ∨
      (-secondCornerVelocity U t < 0 ∧ firstCornerVelocity U t < 0)) := by
  have hsigns := hU.niche_residual_signs_at_attachedCorner ht.1 hderiv hcontact
  have hchain := hU.niche_derivative_corner_velocity hρ hρ0 hρK heq ht hderiv hcontact
  change g * ((-secondCornerVelocity U t) * Real.cos t -
      firstCornerVelocity U t * Real.sin t) =
    (-secondCornerVelocity U t) * Real.sin t + firstCornerVelocity U t * Real.cos t at hchain
  exact false_of_corner_graph_residual_balance_of_same_sign hsigns.1 hsigns.2
    (corner_graph_residual_balance hchain)

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f

theorem fullTiltedSupportQuarterPair_not_same_sign_at_attachedCorner_contact_after_affine
    {t g : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    ¬ ((0 < p t ∧ 0 < q t) ∨ (p t < 0 ∧ q t < 0)) := by
  have hsigns := hU.isCap.niche_residual_signs_at_attachedCorner ht hderiv hcontact
  have hchain := fullTiltedSupportQuarterPair_niche_attachedCorner_slope_after_affine
    hU hm haffine hρ hρ0 hρK heq ht hmt hderiv hcontact
  exact false_of_corner_graph_residual_balance_of_same_sign hsigns.1 hsigns.2
    (corner_graph_residual_balance hchain)

end ActualPair

end AmbidextrousSofa
