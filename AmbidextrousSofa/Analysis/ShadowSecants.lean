module

public import AmbidextrousSofa.Analysis.NeighborShadowing
public import AmbidextrousSofa.Analysis.SourceVelocity

@[expose] public section

/-!
# Shrinking secants give strict source shadowing

The margins below are expressions in the actual neighboring supports.
Their positive limits are the strict signs of the two corner velocities.
The half-angle corrections are kept exactly at finite mesh. Consequently
the resulting empty-source and self-interval conclusions apply to the
literal finite niche, before any limiting density is introduced.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

theorem firstLo_eq_secant_sub_tan {f fp δ : ℝ}
    (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    firstLo f fp δ = (fp - f * Real.cos δ) / Real.sin δ - Real.tan (δ / 2) := by
  have hhalf := MovingSofaOptimality.tan_half_mul_sin hh
  unfold firstLo
  rw [div_eq_iff hs, sub_mul ((fp - f * Real.cos δ) / Real.sin δ), div_mul_cancel₀ _ hs, hhalf]
  ring

theorem firstHi_eq_secant_add_tan {f fm δ : ℝ}
    (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    firstHi f fm δ = (f * Real.cos δ - fm) / Real.sin δ + Real.tan (δ / 2) := by
  have hhalf := MovingSofaOptimality.tan_half_mul_sin hh
  unfold firstHi
  rw [div_eq_iff hs, add_mul, div_mul_cancel₀ _ hs, hhalf]
  ring

theorem companionPlus_sub_eq_secant {f g gp δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionPlus f gp δ - (g - 1) = Real.tan δ *
      (f + (gp - g * Real.cos δ) / Real.sin δ - 1 - Real.tan (δ / 2)) := by
  have hhalf := MovingSofaOptimality.tan_half_mul_sin hh
  have htan : Real.tan δ * Real.cos δ = Real.sin δ := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hc]
  have hsec : Real.sin δ * ((gp - g * Real.cos δ) / Real.sin δ) =
      gp - g * Real.cos δ := by rw [mul_div_cancel₀ _ hs]
  apply mul_right_cancel₀ hc
  calc
    (companionPlus f gp δ - (g - 1)) * Real.cos δ =
        gp - 1 + (f - 1) * Real.sin δ - (g - 1) * Real.cos δ := by
      rw [sub_mul, companionPlus, div_mul_cancel₀ _ hc]
    _ = Real.sin δ *
        (f + (gp - g * Real.cos δ) / Real.sin δ - 1 - Real.tan (δ / 2)) := by
      nlinarith [hhalf, hsec]
    _ = (Real.tan δ *
        (f + (gp - g * Real.cos δ) / Real.sin δ - 1 - Real.tan (δ / 2))) * Real.cos δ := by
      rw [← htan]
      ring

theorem companionMinus_sub_eq_secant {f g gm δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionMinus f gm δ - (g - 1) = -Real.tan δ *
      (f + (g * Real.cos δ - gm) / Real.sin δ - 1 + Real.tan (δ / 2)) := by
  have hhalf := MovingSofaOptimality.tan_half_mul_sin hh
  have htan : Real.tan δ * Real.cos δ = Real.sin δ := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hc]
  have hsec : Real.sin δ * ((g * Real.cos δ - gm) / Real.sin δ) =
      g * Real.cos δ - gm := by rw [mul_div_cancel₀ _ hs]
  apply mul_right_cancel₀ hc
  calc
    (companionMinus f gm δ - (g - 1)) * Real.cos δ =
        gm - 1 - (f - 1) * Real.sin δ - (g - 1) * Real.cos δ := by
      rw [sub_mul, companionMinus, div_mul_cancel₀ _ hc]
    _ = -Real.sin δ *
        (f + (g * Real.cos δ - gm) / Real.sin δ - 1 + Real.tan (δ / 2)) := by
      nlinarith [hhalf, hsec]
    _ = (-Real.tan δ *
        (f + (g * Real.cos δ - gm) / Real.sin δ - 1 + Real.tan (δ / 2))) * Real.cos δ := by
      rw [← htan]
      ring

def forwardSecondCornerSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  MovingSofaOptimality.supp U (t + Real.pi / 2) - forwardAngularSecant U t δ - 1

def backwardFirstCornerSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  MovingSofaOptimality.supp U t + backwardAngularSecant U (t + Real.pi / 2) δ - 1

def positiveShadowMargin (U : Set Plane) (t δ : ℝ) : ℝ :=
  min (-forwardSecondCornerSecant U t δ - Real.tan (δ / 2))
    (min (firstCornerSecant U t δ - Real.tan (δ / 2))
      (firstCornerSecant U t δ - Real.tan (δ / 2) -
        Real.tan δ * (-secondCornerSecant U t δ + Real.tan (δ / 2))))

def negativeShadowMargin (U : Set Plane) (t δ : ℝ) : ℝ :=
  min (secondCornerSecant U t δ - Real.tan (δ / 2))
    (min (-backwardFirstCornerSecant U t δ - Real.tan (δ / 2))
      (secondCornerSecant U t δ - Real.tan (δ / 2) +
        Real.tan δ * (firstCornerSecant U t δ - Real.tan (δ / 2))))

theorem first_forward_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    firstLo (support U (unitNormal t)) (support U (unitNormal (t + δ))) δ -
      (support U (companionNormal t) - 1) =
        -forwardSecondCornerSecant U t δ - Real.tan (δ / 2) := by
  rw [firstLo_eq_secant_sub_tan hs hh, companionNormal_eq_unitNormal]
  change (MovingSofaOptimality.supp U (t + δ) - MovingSofaOptimality.supp U t * Real.cos δ) / Real.sin δ -
    Real.tan (δ / 2) - (MovingSofaOptimality.supp U (t + Real.pi / 2) - 1) = _
  unfold forwardSecondCornerSecant forwardAngularSecant
  ring

theorem first_companion_forward_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionPlus (support U (unitNormal t)) (support U (companionNormal (t + δ))) δ -
      (support U (companionNormal t) - 1) =
        Real.tan δ * (firstCornerSecant U t δ - Real.tan (δ / 2)) := by
  rw [companionPlus_sub_eq_secant hc hs hh]
  rfl

theorem second_companion_forward_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionMinus (support U (companionNormal t)) (support U (unitNormal (t + δ))) δ -
      (support U (unitNormal t) - 1) =
        Real.tan δ * (-forwardSecondCornerSecant U t δ - Real.tan (δ / 2)) := by
  rw [companionMinus_sub_eq_secant hc hs hh, companionNormal_eq_unitNormal]
  change -Real.tan δ * (MovingSofaOptimality.supp U (t + Real.pi / 2) +
    (MovingSofaOptimality.supp U t * Real.cos δ - MovingSofaOptimality.supp U (t + δ)) / Real.sin δ - 1 +
      Real.tan (δ / 2)) = _
  unfold forwardSecondCornerSecant forwardAngularSecant
  ring

theorem second_mixed_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionPlus (support U (companionNormal t)) (support U (unitNormal (t - δ))) δ -
      firstHi (support U (companionNormal t)) (support U (companionNormal (t + δ))) δ =
        firstCornerSecant U t δ - Real.tan (δ / 2) -
          Real.tan δ * (-secondCornerSecant U t δ + Real.tan (δ / 2)) := by
  have h := companionPlus_sub_eq_secant
    (f := support U (companionNormal t)) (g := support U (unitNormal t))
    (gp := support U (unitNormal (t - δ))) hc hs hh
  rw [firstHi_eq_secant_add_tan hs hh]
  unfold firstCornerSecant secondCornerSecant
  linear_combination h

theorem second_backward_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    firstLo (support U (companionNormal t)) (support U (companionNormal (t - δ))) δ -
      (support U (unitNormal t) - 1) =
        -backwardFirstCornerSecant U t δ - Real.tan (δ / 2) := by
  rw [firstLo_eq_secant_sub_tan hs hh]
  simp only [companionNormal_eq_unitNormal,
    show (t - δ) + Real.pi / 2 = (t + Real.pi / 2) - δ by ring]
  change (MovingSofaOptimality.supp U ((t + Real.pi / 2) - δ) -
    MovingSofaOptimality.supp U (t + Real.pi / 2) * Real.cos δ) / Real.sin δ -
      Real.tan (δ / 2) - (MovingSofaOptimality.supp U t - 1) = _
  unfold backwardFirstCornerSecant backwardAngularSecant
  ring

theorem second_companion_backward_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionPlus (support U (companionNormal t)) (support U (unitNormal (t - δ))) δ -
      (support U (unitNormal t) - 1) =
        Real.tan δ * (secondCornerSecant U t δ - Real.tan (δ / 2)) := by
  rw [companionPlus_sub_eq_secant hc hs hh]
  rfl

theorem first_companion_backward_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionMinus (support U (unitNormal t)) (support U (companionNormal (t - δ))) δ -
      (support U (companionNormal t) - 1) =
        Real.tan δ * (-backwardFirstCornerSecant U t δ - Real.tan (δ / 2)) := by
  rw [companionMinus_sub_eq_secant hc hs hh]
  simp only [companionNormal_eq_unitNormal,
    show (t - δ) + Real.pi / 2 = (t + Real.pi / 2) - δ by ring]
  change -Real.tan δ * (MovingSofaOptimality.supp U t +
    (MovingSofaOptimality.supp U (t + Real.pi / 2) * Real.cos δ -
      MovingSofaOptimality.supp U ((t + Real.pi / 2) - δ)) / Real.sin δ - 1 + Real.tan (δ / 2)) = _
  unfold backwardFirstCornerSecant backwardAngularSecant
  ring

theorem first_mixed_shadow_gap (U : Set Plane) (t : ℝ) {δ : ℝ}
    (hc : Real.cos δ ≠ 0) (hs : Real.sin δ ≠ 0) (hh : Real.cos (δ / 2) ≠ 0) :
    companionPlus (support U (unitNormal t)) (support U (companionNormal (t + δ))) δ -
      firstHi (support U (unitNormal t)) (support U (unitNormal (t - δ))) δ =
        secondCornerSecant U t δ - Real.tan (δ / 2) +
          Real.tan δ * (firstCornerSecant U t δ - Real.tan (δ / 2)) := by
  have h := first_companion_forward_shadow_gap U t hc hs hh
  rw [firstHi_eq_secant_add_tan hs hh]
  unfold secondCornerSecant
  linear_combination h

theorem positive_shadow_source_bounds {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0)
    (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hmargin : 0 < positiveShadowMargin U t.val δ) :
    innerSourceSet U grid (Sum.inl t) = ∅ ∧
      (∫ x in a..b, innerDensity U grid (Sum.inr t) x) ≤
        max (2 * Real.tan (δ / 2) - (upperCurvature U {t.val + Real.pi / 2}).toReal) 0 := by
  have hm := lt_min_iff.mp hmargin
  have htan : 0 < Real.tan δ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hs hc
  have hg1 := first_forward_shadow_gap U t.val hs.ne' hh
  have hg2 := first_companion_forward_shadow_gap U t.val hc.ne' hs.ne' hh
  have hg3 := second_companion_forward_shadow_gap U t.val hc.ne' hs.ne' hh
  have hg4 := second_mixed_shadow_gap U t.val hc.ne' hs.ne' hh
  have hp1 := hm.1
  have hp2 := (lt_min_iff.mp hm.2).1
  have hp3 := (lt_min_iff.mp hm.2).2
  constructor
  · apply first_source_empty_of_forward_separation hU grid t hc hs hminus hplus
    · linarith [hg1]
    · have hmul := mul_pos htan hp2
      linarith [hg2]
  · apply integral_second_source_le_self_interval hU grid t hc hs hh hab hminus hplus
    · have hmul := mul_pos htan hp1
      linarith [hg3]
    · linarith [hg4]

theorem negative_shadow_source_bounds {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0)
    (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hmargin : 0 < negativeShadowMargin U t.val δ) :
    innerSourceSet U grid (Sum.inr t) = ∅ ∧
      (∫ x in a..b, innerDensity U grid (Sum.inl t) x) ≤
        max (2 * Real.tan (δ / 2) - (upperCurvature U {(t.val : ℝ)}).toReal) 0 := by
  have hm := lt_min_iff.mp hmargin
  have htan : 0 < Real.tan δ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hs hc
  have hg1 := second_backward_shadow_gap U t.val hs.ne' hh
  have hg2 := second_companion_backward_shadow_gap U t.val hc.ne' hs.ne' hh
  have hg3 := first_companion_backward_shadow_gap U t.val hc.ne' hs.ne' hh
  have hg4 := first_mixed_shadow_gap U t.val hc.ne' hs.ne' hh
  have hp1 := hm.1
  have hp2 := (lt_min_iff.mp hm.2).1
  have hp3 := (lt_min_iff.mp hm.2).2
  constructor
  · apply second_source_empty_of_backward_separation hU grid t hc hs hminus hplus
    · linarith [hg1]
    · have hmul := mul_pos htan hp1
      linarith [hg2]
  · apply integral_first_source_le_self_interval hU grid t hc hs hh hab hminus hplus
    · have hmul := mul_pos htan hp2
      linarith [hg3]
    · linarith [hg4]

theorem mesh_half_tan_nonneg (n : ℕ) : 0 ≤ Real.tan (mesh n / 2) := by
  apply nonneg_of_mul_nonneg_left _ (mesh_sin_pos n)
  rw [MovingSofaOptimality.tan_half_mul_sin (mesh_half_cos_ne n)]
  linarith [Real.cos_le_one (mesh n)]

theorem IsSelectedPolygon.positive_shadow_atoms {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (t : InteriorPoint (dyadic level))
    (hmargin : 0 < positiveShadowMargin U t.val (mesh level)) :
    (upperCurvature U {(t.val : ℝ)}).toReal ≤ middleOuterMass U (dyadic level) (Sum.inl t) +
        selectionDefect target U level coefficient (Sum.inl t) ∧
      (upperCurvature U {t.val + Real.pi / 2}).toReal ≤ Real.tan (mesh level / 2) +
        middleOuterMass U (dyadic level) (Sum.inr t) +
          selectionDefect target U level coefficient (Sum.inr t) := by
  obtain ⟨hm, hp⟩ := dyadic_neighbors level t
  have hab : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by
    linarith [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]
  have hsource := positive_shadow_source_bounds hU.isCap (dyadic level) t
    (mesh_cos_pos level) (mesh_sin_pos level) (mesh_half_cos_ne level) hab hm hp hmargin
  exact ⟨hU.curvature_atom_le_error_of_source_empty hc (Sum.inl t) hsource.1,
    hU.curvature_atom_le_half_of_self_interval hc (Sum.inr t) (mesh_half_tan_nonneg level)
      hsource.2⟩

theorem IsSelectedPolygon.negative_shadow_atoms {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (t : InteriorPoint (dyadic level))
    (hmargin : 0 < negativeShadowMargin U t.val (mesh level)) :
    (upperCurvature U {t.val + Real.pi / 2}).toReal ≤
        middleOuterMass U (dyadic level) (Sum.inr t) +
          selectionDefect target U level coefficient (Sum.inr t) ∧
      (upperCurvature U {(t.val : ℝ)}).toReal ≤ Real.tan (mesh level / 2) +
        middleOuterMass U (dyadic level) (Sum.inl t) +
          selectionDefect target U level coefficient (Sum.inl t) := by
  obtain ⟨hm, hp⟩ := dyadic_neighbors level t
  have hab : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by
    linarith [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]
  have hsource := negative_shadow_source_bounds hU.isCap (dyadic level) t
    (mesh_cos_pos level) (mesh_sin_pos level) (mesh_half_cos_ne level) hab hm hp hmargin
  exact ⟨hU.curvature_atom_le_error_of_source_empty hc (Sum.inr t) hsource.1,
    hU.curvature_atom_le_half_of_self_interval hc (Sum.inl t) (mesh_half_tan_nonneg level)
      hsource.2⟩

end AngularGrid

theorem CapHausdorffTendsto.forwardSecondCornerSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    Tendsto (fun n => AngularGrid.forwardSecondCornerSecant (U n) (angle n) (δ n))
      atTop (𝓝 (secondCornerVelocity K t)) := by
  have hshift := hangle.add_const (Real.pi / 2)
  have hnormal : Tendsto (fun n => unitNormal (angle n + Real.pi / 2)) atTop
      (𝓝 (unitNormal (t + Real.pi / 2))) :=
    (Real.continuous_cos.tendsto _ |>.comp hshift).prodMk_nhds
      (Real.continuous_sin.tendsto _ |>.comp hshift)
  have hsupp : Tendsto (fun n => MovingSofaOptimality.supp (U n) (angle n + Real.pi / 2)) atTop
      (𝓝 (MovingSofaOptimality.supp K (t + Real.pi / 2))) :=
    h.support_tendsto_moving hU hK hnormal
  have hsec := h.forwardAngularSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht
  simpa only [AngularGrid.forwardSecondCornerSecant, secondCornerVelocity] using
    (hsupp.sub hsec).sub_const 1

theorem CapHausdorffTendsto.backwardFirstCornerSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.backwardFirstCornerSecant (U n) (angle n) (δ n))
      atTop (𝓝 (firstCornerVelocity K t)) := by
  have hnormal : Tendsto (fun n => unitNormal (angle n)) atTop (𝓝 (unitNormal t)) :=
    (Real.continuous_cos.tendsto _ |>.comp hangle).prodMk_nhds
      (Real.continuous_sin.tendsto _ |>.comp hangle)
  have hsupp : Tendsto (fun n => MovingSofaOptimality.supp (U n) (angle n)) atTop
      (𝓝 (MovingSofaOptimality.supp K t)) := h.support_tendsto_moving hU hK hnormal
  have hsec := h.backwardAngularSecant_tendsto hU hK hB hbox
    (hangle.add_const (Real.pi / 2)) hδ hsin hcos ht
  simpa only [AngularGrid.backwardFirstCornerSecant, firstCornerVelocity] using
    (hsupp.add hsec).sub_const 1

theorem CapHausdorffTendsto.positiveShadowMargin_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) (htcomp : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.positiveShadowMargin (U n) (angle n) (δ n)) atTop
      (𝓝 (min (-secondCornerVelocity K t) (firstCornerVelocity K t))) := by
  have hrf := h.forwardSecondCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht
  have hrb := h.secondCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht
  have hqf := h.firstCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos htcomp
  have htan0 := (Real.hasDerivAt_tan (x := 0) (by simp)).continuousAt.tendsto
  have htan : Tendsto (fun n => Real.tan (δ n)) atTop (𝓝 0) := by
    simpa only [Real.tan_zero, Function.comp_def] using htan0.comp hδ
  have hhalf : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by
      simpa only [zero_div] using hδ.div_const 2
    simpa only [Real.tan_zero, Function.comp_def] using htan0.comp hdiv
  have hthird := (hqf.sub hhalf).sub (htan.mul (hrb.neg.add hhalf))
  simpa only [AngularGrid.positiveShadowMargin, sub_zero, add_zero, zero_mul, min_self] using
    (hrf.neg.sub hhalf).min ((hqf.sub hhalf).min hthird)

theorem CapHausdorffTendsto.negativeShadowMargin_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) (htcomp : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.negativeShadowMargin (U n) (angle n) (δ n)) atTop
      (𝓝 (min (secondCornerVelocity K t) (-firstCornerVelocity K t))) := by
  have hrb := h.secondCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht
  have hqf := h.firstCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos htcomp
  have hqb := h.backwardFirstCornerSecant_tendsto hU hK hB hbox hangle hδ hsin hcos htcomp
  have htan0 := (Real.hasDerivAt_tan (x := 0) (by simp)).continuousAt.tendsto
  have htan : Tendsto (fun n => Real.tan (δ n)) atTop (𝓝 0) := by
    simpa only [Real.tan_zero, Function.comp_def] using htan0.comp hδ
  have hhalf : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by
      simpa only [zero_div] using hδ.div_const 2
    simpa only [Real.tan_zero, Function.comp_def] using htan0.comp hdiv
  have hthird := (hrb.sub hhalf).add (htan.mul (hqf.sub hhalf))
  have hlim := (hrb.sub hhalf).min ((hqb.neg.sub hhalf).min hthird)
  have hmin (a b : ℝ) : min a (min b a) = min a b := by
    rcases le_total a b with hab | hba
    · simp only [min_eq_left hab, min_eq_right hab, min_self]
    · simp only [min_eq_left hba, min_eq_right hba]
  simpa only [AngularGrid.negativeShadowMargin, sub_zero, zero_mul, add_zero,
    hmin] using hlim

end AmbidextrousSofa
