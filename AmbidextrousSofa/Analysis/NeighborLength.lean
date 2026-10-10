module

public import AmbidextrousSofa.Analysis.NeighborWalls

@[expose] public section

/-!
# Quantitative neighboring-wall source bounds

The literal finite niche source set is confined to two tangent intervals.
Their horizontal images give its actual Lebesgue measure. The second
interval is controlled by the actual Stieltjes curvature atom, using only
support inequalities at the two endpoints of the supporting face. This
does not require consecutive sampled walls to have nonzero facets.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem image_parameterInterval {s : ℝ} (hs : 0 < s) (c a b : ℝ) :
    (fun v : ℝ => c - v * s) '' Icc a b = Icc (c - b * s) (c - a * s) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hv.2 hs.le]
    · nlinarith [mul_le_mul_of_nonneg_right hv.1 hs.le]
  · intro hx
    refine ⟨(c - x) / s, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hs]
      linarith [hx.2]
    · rw [div_le_iff₀ hs]
      linarith [hx.1]
    · show c - (c - x) / s * s = x
      rw [div_mul_cancel₀ _ hs.ne']
      ring

theorem volume_real_image_parameterInterval {s : ℝ} (hs : 0 < s) (c a b : ℝ) :
    volume.real ((fun v : ℝ => c - v * s) '' Icc a b) = s * max (b - a) 0 := by
  rw [image_parameterInterval hs, Real.volume_real_Icc,
    mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  ring

/-- The intervals may be empty or overlap. No disjointness assertion is
needed for this upper bound. -/
theorem measure_parameterIntervals_le {S : Set ℝ} {s : ℝ} (hs : 0 < s)
    (c a b d e : ℝ)
    (hS : ∀ x ∈ S, ∃ v : ℝ, x = c - v * s ∧ v ∈ Icc a b ∪ Icc d e) :
    volume.real S / s ≤ max (b - a) 0 + max (e - d) 0 := by
  let F : ℝ → ℝ := fun v => c - v * s
  have hsub : S ⊆ F '' Icc a b ∪ F '' Icc d e := by
    intro x hx
    obtain ⟨v, rfl, hv⟩ := hS x hx
    rcases hv with hv | hv
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  have hfinite : volume (F '' Icc a b ∪ F '' Icc d e) ≠ ⊤ := by
    dsimp only [F]
    rw [image_parameterInterval hs, image_parameterInterval hs]
    exact (measure_union_lt_top isCompact_Icc.measure_lt_top isCompact_Icc.measure_lt_top).ne
  have hvol : volume.real S ≤ s * max (b - a) 0 + s * max (e - d) 0 := by
    calc
      volume.real S ≤ volume.real (F '' Icc a b ∪ F '' Icc d e) :=
        measureReal_mono hsub hfinite
      _ ≤ volume.real (F '' Icc a b) + volume.real (F '' Icc d e) :=
        measureReal_union_le _ _
      _ = s * max (b - a) 0 + s * max (e - d) 0 := by
        rw [volume_real_image_parameterInterval hs, volume_real_image_parameterInterval hs]
  rw [div_le_iff₀ hs]
  nlinarith

/-- Every actual face atom is bounded by the support second difference.
The inequality is obtained at the two actual endpoints of that face. -/
theorem IsDownwardCap.curvature_atom_mul_sin_le {U : Set Plane}
    (hU : IsDownwardCap U) (t δ : ℝ) :
    (upperCurvature U {t}).toReal * Real.sin δ ≤
      support U (unitNormal (t - δ)) + support U (unitNormal (t + δ)) -
        2 * Real.cos δ * support U (unitNormal t) := by
  have hK := hU.imported_isConvexBody
  have hm := MovingSofaOptimality.dot_le_supp hU.isCompact (MovingSofaOptimality.vminus_mem_edge hK t).1 (t - δ)
  have hp := MovingSofaOptimality.dot_le_supp hU.isCompact (MovingSofaOptimality.vplus_mem_edge hK t).1 (t + δ)
  rw [MovingSofaOptimality.dot_uvec_eq_cos_add_sin _ (t - δ) t,
    show t - δ - t = -δ by ring, Real.cos_neg, Real.sin_neg,
    MovingSofaOptimality.dot_vminus_uvec] at hm
  rw [MovingSofaOptimality.dot_uvec_eq_cos_add_sin _ (t + δ) t,
    show t + δ - t = δ by ring, MovingSofaOptimality.dot_vplus_uvec] at hp
  change MovingSofaOptimality.sigmaAt U t * Real.sin δ ≤
    MovingSofaOptimality.supp U (t - δ) + MovingSofaOptimality.supp U (t + δ) -
      2 * Real.cos δ * MovingSofaOptimality.supp U t
  rw [MovingSofaOptimality.sigmaAt_eq_dot_sub hK]
  nlinarith

theorem IsDownwardCap.support_secondDifference_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) (t : ℝ) {δ : ℝ} (hs : 0 ≤ Real.sin δ) :
    0 ≤ support U (unitNormal (t - δ)) + support U (unitNormal (t + δ)) -
      2 * Real.cos δ * support U (unitNormal t) :=
  (mul_nonneg ENNReal.toReal_nonneg hs).trans (hU.curvature_atom_mul_sin_le t δ)

theorem IsDownwardCap.companion_secondDifference_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) (t : ℝ) {δ : ℝ} (hs : 0 ≤ Real.sin δ) :
    0 ≤ support U (companionNormal (t - δ)) + support U (companionNormal (t + δ)) -
      2 * Real.cos δ * support U (companionNormal t) := by
  have h := hU.support_secondDifference_nonneg (t + Real.pi / 2) hs
  rw [show t + Real.pi / 2 - δ = (t - δ) + Real.pi / 2 by ring,
    show t + Real.pi / 2 + δ = (t + δ) + Real.pi / 2 by ring] at h
  simpa only [← companionNormal_eq_unitNormal] using h

namespace AngularGrid

open FinitePolygon

def firstCornerSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  support U (unitNormal t) +
    (support U (companionNormal (t + δ)) -
      support U (companionNormal t) * Real.cos δ) / Real.sin δ - 1

theorem companion_interval_length_le {f g gm gp δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0)
    (hconv : 0 ≤ gm + gp - 2 * Real.cos δ * g) :
    max (g - 1 - min (companionMinus f gm δ) (companionPlus f gp δ)) 0 ≤
      Real.tan δ * (|f + (gp - g * Real.cos δ) / Real.sin δ - 1| + Real.tan (δ / 2)) := by
  let q : ℝ := f + (gp - g * Real.cos δ) / Real.sin δ - 1
  let qm : ℝ := f + (g * Real.cos δ - gm) / Real.sin δ - 1
  have hqm : qm ≤ q := by
    dsimp only [qm, q]
    apply sub_le_sub_right
    apply add_le_add_right
    apply (div_le_div_iff_of_pos_right hs).mpr
    linarith
  have hhalf := MovingSofaOptimality.tan_half_mul_sin hh
  have hh0 : 0 ≤ Real.tan (δ / 2) := by
    apply nonneg_of_mul_nonneg_left _ hs
    rw [hhalf]
    linarith [Real.cos_le_one δ]
  have htan : 0 ≤ Real.tan δ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hs.le hc.le
  have hm : g - 1 - companionMinus f gm δ =
      Real.tan δ * (qm + Real.tan (δ / 2)) := by
    unfold companionMinus
    dsimp only [qm]
    rw [Real.tan_eq_sin_div_cos δ]
    have hhs := congrArg (fun z : ℝ => z * Real.sin δ) hhalf
    field_simp [hc.ne', hs.ne']
    nlinarith [hhs]
  have hp : g - 1 - companionPlus f gp δ =
      Real.tan δ * (-q + Real.tan (δ / 2)) := by
    unfold companionPlus
    dsimp only [q]
    rw [Real.tan_eq_sin_div_cos δ]
    have hhs := congrArg (fun z : ℝ => z * Real.sin δ) hhalf
    field_simp [hc.ne', hs.ne']
    nlinarith [hhs]
  have hmle : g - 1 - companionMinus f gm δ ≤
      Real.tan δ * (|q| + Real.tan (δ / 2)) := by
    rw [hm]
    exact mul_le_mul_of_nonneg_left (add_le_add_left (hqm.trans (le_abs_self q)) _) htan
  have hple : g - 1 - companionPlus f gp δ ≤
      Real.tan δ * (|q| + Real.tan (δ / 2)) := by
    rw [hp]
    exact mul_le_mul_of_nonneg_left (add_le_add_left (neg_le_abs q) _) htan
  have hzero : 0 ≤ Real.tan δ * (|q| + Real.tan (δ / 2)) :=
    mul_nonneg htan (add_nonneg (abs_nonneg q) hh0)
  change max (g - 1 - min (companionMinus f gm δ) (companionPlus f gp δ)) 0 ≤ _
  by_cases hmp : companionMinus f gm δ ≤ companionPlus f gp δ
  · rw [min_eq_left hmp]
    exact max_le hmle hzero
  · rw [min_eq_right (le_of_not_ge hmp)]
    exact max_le hple hzero

theorem first_interval_length_le_curvature {U : Set Plane} (hU : IsDownwardCap U)
    (t : ℝ) {δ : ℝ} (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0) :
    firstHi (support U (unitNormal t)) (support U (unitNormal (t - δ))) δ -
      firstLo (support U (unitNormal t)) (support U (unitNormal (t + δ))) δ ≤
        2 * Real.tan (δ / 2) - (upperCurvature U {t}).toReal := by
  have hcur := hU.curvature_atom_mul_sin_le t δ
  have hhalf := MovingSofaOptimality.tan_half_mul_sin hh
  have heq :
      (firstHi (support U (unitNormal t)) (support U (unitNormal (t - δ))) δ -
        firstLo (support U (unitNormal t)) (support U (unitNormal (t + δ))) δ) * Real.sin δ =
      2 - 2 * Real.cos δ -
        (support U (unitNormal (t - δ)) + support U (unitNormal (t + δ)) -
          2 * Real.cos δ * support U (unitNormal t)) := by
    unfold firstHi firstLo
    field_simp [hs.ne']
    ring
  apply (mul_le_mul_iff_left₀ hs).mp
  nlinarith

theorem integral_first_source_le_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inl t) x) ≤
      max (support U (companionNormal t.val) - 1 -
        min (companionMinus (support U (unitNormal t.val))
          (support U (companionNormal ((t.val : ℝ) - δ))) δ)
          (companionPlus (support U (unitNormal t.val))
            (support U (companionNormal ((t.val : ℝ) + δ))) δ)) 0 +
      max (firstHi (support U (unitNormal t.val))
          (support U (unitNormal ((t.val : ℝ) - δ))) δ -
        firstLo (support U (unitNormal t.val))
          (support U (unitNormal ((t.val : ℝ) + δ))) δ) 0 := by
  classical
  have ht : 0 < Real.sin t.val := normal_snd_pos grid (Sum.inl t)
  have hint := integral_sourceDensity_outward (barrierExpr (pairList grid) none)
    (normal grid) (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (Sum.inl t) hab
  change (∫ x in a..b, innerDensity U grid (Sum.inl t) x) =
    volume.real (Ioc a b ∩ innerSourceSet U grid (Sum.inl t)) / Real.sin t.val at hint
  rw [hint]
  apply measure_parameterIntervals_le ht
    ((support U (unitNormal t.val) - 1) * Real.cos t.val)
  intro x hx
  exact first_source_neighbor_parameters hU grid t hc hs hminus hplus hx.2

/-- The refined first-wall source estimate for the actual finite niche,
on any ordered spatial integration interval. -/
theorem integral_first_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inl t) x) ≤
      Real.tan δ * (|firstCornerSecant U t.val δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {(t.val : ℝ)}).toReal) 0 := by
  have hraw := integral_first_source_le_parameters hU grid t hc hs hab hminus hplus
  have hcomp := companion_interval_length_le (f := support U (unitNormal t.val)) hc hs hh
    (hU.companion_secondDifference_nonneg t.val hs.le)
  have hfirst := first_interval_length_le_curvature hU t.val hs hh
  exact hraw.trans (add_le_add hcomp (max_le_max hfirst le_rfl))

end AngularGrid

end AmbidextrousSofa
