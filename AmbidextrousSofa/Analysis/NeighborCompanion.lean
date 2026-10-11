module

public import AmbidextrousSofa.Analysis.NeighborLength

@[expose] public section

/-!
# The companion-wall neighboring estimate

The companion source uses the same two-interval argument with the angle
order reversed. The proof works with the literal selected finite source;
it needs no assertion that a tie-breaking rule commutes with reflection.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem measure_addParameterIntervals_le {S : Set ℝ} {s : ℝ} (hs : 0 < s)
    (c a b d e : ℝ)
    (hS : ∀ x ∈ S, ∃ v : ℝ, x = c + v * s ∧ v ∈ Icc a b ∪ Icc d e) :
    volume.real S / s ≤ max (b - a) 0 + max (e - d) 0 := by
  simpa only [neg_sub_neg] using measure_parameterIntervals_le hs c (-b) (-a) (-e) (-d)
    fun x hx => by
      obtain ⟨v, rfl, hv⟩ := hS x hx
      refine ⟨-v, by ring, ?_⟩
      rcases hv with hv | hv
      exacts [Or.inl ⟨neg_le_neg hv.2, neg_le_neg hv.1⟩, Or.inr ⟨neg_le_neg hv.2, neg_le_neg hv.1⟩]

namespace AngularGrid

open FinitePolygon

theorem second_source_le_first (U : Set Plane) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inr t)) :
    supportWall U (companionNormal t.val) x ≤ supportWall U (unitNormal t.val) x := by
  classical
  let v : Option (SourceIndex grid) → ℝ := fun i => wallSlope (normal grid) i * x +
    barrierIntercept (normal grid) (fun j => support U (normal grid j)) i
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some (v := v) hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases (Sum.inl s, Sum.inr s) v with h | h <;> rw [h.1] at hselected
  · simp at hselected
  · obtain rfl : s = t := by simpa using hselected
    have h2 := h.2
    simp only [v, ← supportWall_eq_affine] at h2
    exact h2

def companionPoint (U : Set Plane) (t v : ℝ) : Plane :=
  v • unitNormal t + (support U (companionNormal t) - 1) • companionNormal t

theorem companionPoint_fst (U : Set Plane) (t v : ℝ) :
    (companionPoint U t v).1 =
      -(support U (companionNormal t) - 1) * Real.sin t + v * Real.cos t := by
  simp only [companionPoint, unitNormal, companionNormal, Prod.fst_add,
    Prod.smul_fst, smul_eq_mul]
  ring

theorem dot_companionPoint_first (U : Set Plane) (t v s : ℝ) :
    coordDot (companionPoint U t v) (unitNormal s) =
      v * Real.cos (s - t) + (support U (companionNormal t) - 1) * Real.sin (s - t) := by
  simp [companionPoint, coordDot, unitNormal, companionNormal, Real.cos_sub, Real.sin_sub]
  ring

theorem dot_companionPoint_companion (U : Set Plane) (t v s : ℝ) :
    coordDot (companionPoint U t v) (companionNormal s) =
      v * Real.sin (t - s) + (support U (companionNormal t) - 1) * Real.cos (t - s) := by
  simp [companionPoint, coordDot, unitNormal, companionNormal, Real.cos_sub, Real.sin_sub]
  ring

theorem point_eq_companionPoint {U : Set Plane} {p : Plane} {t : ℝ}
    (hline : coordDot p (companionNormal t) = support U (companionNormal t) - 1) :
    p = companionPoint U t (coordDot p (unitNormal t)) := by
  have h := MovingSofaOptimality.eq_dot_uvec_smul_add p t
  change p = coordDot p (unitNormal t) • unitNormal t +
    coordDot p (companionNormal t) • companionNormal t at h
  rwa [hline] at h

theorem second_source_neighbor_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inr t)) :
    ∃ v : ℝ, x = -(support U (companionNormal t.val) - 1) * Real.sin t.val +
        v * Real.cos t.val ∧
      v ∈ neighborParameters (support U (companionNormal t.val)) (support U (unitNormal t.val))
        (support U (companionNormal ((t.val : ℝ) + δ)))
        (support U (companionNormal ((t.val : ℝ) - δ)))
        (support U (unitNormal ((t.val : ℝ) + δ)))
        (support U (unitNormal ((t.val : ℝ) - δ))) δ := by
  let p : Plane := (x, supportWall U (companionNormal t.val) x)
  have hy : finiteBarrier U (normal grid) (pairList grid) none p.1 = p.2 :=
    innerSource_height U grid (Sum.inr t) hx
  have hy0 : 0 ≤ p.2 := hy ▸ finiteBarrier_nonneg _ _ _ _ _
  have hp : p = companionPoint U t.val (coordDot p (unitNormal t.val)) :=
    point_eq_companionPoint (le_antisymm
      ((le_supportWall_iff (normal_snd_pos grid (Sum.inr t)) _ _).mp le_rfl)
      ((supportWall_le_iff (normal_snd_pos grid (Sum.inr t)) _ _).mp le_rfl))
  have hv : coordDot p (unitNormal t.val) ≤ support U (unitNormal t.val) - 1 :=
    (le_supportWall_iff (normal_snd_pos grid (Sum.inl t)) _ _).mp
      (second_source_le_first U grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_niche_wall_alternative hU grid hy0 hy.le hsm
  have hp' := above_niche_wall_alternative hU grid hy0 hy.le hsp
  rw [hp] at hm hp'
  simp only [hsmval, hspval, dot_companionPoint_first, dot_companionPoint_companion,
    sub_sub_cancel_left, sub_sub_cancel, add_sub_cancel_left, sub_add_cancel_left,
    Real.cos_neg, Real.sin_neg] at hm hp'
  refine ⟨_, ?_, mem_neighborParameters hc hs hv (hp'.symm.imp (fun h => by linarith)
    fun h => by linarith) (hm.symm.imp (fun h => by linarith) fun h => by linarith)⟩
  simpa only [companionPoint_fst] using congrArg Prod.fst hp

def secondCornerSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  support U (companionNormal t) +
    (support U (unitNormal (t - δ)) -
      support U (unitNormal t) * Real.cos δ) / Real.sin δ - 1

theorem companion_interval_length_le_curvature {U : Set Plane} (hU : IsDownwardCap U)
    (t : ℝ) {δ : ℝ} (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0) :
    firstHi (support U (companionNormal t)) (support U (companionNormal (t + δ))) δ -
      firstLo (support U (companionNormal t)) (support U (companionNormal (t - δ))) δ ≤
        2 * Real.tan (δ / 2) - (upperCurvature U {t + Real.pi / 2}).toReal := by
  have h := first_interval_length_le_curvature hU (t + Real.pi / 2) hs hh
  rw [show t + Real.pi / 2 - δ = (t - δ) + Real.pi / 2 by ring,
    show t + Real.pi / 2 + δ = (t + δ) + Real.pi / 2 by ring] at h
  simp only [← companionNormal_eq_unitNormal] at h
  convert h using 1
  unfold firstHi firstLo
  ring

theorem integral_second_source_le_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inr t) x) ≤
      max (support U (unitNormal t.val) - 1 -
        min (companionMinus (support U (companionNormal t.val))
          (support U (unitNormal ((t.val : ℝ) + δ))) δ)
          (companionPlus (support U (companionNormal t.val))
            (support U (unitNormal ((t.val : ℝ) - δ))) δ)) 0 +
      max (firstHi (support U (companionNormal t.val))
          (support U (companionNormal ((t.val : ℝ) + δ))) δ -
        firstLo (support U (companionNormal t.val))
          (support U (companionNormal ((t.val : ℝ) - δ))) δ) 0 := by
  classical
  exact (integral_sourceDensity_outward (barrierExpr (pairList grid) none) (normal grid)
    (barrierIntercept (normal grid) (fun i => support U (normal grid i))) (Sum.inr t) hab).trans_le
    (measure_addParameterIntervals_le (normal_snd_pos grid (Sum.inr t))
      (-(support U (companionNormal t.val) - 1) * Real.sin t.val) _ _ _ _ fun x hx =>
        second_source_neighbor_parameters hU grid t hc hs hminus hplus hx.2)

theorem integral_second_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inr t) x) ≤
      Real.tan δ * (|secondCornerSecant U t.val δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {t.val + Real.pi / 2}).toReal) 0 :=
  (integral_second_source_le_parameters hU grid t hc hs hab hminus hplus).trans
    (add_le_add (companion_interval_length_le hc hs hh
      (by linarith [hU.support_secondDifference_nonneg t.val hs.le]))
      (max_le_max (companion_interval_length_le_curvature hU t.val hs hh) le_rfl))

end AngularGrid

end AmbidextrousSofa
