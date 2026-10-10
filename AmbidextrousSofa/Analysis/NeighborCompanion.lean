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

theorem image_addParameterInterval {s : ℝ} (hs : 0 < s) (c a b : ℝ) :
    (fun v : ℝ => c + v * s) '' Icc a b = Icc (c + a * s) (c + b * s) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨add_le_add_right (mul_le_mul_of_nonneg_right hv.1 hs.le) _,
      add_le_add_right (mul_le_mul_of_nonneg_right hv.2 hs.le) _⟩
  · intro hx
    refine ⟨(x - c) / s, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hs]
      linarith [hx.1]
    · rw [div_le_iff₀ hs]
      linarith [hx.2]
    · dsimp only
      rw [div_mul_cancel₀ _ hs.ne']
      ring

theorem volume_real_image_addParameterInterval {s : ℝ} (hs : 0 < s) (c a b : ℝ) :
    volume.real ((fun v : ℝ => c + v * s) '' Icc a b) = s * max (b - a) 0 := by
  rw [image_addParameterInterval hs, Real.volume_real_Icc,
    mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  ring

theorem measure_addParameterIntervals_le {S : Set ℝ} {s : ℝ} (hs : 0 < s)
    (c a b d e : ℝ)
    (hS : ∀ x ∈ S, ∃ v : ℝ, x = c + v * s ∧ v ∈ Icc a b ∪ Icc d e) :
    volume.real S / s ≤ max (b - a) 0 + max (e - d) 0 := by
  let F : ℝ → ℝ := fun v => c + v * s
  have hsub : S ⊆ F '' Icc a b ∪ F '' Icc d e := by
    intro x hx
    obtain ⟨v, rfl, hv⟩ := hS x hx
    rcases hv with hv | hv
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  have hfinite : volume (F '' Icc a b ∪ F '' Icc d e) ≠ ⊤ := by
    dsimp only [F]
    rw [image_addParameterInterval hs, image_addParameterInterval hs]
    exact (measure_union_lt_top isCompact_Icc.measure_lt_top isCompact_Icc.measure_lt_top).ne
  have hvol : volume.real S ≤ s * max (b - a) 0 + s * max (e - d) 0 := by
    calc
      volume.real S ≤ volume.real (F '' Icc a b ∪ F '' Icc d e) :=
        measureReal_mono hsub hfinite
      _ ≤ volume.real (F '' Icc a b) + volume.real (F '' Icc d e) :=
        measureReal_union_le _ _
      _ = s * max (b - a) 0 + s * max (e - d) 0 := by
        rw [volume_real_image_addParameterInterval hs, volume_real_image_addParameterInterval hs]
  rw [div_le_iff₀ hs]
  nlinarith

namespace AngularGrid

open FinitePolygon

theorem second_source_le_first (U : Set Plane) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inr t)) :
    supportWall U (companionNormal t.val) x ≤ supportWall U (unitNormal t.val) x := by
  classical
  let v : Option (SourceIndex grid) → ℝ := fun i => wallSlope (normal grid) i * x +
    barrierIntercept (normal grid) (fun j => support U (normal grid j)) i
  have hsource : (nicheExpr (pairList grid)).source v = some (Sum.inr t) := hx
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some hsource
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases (Sum.inl s, Sum.inr s) v with h | h
  · have hfalse := hselected.symm.trans h.1
    simp at hfalse
  · have heq : t = s := Sum.inr.inj (Option.some.inj (hselected.symm.trans h.1))
    subst s
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
  change MovingSofaOptimality.dot
    (v • MovingSofaOptimality.uvec t + (support U (companionNormal t) - 1) • MovingSofaOptimality.vvec t)
      (MovingSofaOptimality.uvec s) = _
  rw [MovingSofaOptimality.dot_add_left, MovingSofaOptimality.dot_smul_left, MovingSofaOptimality.dot_smul_left,
    MovingSofaOptimality.dot_uvec_uvec, MovingSofaOptimality.dot_vvec_uvec',
    show Real.cos (t - s) = Real.cos (s - t) by rw [← Real.cos_neg, neg_sub]]

theorem dot_companionPoint_companion (U : Set Plane) (t v s : ℝ) :
    coordDot (companionPoint U t v) (companionNormal s) =
      v * Real.sin (t - s) + (support U (companionNormal t) - 1) * Real.cos (t - s) := by
  change MovingSofaOptimality.dot
    (v • MovingSofaOptimality.uvec t + (support U (companionNormal t) - 1) • MovingSofaOptimality.vvec t)
      (MovingSofaOptimality.vvec s) = _
  rw [MovingSofaOptimality.dot_add_left, MovingSofaOptimality.dot_smul_left, MovingSofaOptimality.dot_smul_left,
    MovingSofaOptimality.dot_uvec_vvec', MovingSofaOptimality.dot_vvec_vvec]

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
  let y := supportWall U (companionNormal t.val) x
  let p : Plane := (x, y)
  let v := coordDot p (unitNormal t.val)
  have hy : finiteBarrier U (normal grid) (pairList grid) none x = y :=
    innerSource_height U grid (Sum.inr t) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (companionNormal t.val) = support U (companionNormal t.val) - 1 := by
    apply le_antisymm
    · exact (le_supportWall_iff (normal_snd_pos grid (Sum.inr t)) x y).mp le_rfl
    · exact (supportWall_le_iff (normal_snd_pos grid (Sum.inr t)) x y).mp le_rfl
  have hp : p = companionPoint U t.val v := point_eq_companionPoint hline
  have hv : v ≤ support U (unitNormal t.val) - 1 :=
    (le_supportWall_iff (normal_snd_pos grid (Sum.inl t)) x y).mp
      (second_source_le_first U grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_niche_wall_alternative hU grid hy0 hy.le hsm
  have hp' := above_niche_wall_alternative hU grid hy0 hy.le hsp
  rw [hsmval, hp, dot_companionPoint_first, dot_companionPoint_companion,
    show (t.val : ℝ) - δ - (t.val : ℝ) = -δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) - δ) = δ by ring,
    Real.cos_neg, Real.sin_neg] at hm
  rw [hspval, hp, dot_companionPoint_first, dot_companionPoint_companion,
    show (t.val : ℝ) + δ - (t.val : ℝ) = δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) + δ) = -δ by ring,
    Real.sin_neg, Real.cos_neg] at hp'
  refine ⟨v, ?_, mem_neighborParameters hc hs hv ?_ ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, companionPoint_fst] using h
  · rcases hp' with h | h
    · right
      nlinarith
    · left
      nlinarith
  · rcases hm with h | h
    · right
      nlinarith
    · left
      nlinarith

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
  calc
    firstHi (support U (companionNormal t)) (support U (companionNormal (t + δ))) δ -
        firstLo (support U (companionNormal t)) (support U (companionNormal (t - δ))) δ =
      firstHi (support U (companionNormal t)) (support U (companionNormal (t - δ))) δ -
        firstLo (support U (companionNormal t)) (support U (companionNormal (t + δ))) δ := by
          unfold firstHi firstLo
          ring
    _ ≤ _ := h

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
  have ht : 0 < Real.cos t.val := normal_snd_pos grid (Sum.inr t)
  have hint := integral_sourceDensity_outward (barrierExpr (pairList grid) none)
    (normal grid) (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (Sum.inr t) hab
  change (∫ x in a..b, innerDensity U grid (Sum.inr t) x) =
    volume.real (Ioc a b ∩ innerSourceSet U grid (Sum.inr t)) / Real.cos t.val at hint
  rw [hint]
  apply measure_addParameterIntervals_le ht
    (-(support U (companionNormal t.val) - 1) * Real.sin t.val)
  intro x hx
  exact second_source_neighbor_parameters hU grid t hc hs hminus hplus hx.2

theorem integral_second_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inr t) x) ≤
      Real.tan δ * (|secondCornerSecant U t.val δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {t.val + Real.pi / 2}).toReal) 0 := by
  have hraw := integral_second_source_le_parameters hU grid t hc hs hab hminus hplus
  have hconv : 0 ≤ support U (unitNormal ((t.val : ℝ) + δ)) +
      support U (unitNormal ((t.val : ℝ) - δ)) -
        2 * Real.cos δ * support U (unitNormal t.val) := by
    nlinarith [hU.support_secondDifference_nonneg t.val hs.le]
  have hcomp := companion_interval_length_le (f := support U (companionNormal t.val))
    hc hs hh hconv
  have hfirst := companion_interval_length_le_curvature hU t.val hs hh
  exact hraw.trans (add_le_add hcomp (max_le_max hfirst le_rfl))

end AngularGrid

end AmbidextrousSofa
