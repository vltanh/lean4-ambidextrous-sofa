module

public import AmbidextrousSofa.Analysis.SelectedCurvature

@[expose] public section

/-!
# Neighboring walls constrain each actual finite niche source

A selected first wall lies below its own companion wall and above the
finite niche. At either neighboring angle it therefore satisfies one of
the two actual wall alternatives. These alternatives confine its tangent
parameter to two explicit intervals. The endpoint grid angles are included:
their alternative above the floor follows from the cap's height bound.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem supportWall_eq_affine (U : Set Plane) (normal : ι → Plane) (x : ℝ) (i : ι) :
    supportWall U (normal i) x = wallSlope normal (some i) * x +
      barrierIntercept normal (fun j => support U (normal j)) (some i) := by
  unfold supportWall wallSlope barrierIntercept
  ring

theorem supportWall_le_iff {U : Set Plane} {n : Plane} (hny : 0 < n.2) (x y : ℝ) :
    supportWall U n x ≤ y ↔ support U n - 1 ≤ coordDot (x, y) n := by
  unfold supportWall
  rw [div_le_iff₀ hny]
  unfold coordDot
  constructor <;> intro h <;> linarith

theorem le_supportWall_iff {U : Set Plane} {n : Plane} (hny : 0 < n.2) (x y : ℝ) :
    y ≤ supportWall U n x ↔ coordDot (x, y) n ≤ support U n - 1 := by
  unfold supportWall
  rw [le_div_iff₀ hny]
  unfold coordDot
  constructor <;> intro h <;> linarith

theorem cornerExpr_source_cases (ij : ι × ι) (v : Option ι → ℝ) :
    ((cornerExpr ij).source v = some ij.1 ∧ v (some ij.1) ≤ v (some ij.2)) ∨
      ((cornerExpr ij).source v = some ij.2 ∧ v (some ij.2) ≤ v (some ij.1)) := by
  by_cases h : v (some ij.1) ≤ v (some ij.2)
  · exact Or.inl ⟨by simp [cornerExpr, WallExpr.source, WallExpr.eval, h], h⟩
  · exact Or.inr ⟨by simp [cornerExpr, WallExpr.source, WallExpr.eval, h], le_of_not_ge h⟩

theorem nicheExpr_source_some {corners : List (ι × ι)} {v : Option ι → ℝ} {j : ι}
    (hsource : (nicheExpr corners).source v = some j) :
    ∃ ij ∈ corners, (cornerExpr ij).source v = some j := by
  revert hsource
  induction corners with
  | nil => intro hsource; simp [nicheExpr, WallExpr.source] at hsource
  | cons ij rest ih =>
    intro hsource
    change (if (cornerExpr ij).eval v ≤ (nicheExpr rest).eval v then
      (nicheExpr rest).source v else (cornerExpr ij).source v) = some j at hsource
    by_cases hle : (cornerExpr ij).eval v ≤ (nicheExpr rest).eval v
    · rw [if_pos hle] at hsource
      obtain ⟨kl, hkl, hk⟩ := ih hsource
      exact ⟨kl, List.mem_cons_of_mem _ hkl, hk⟩
    · rw [if_neg hle] at hsource
      exact ⟨ij, by simp, hsource⟩

end FinitePolygon

namespace AngularGrid

open FinitePolygon

def innerSourceSet (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : Set ℝ :=
  (barrierExpr (pairList grid) none).sourceSet (wallSlope (normal grid))
    (barrierIntercept (normal grid) (fun i => support U (normal grid i))) (some j)

theorem measurableSet_innerSourceSet (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) : MeasurableSet (innerSourceSet U grid j) := by
  classical
  exact WallExpr.measurableSet_sourceSet _ _ _ _

theorem innerSource_height (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    finiteBarrier U (normal grid) (pairList grid) none x = supportWall U (normal grid j) x := by
  rw [finiteBarrier_eq_eval (normal grid) _ (fun _ => rfl)]
  rw [WallExpr.eval_eq_source]
  change (barrierExpr (pairList grid) none).source
    (fun i => wallSlope (normal grid) i * x +
      barrierIntercept (normal grid) (fun j => support U (normal grid j)) i) = some j at hx
  rw [hx, ← supportWall_eq_affine]

theorem first_source_le_companion (U : Set Plane) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inl t)) :
    supportWall U (unitNormal t.val) x ≤ supportWall U (companionNormal t.val) x := by
  classical
  let v : Option (SourceIndex grid) → ℝ := fun i => wallSlope (normal grid) i * x +
    barrierIntercept (normal grid) (fun j => support U (normal grid j)) i
  have hsource : (nicheExpr (pairList grid)).source v = some (Sum.inl t) := hx
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some hsource
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases (Sum.inl s, Sum.inr s) v with h | h
  · have heq : t = s := Sum.inl.inj (Option.some.inj (hselected.symm.trans h.1))
    subst s
    simpa only [v, ← supportWall_eq_affine, normal] using h.2
  · have hfalse := hselected.symm.trans h.1
    simp at hfalse

/-- A point above the finite niche satisfies the actual corridor
alternative at every sampled angle, including both axis samples. -/
theorem above_niche_wall_alternative {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) {p : Plane} (hp0 : 0 ≤ p.2)
    (hpN : finiteBarrier U (normal grid) (pairList grid) none p.1 ≤ p.2)
    {s : QuarterAngle} (hs : s ∈ grid) :
    support U (unitNormal s) - 1 ≤ coordDot p (unitNormal s) ∨
      support U (companionNormal s) - 1 ≤ coordDot p (companionNormal s) := by
  classical
  by_cases hs0 : (s : ℝ) = 0
  · right
    have htop := hU.support_upward_le_one
    simpa only [hs0, companionNormal, Real.sin_zero, Real.cos_zero, neg_zero,
      coordDot, mul_zero, zero_add, mul_one] using (by linarith : support U (0, 1) - 1 ≤ p.2)
  by_cases hsL : (s : ℝ) = Real.pi / 2
  · left
    have htop := hU.support_upward_le_one
    simpa only [hsL, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      coordDot, mul_zero, zero_add, mul_one] using (by linarith : support U (0, 1) - 1 ≤ p.2)
  · have hsopen : 0 < (s : ℝ) ∧ (s : ℝ) < Real.pi / 2 :=
      ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0), lt_of_le_of_ne s.property.2 hsL⟩
    let t : InteriorPoint grid := ⟨s, Finset.mem_filter.mpr ⟨hs, hsopen⟩⟩
    have hmin := ((finiteNiche_le_iff U (normal grid) (pairList grid) p.1 p.2).mp hpN).2
      (Sum.inl t, Sum.inr t) (pair_mem_pairList grid t)
    rcases min_le_iff.mp hmin with h | h
    · left
      exact (supportWall_le_iff (normal_snd_pos grid (Sum.inl t)) p.1 p.2).mp h
    · right
      exact (supportWall_le_iff (normal_snd_pos grid (Sum.inr t)) p.1 p.2).mp h

def wallPoint (U : Set Plane) (t v : ℝ) : Plane :=
  (support U (unitNormal t) - 1) • unitNormal t + v • companionNormal t

theorem wallPoint_fst (U : Set Plane) (t v : ℝ) :
    (wallPoint U t v).1 = (support U (unitNormal t) - 1) * Real.cos t - v * Real.sin t := by
  simp only [wallPoint, unitNormal, companionNormal, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  ring

theorem dot_wallPoint_first (U : Set Plane) (t v s : ℝ) :
    coordDot (wallPoint U t v) (unitNormal s) =
      (support U (unitNormal t) - 1) * Real.cos (s - t) + v * Real.sin (s - t) := by
  change MovingSofaOptimality.dot
    ((support U (unitNormal t) - 1) • MovingSofaOptimality.uvec t + v • MovingSofaOptimality.vvec t) (MovingSofaOptimality.uvec s) = _
  rw [MovingSofaOptimality.dot_add_left, MovingSofaOptimality.dot_smul_left, MovingSofaOptimality.dot_smul_left,
    MovingSofaOptimality.dot_uvec_uvec, MovingSofaOptimality.dot_vvec_uvec', Real.cos_sub_comm t s]

theorem dot_wallPoint_companion (U : Set Plane) (t v s : ℝ) :
    coordDot (wallPoint U t v) (companionNormal s) =
      (support U (unitNormal t) - 1) * Real.sin (t - s) + v * Real.cos (t - s) := by
  change MovingSofaOptimality.dot
    ((support U (unitNormal t) - 1) • MovingSofaOptimality.uvec t + v • MovingSofaOptimality.vvec t) (MovingSofaOptimality.vvec s) = _
  rw [MovingSofaOptimality.dot_add_left, MovingSofaOptimality.dot_smul_left, MovingSofaOptimality.dot_smul_left,
    MovingSofaOptimality.dot_uvec_vvec', MovingSofaOptimality.dot_vvec_vvec]

theorem point_eq_wallPoint {U : Set Plane} {p : Plane} {t : ℝ}
    (hline : coordDot p (unitNormal t) = support U (unitNormal t) - 1) :
    p = wallPoint U t (coordDot p (companionNormal t)) := by
  have h := MovingSofaOptimality.eq_dot_uvec_smul_add p t
  change p = coordDot p (unitNormal t) • unitNormal t +
    coordDot p (companionNormal t) • companionNormal t at h
  rwa [hline] at h

def companionMinus (f gm δ : ℝ) : ℝ :=
  (gm - 1 - (f - 1) * Real.sin δ) / Real.cos δ

def companionPlus (f gp δ : ℝ) : ℝ :=
  (gp - 1 + (f - 1) * Real.sin δ) / Real.cos δ

def firstLo (f fp δ : ℝ) : ℝ :=
  (fp - 1 - (f - 1) * Real.cos δ) / Real.sin δ

def firstHi (f fm δ : ℝ) : ℝ :=
  ((f - 1) * Real.cos δ - fm + 1) / Real.sin δ

def neighborParameters (f g fm fp gm gp δ : ℝ) : Set ℝ :=
  Icc (min (companionMinus f gm δ) (companionPlus f gp δ)) (g - 1) ∪
    Icc (firstLo f fp δ) (firstHi f fm δ)

theorem mem_neighborParameters {f g fm fp gm gp δ v : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hv : v ≤ g - 1)
    (hminus : fm - 1 ≤ (f - 1) * Real.cos δ - v * Real.sin δ ∨
      gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ)
    (hplus : fp - 1 ≤ (f - 1) * Real.cos δ + v * Real.sin δ ∨
      gp - 1 ≤ -(f - 1) * Real.sin δ + v * Real.cos δ) :
    v ∈ neighborParameters f g fm fp gm gp δ := by
  by_cases hm : gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ
  · left
    refine ⟨(min_le_left _ _).trans ?_, hv⟩
    change (gm - 1 - (f - 1) * Real.sin δ) / Real.cos δ ≤ v
    rw [div_le_iff₀ hc]
    linarith
  by_cases hp : gp - 1 ≤ -(f - 1) * Real.sin δ + v * Real.cos δ
  · left
    refine ⟨(min_le_right _ _).trans ?_, hv⟩
    change (gp - 1 + (f - 1) * Real.sin δ) / Real.cos δ ≤ v
    rw [div_le_iff₀ hc]
    linarith
  · right
    have hm' := hminus.resolve_right hm
    have hp' := hplus.resolve_right hp
    constructor
    · change (fp - 1 - (f - 1) * Real.cos δ) / Real.sin δ ≤ v
      rw [div_le_iff₀ hs]
      linarith
    · change v ≤ ((f - 1) * Real.cos δ - fm + 1) / Real.sin δ
      rw [le_div_iff₀ hs]
      linarith

/-- Every actual first source lies in the two neighboring-wall parameter
intervals. This statement applies to every downward cap, independently of
polygonal maximization. -/
theorem first_source_neighbor_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inl t)) :
    ∃ v : ℝ, x = (support U (unitNormal t.val) - 1) * Real.cos t.val - v * Real.sin t.val ∧
      v ∈ neighborParameters (support U (unitNormal t.val)) (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) - δ))) (support U (unitNormal ((t.val : ℝ) + δ)))
        (support U (companionNormal ((t.val : ℝ) - δ)))
        (support U (companionNormal ((t.val : ℝ) + δ))) δ := by
  let y := supportWall U (unitNormal t.val) x
  let p : Plane := (x, y)
  let v := coordDot p (companionNormal t.val)
  have hy : finiteBarrier U (normal grid) (pairList grid) none x = y :=
    innerSource_height U grid (Sum.inl t) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (unitNormal t.val) = support U (unitNormal t.val) - 1 := by
    apply le_antisymm
    · exact (le_supportWall_iff (normal_snd_pos grid (Sum.inl t)) x y).mp le_rfl
    · exact (supportWall_le_iff (normal_snd_pos grid (Sum.inl t)) x y).mp le_rfl
  have hp : p = wallPoint U t.val v := point_eq_wallPoint hline
  have hv : v ≤ support U (companionNormal t.val) - 1 :=
    (le_supportWall_iff (normal_snd_pos grid (Sum.inr t)) x y).mp
      (first_source_le_companion U grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_niche_wall_alternative hU grid hy0 hy.le hsm
  have hp' := above_niche_wall_alternative hU grid hy0 hy.le hsp
  rw [hsmval, hp, dot_wallPoint_first, dot_wallPoint_companion,
    show (t.val : ℝ) - δ - (t.val : ℝ) = -δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) - δ) = δ by ring,
    Real.cos_neg, Real.sin_neg] at hm
  rw [hspval, hp, dot_wallPoint_first, dot_wallPoint_companion,
    show (t.val : ℝ) + δ - (t.val : ℝ) = δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) + δ) = -δ by ring,
    Real.sin_neg, Real.cos_neg] at hp'
  refine ⟨v, ?_, mem_neighborParameters hc hs hv ?_ ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, wallPoint_fst] using h
  · rcases hm with h | h
    · left
      nlinarith
    · exact Or.inr h
  · rcases hp' with h | h
    · exact Or.inl h
    · right
      nlinarith

end AngularGrid

end AmbidextrousSofa
