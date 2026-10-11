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
  unfold supportWall wallSlope barrierIntercept; ring

theorem supportWall_le_iff {U : Set Plane} {n : Plane} (hny : 0 < n.2) (x y : ℝ) :
    supportWall U n x ≤ y ↔ support U n - 1 ≤ coordDot (x, y) n :=
  (div_le_iff₀ hny).trans sub_le_iff_le_add'

theorem le_supportWall_iff {U : Set Plane} {n : Plane} (hny : 0 < n.2) (x y : ℝ) :
    y ≤ supportWall U n x ↔ coordDot (x, y) n ≤ support U n - 1 :=
  (le_div_iff₀ hny).trans le_sub_iff_add_le'

theorem cornerExpr_source_cases (ij : ι × ι) (v : Option ι → ℝ) :
    ((cornerExpr ij).source v = some ij.1 ∧ v (some ij.1) ≤ v (some ij.2)) ∨
      ((cornerExpr ij).source v = some ij.2 ∧ v (some ij.2) ≤ v (some ij.1)) := by
  by_cases h : v (some ij.1) ≤ v (some ij.2) <;>
    simp [cornerExpr, WallExpr.source, WallExpr.eval, h, le_of_not_ge]

theorem nicheExpr_source_some {corners : List (ι × ι)} {v : Option ι → ℝ} {j : ι}
    (hsource : (nicheExpr corners).source v = some j) :
    ∃ ij ∈ corners, (cornerExpr ij).source v = some j := by
  induction corners with
  | nil => simp [nicheExpr, WallExpr.source] at hsource
  | cons ij rest ih =>
    rw [nicheExpr, WallExpr.source] at hsource
    split_ifs at hsource
    · exact (ih hsource).imp fun _ h => ⟨List.mem_cons_of_mem _ h.1, h.2⟩
    · exact ⟨ij, List.mem_cons_self, hsource⟩

end FinitePolygon

namespace AngularGrid

open FinitePolygon

def innerSourceSet (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : Set ℝ :=
  (barrierExpr (pairList grid) none).sourceSet (wallSlope (normal grid))
    (barrierIntercept (normal grid) (fun i => support U (normal grid i))) (some j)

theorem innerSource_height (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    finiteBarrier U (normal grid) (pairList grid) none x = supportWall U (normal grid j) x := by
  have hx : (barrierExpr (pairList grid) none).source _ = some j := hx
  rw [finiteBarrier_eq_eval (normal grid) _ (fun _ => rfl), WallExpr.eval_eq_source, hx,
    ← supportWall_eq_affine]

theorem first_source_le_companion (U : Set Plane) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inl t)) :
    supportWall U (unitNormal t.val) x ≤ supportWall U (companionNormal t.val) x := by
  let v : Option (SourceIndex grid) → ℝ := fun i => wallSlope (normal grid) i * x +
    barrierIntercept (normal grid) (fun j => support U (normal grid j)) i
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some (v := v) hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases (Sum.inl s, Sum.inr s) v with h | h <;> rw [h.1] at hselected
  · obtain rfl : s = t := by simpa using hselected
    simp only [v, ← supportWall_eq_affine] at h
    exact h.2
  · simp at hselected

/-- A point above the finite niche satisfies the actual corridor
alternative at every sampled angle, including both axis samples. -/
theorem above_niche_wall_alternative {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) {p : Plane} (hp0 : 0 ≤ p.2)
    (hpN : finiteBarrier U (normal grid) (pairList grid) none p.1 ≤ p.2)
    {s : QuarterAngle} (hs : s ∈ grid) :
    support U (unitNormal s) - 1 ≤ coordDot p (unitNormal s) ∨
      support U (companionNormal s) - 1 ≤ coordDot p (companionNormal s) := by
  have htop := hU.support_upward_le_one
  by_cases hs0 : (s : ℝ) = 0
  · right; simp [hs0, companionNormal, coordDot]; linarith
  by_cases hsL : (s : ℝ) = Real.pi / 2
  · left; simp [hsL, unitNormal, coordDot]; linarith
  let t : InteriorPoint grid := ⟨s, Finset.mem_filter.mpr
    ⟨hs, lt_of_le_of_ne s.2.1 (Ne.symm hs0), lt_of_le_of_ne s.2.2 hsL⟩⟩
  exact (min_le_iff.mp (((finiteNiche_le_iff U (normal grid) (pairList grid) p.1 p.2).mp hpN).2
      (Sum.inl t, Sum.inr t) (pair_mem_pairList grid t))).imp
    (supportWall_le_iff (normal_snd_pos grid (Sum.inl t)) p.1 p.2).mp
    (supportWall_le_iff (normal_snd_pos grid (Sum.inr t)) p.1 p.2).mp

def wallPoint (U : Set Plane) (t v : ℝ) : Plane :=
  (support U (unitNormal t) - 1) • unitNormal t + v • companionNormal t

theorem wallPoint_fst (U : Set Plane) (t v : ℝ) :
    (wallPoint U t v).1 = (support U (unitNormal t) - 1) * Real.cos t - v * Real.sin t := by
  simp [wallPoint, unitNormal, companionNormal]; ring

theorem dot_wallPoint_first (U : Set Plane) (t v s : ℝ) :
    coordDot (wallPoint U t v) (unitNormal s) =
      (support U (unitNormal t) - 1) * Real.cos (s - t) + v * Real.sin (s - t) := by
  simp [wallPoint, coordDot, unitNormal, companionNormal, Real.cos_sub, Real.sin_sub]; ring

theorem dot_wallPoint_companion (U : Set Plane) (t v s : ℝ) :
    coordDot (wallPoint U t v) (companionNormal s) =
      (support U (unitNormal t) - 1) * Real.sin (t - s) + v * Real.cos (t - s) := by
  simp [wallPoint, coordDot, unitNormal, companionNormal, Real.cos_sub, Real.sin_sub]; ring

theorem point_eq_wallPoint {U : Set Plane} {p : Plane} {t : ℝ}
    (hline : coordDot p (unitNormal t) = support U (unitNormal t) - 1) :
    p = wallPoint U t (coordDot p (companionNormal t)) := by
  rw [wallPoint, ← hline]; exact MovingSofaOptimality.eq_dot_uvec_smul_add p t

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
  simp only [neighborParameters, companionMinus, companionPlus, firstLo, firstHi, mem_union,
    mem_Icc, min_le_iff, div_le_iff₀ hc, div_le_iff₀ hs, le_div_iff₀ hs, hv, and_true]
  rcases hminus with h | h
  · rcases hplus with h' | h'
    · exact .inr ⟨by linarith, by linarith⟩
    · exact .inl (.inr (by linarith))
  · exact .inl (.inl (by linarith))

def neighborFeasible (f g fm fp gm gp δ : ℝ) : Set ℝ :=
  {v | v ≤ g - 1 ∧
    (fm - 1 ≤ (f - 1) * Real.cos δ - v * Real.sin δ ∨
      gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ) ∧
    (fp - 1 ≤ (f - 1) * Real.cos δ + v * Real.sin δ ∨
      gp - 1 ≤ -(f - 1) * Real.sin δ + v * Real.cos δ)}

theorem first_source_neighbor_feasible {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inl t)) :
    ∃ v : ℝ, x = (support U (unitNormal t.val) - 1) * Real.cos t.val - v * Real.sin t.val ∧
      v ∈ neighborFeasible (support U (unitNormal t.val)) (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) - δ))) (support U (unitNormal ((t.val : ℝ) + δ)))
        (support U (companionNormal ((t.val : ℝ) - δ)))
        (support U (companionNormal ((t.val : ℝ) + δ))) δ := by
  let p : Plane := (x, supportWall U (unitNormal t.val) x)
  have hy : finiteBarrier U (normal grid) (pairList grid) none p.1 = p.2 :=
    innerSource_height U grid (Sum.inl t) hx
  have hp : p = wallPoint U t.val (coordDot p (companionNormal t.val)) :=
    point_eq_wallPoint (le_antisymm
      ((le_supportWall_iff (normal_snd_pos grid (Sum.inl t)) _ _).mp le_rfl)
      ((supportWall_le_iff (normal_snd_pos grid (Sum.inl t)) _ _).mp le_rfl))
  have hv : coordDot p (companionNormal t.val) ≤ support U (companionNormal t.val) - 1 :=
    (le_supportWall_iff (normal_snd_pos grid (Sum.inr t)) _ _).mp
      (first_source_le_companion U grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_niche_wall_alternative hU grid (hy ▸ finiteBarrier_nonneg ..) hy.le hsm
  have hp' := above_niche_wall_alternative hU grid (hy ▸ finiteBarrier_nonneg ..) hy.le hsp
  rw [hp] at hm hp'
  simp [hsmval, hspval, dot_wallPoint_first, dot_wallPoint_companion] at hm hp'
  refine ⟨_, ?_, hv, hm.imp (fun h => by linarith) (fun h => by linarith),
    hp'.imp (fun h => by linarith) fun h => by linarith⟩
  simpa only [wallPoint_fst] using congrArg Prod.fst hp

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
        (support U (companionNormal ((t.val : ℝ) + δ))) δ :=
  let ⟨v, hxv, hv, hm, hp⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx
  ⟨v, hxv, mem_neighborParameters hc hs hv hm hp⟩

end AngularGrid

end AmbidextrousSofa
