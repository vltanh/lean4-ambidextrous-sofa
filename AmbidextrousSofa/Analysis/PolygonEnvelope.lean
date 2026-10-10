module

public import AmbidextrousSofa.Analysis.PolygonVariation

@[expose] public section

/-!
# Finite expressions for actual polygon roofs and hallway barriers

The outer roof and the inner wall system use the same normal indices. A
source that occurs in several corners or also supplies the proper terminal
wall is represented by the same leaf. This keeps equal slopes from being
mistaken for different moving sources.

The zero leaf is the top wall in the outer expression and the baseline in
the inner expression. All other leaves are actual supporting halfplanes.
On the actual polygon projection the outer expression equals `capRoof`.
The inner expression equals the literal maximum of the sampled physical
corners and the terminal wall. No contact ordering is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

def roofExprList : List ι → WallExpr (Option ι)
  | [] => WallExpr.leaf none
  | i :: is => WallExpr.minimum (WallExpr.leaf (some i)) (roofExprList is)

def roofExpr [Fintype ι] : WallExpr (Option ι) :=
  roofExprList (Finset.univ.toList)

theorem le_eval_roofExprList_iff (is : List ι) (v : Option ι → ℝ) (y : ℝ) :
    y ≤ (roofExprList is).eval v ↔ y ≤ v none ∧ ∀ i ∈ is, y ≤ v (some i) := by
  induction is with
  | nil => simp [roofExprList, WallExpr.eval]
  | cons i is ih =>
    rw [roofExprList, WallExpr.eval, le_min_iff, ih]
    constructor
    · rintro ⟨hi, hnone, hrest⟩
      refine ⟨hnone, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hrest j hj
    · rintro ⟨hnone, hall⟩
      exact ⟨hall i (by simp), hnone, fun j hj => hall j (List.mem_cons_of_mem _ hj)⟩

theorem le_eval_roofExpr_iff [Fintype ι] (v : Option ι → ℝ) (y : ℝ) :
    y ≤ (roofExpr (ι := ι)).eval v ↔ y ≤ v none ∧ ∀ i, y ≤ v (some i) := by
  rw [roofExpr, le_eval_roofExprList_iff]
  simp only [Finset.mem_toList, Finset.mem_univ, forall_true_left]

def wallSlope (normal : ι → Plane) : Option ι → ℝ
  | none => 0
  | some i => -(normal i).1 / (normal i).2

def roofIntercept (normal : ι → Plane) (height : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => height i / (normal i).2

def barrierIntercept (normal : ι → Plane) (height : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => (height i - 1) / (normal i).2

def outwardVelocity [DecidableEq ι] (normal : ι → Plane) (j : ι) : Option ι → ℝ
  | none => 0
  | some i => if i = j then 1 / (normal i).2 else 0

/-- Distinct nonvertical supporting directions and the top leaf have
distinct spatial slopes. This verifies the finite-envelope hypothesis
directly from the displayed normal geometry. -/
theorem wallSlope_injective (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hnx : ∀ i, (normal i).1 ≠ 0)
    (hdet : ∀ i j, i ≠ j →
      (normal i).1 * (normal j).2 - (normal i).2 * (normal j).1 ≠ 0) :
    Function.Injective (wallSlope normal) := by
  intro i j heq
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      have hzero : -(normal j).1 / (normal j).2 = 0 := heq.symm
      have hnxzero := (div_eq_zero_iff.mp hzero).resolve_right (hnormal j).ne'
      exact (hnx j (neg_eq_zero.mp hnxzero)).elim
  | some i =>
    cases j with
    | none =>
      have hzero : -(normal i).1 / (normal i).2 = 0 := heq
      have hnxzero := (div_eq_zero_iff.mp hzero).resolve_right (hnormal i).ne'
      exact (hnx i (neg_eq_zero.mp hnxzero)).elim
    | some j =>
      congr 1
      by_contra hij
      have hcross := (div_eq_div_iff (hnormal i).ne' (hnormal j).ne').mp heq
      apply hdet i j hij
      nlinarith

def roofEnvelope [Fintype ι] (normal : ι → Plane) (height : ι → ℝ) (x : ℝ) : ℝ :=
  (roofExpr (ι := ι)).eval (fun i => wallSlope normal i * x + roofIntercept normal height i)

theorem le_upper_line_iff {n : Plane} (hny : 0 < n.2) (height x y : ℝ) :
    y ≤ -n.1 / n.2 * x + height / n.2 ↔ coordDot (x, y) n ≤ height := by
  rw [show -n.1 / n.2 * x + height / n.2 = (height - x * n.1) / n.2 by ring,
    le_div_iff₀ hny]
  unfold coordDot
  constructor <;> intro h <;> linarith

theorem le_roofEnvelope_iff [Fintype ι] (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2) (x y : ℝ) :
    y ≤ roofEnvelope normal height x ↔
      y ≤ 1 ∧ ∀ i, coordDot (x, y) (normal i) ≤ height i := by
  rw [roofEnvelope, le_eval_roofExpr_iff]
  simp only [wallSlope, roofIntercept, zero_mul, zero_add]
  have hline : ∀ i, y ≤ -(normal i).1 / (normal i).2 * x + height i / (normal i).2 ↔
      coordDot (x, y) (normal i) ≤ height i :=
    fun i => le_upper_line_iff (hnormal i) (height i) x y
  simp_rw [hline]

theorem mem_upperPolygon_iff_roofEnvelope [Fintype ι] (l r : ℝ)
    (normal : ι → Plane) (height : ι → ℝ) (hnormal : ∀ i, 0 < (normal i).2) (x y : ℝ) :
    (x, y) ∈ upperPolygon l r normal height ↔
      x ∈ Icc l r ∧ 0 ≤ y ∧ y ≤ roofEnvelope normal height x := by
  rw [mem_upperPolygon_iff, le_roofEnvelope_iff normal height hnormal]
  simp only [mem_Icc, Prod.fst, Prod.snd]
  tauto

/-- The finite upper expression is the actual fiber supremum, including
the vertical endpoint faces. -/
theorem capRoof_upperPolygon [Fintype ι] (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    {x : ℝ} (hx : x ∈ Icc l r) :
    capRoof (upperPolygon l r normal height) x = roofEnvelope normal height x := by
  have hproj : x ∈ horizontalProjection (upperPolygon l r normal height) := by
    rw [horizontalProjection_upperPolygon l r normal height hbaseline]
    exact hx
  have hzero : 0 ≤ roofEnvelope normal height x :=
    (le_roofEnvelope_iff normal height hnormal x 0).mpr ⟨by norm_num, hbaseline x hx⟩
  apply le_antisymm
  · exact ((mem_upperPolygon_iff_roofEnvelope l r normal height hnormal _ _).mp
      (capRoof_mem (isCompact_upperPolygon l r normal height) hproj)).2.2
  · apply le_capRoof (isCompact_upperPolygon l r normal height)
    exact (mem_upperPolygon_iff_roofEnvelope l r normal height hnormal _ _).mpr
      ⟨hx, hzero, le_rfl⟩

theorem continuous_roofEnvelope [Fintype ι] (normal : ι → Plane) (height : ι → ℝ) :
    Continuous (roofEnvelope normal height) :=
  (roofExpr (ι := ι)).continuous_eval (fun _ => by fun_prop)

theorem roofEnvelope_update [Fintype ι] [DecidableEq ι]
    (normal : ι → Plane) (height : ι → ℝ) (j : ι) (ε : ℝ) :
    roofEnvelope normal (Function.update height j (height j + ε)) =
      (roofExpr (ι := ι)).affineEnvelope (wallSlope normal) (roofIntercept normal height)
        (outwardVelocity normal j) ε := by
  funext x
  unfold roofEnvelope WallExpr.affineEnvelope
  congr 1
  funext i
  cases i with
  | none => simp [wallSlope, roofIntercept, outwardVelocity]
  | some i =>
    by_cases hij : i = j
    · subst i
      simp only [wallSlope, roofIntercept, outwardVelocity, Function.update_same, if_pos rfl]
      ring
    · simp [wallSlope, roofIntercept, outwardVelocity, Function.update_of_ne hij, hij]

/-- One inner wall written without an angular coordinate chart. -/
def supportWall (U : Set Plane) (n : Plane) (x : ℝ) : ℝ :=
  (support U n - 1 - x * n.1) / n.2

theorem supportWall_unitNormal (U : Set Plane) (θ x : ℝ) :
    supportWall U (unitNormal θ) x = firstWall U θ x := rfl

theorem supportWall_companionNormal (U : Set Plane) (θ x : ℝ) :
    supportWall U (companionNormal θ) x = secondWall U θ x := by
  unfold supportWall secondWall companionNormal
  congr 1
  ring

def cornerExpr (ij : ι × ι) : WallExpr (Option ι) :=
  WallExpr.minimum (WallExpr.leaf (some ij.1)) (WallExpr.leaf (some ij.2))

def nicheExpr : List (ι × ι) → WallExpr (Option ι)
  | [] => WallExpr.leaf none
  | ij :: rest => WallExpr.maximum (cornerExpr ij) (nicheExpr rest)

def barrierExpr (corners : List (ι × ι)) (terminal : Option ι) : WallExpr (Option ι) :=
  match terminal with
  | none => nicheExpr corners
  | some j => WallExpr.maximum (nicheExpr corners) (WallExpr.leaf (some j))

/-- Literal sampled corners, always clipped from below at zero. -/
def finiteNiche (U : Set Plane) (normal : ι → Plane) : List (ι × ι) → ℝ → ℝ
  | [], _ => 0
  | ij :: rest, x => max (min (supportWall U (normal ij.1) x)
      (supportWall U (normal ij.2) x)) (finiteNiche U normal rest x)

/-- A proper terminal wall remains a whole wall. It shares its source index
with any corner in which the same support is used. -/
def finiteBarrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) : ℝ :=
  match terminal with
  | none => finiteNiche U normal corners x
  | some j => max (finiteNiche U normal corners x) (supportWall U (normal j) x)

theorem finiteNiche_le_iff (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (x b : ℝ) :
    finiteNiche U normal corners x ≤ b ↔ 0 ≤ b ∧ ∀ ij ∈ corners,
      min (supportWall U (normal ij.1) x) (supportWall U (normal ij.2) x) ≤ b := by
  induction corners with
  | nil => simp [finiteNiche]
  | cons ij rest ih =>
    rw [finiteNiche, max_le_iff, ih]
    constructor
    · rintro ⟨hij, hb, hrest⟩
      refine ⟨hb, ?_⟩
      intro kl hkl
      rcases List.mem_cons.mp hkl with rfl | hkl
      · exact hij
      · exact hrest kl hkl
    · rintro ⟨hb, hall⟩
      exact ⟨hall ij (by simp), hb, fun kl hkl => hall kl (List.mem_cons_of_mem _ hkl)⟩

theorem finiteNiche_nonneg (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (x : ℝ) : 0 ≤ finiteNiche U normal corners x := by
  induction corners with
  | nil => exact le_rfl
  | cons ij rest ih => exact ih.trans (le_max_right _ _)

theorem finiteBarrier_nonneg (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    0 ≤ finiteBarrier U normal corners terminal x := by
  cases terminal with
  | none => exact finiteNiche_nonneg U normal corners x
  | some j => exact (finiteNiche_nonneg U normal corners x).trans (le_max_left _ _)

theorem finiteNiche_eq_eval {U : Set Plane} (normal : ι → Plane) (height : ι → ℝ)
    (hexact : ∀ i, support U (normal i) = height i) (corners : List (ι × ι)) (x : ℝ) :
    finiteNiche U normal corners x = (nicheExpr corners).eval
      (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
  have hline : ∀ i, supportWall U (normal i) x =
      wallSlope normal (some i) * x + barrierIntercept normal height (some i) := by
    intro i
    unfold supportWall wallSlope barrierIntercept
    rw [hexact i]
    ring
  induction corners with
  | nil => simp [finiteNiche, nicheExpr, WallExpr.eval, wallSlope, barrierIntercept]
  | cons ij rest ih =>
    simp only [finiteNiche, nicheExpr, cornerExpr, WallExpr.eval, hline, ih]

theorem finiteBarrier_eq_eval {U : Set Plane} (normal : ι → Plane) (height : ι → ℝ)
    (hexact : ∀ i, support U (normal i) = height i)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    finiteBarrier U normal corners terminal x = (barrierExpr corners terminal).eval
      (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
  cases terminal with
  | none => exact finiteNiche_eq_eval normal height hexact corners x
  | some j =>
    simp only [finiteBarrier, barrierExpr, WallExpr.eval,
      finiteNiche_eq_eval normal height hexact]
    congr 1
    unfold supportWall wallSlope barrierIntercept
    rw [hexact j]
    ring

theorem continuous_finiteBarrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (finiteBarrier U normal corners terminal) := by
  have heq : finiteBarrier U normal corners terminal = fun x =>
      (barrierExpr corners terminal).eval
        (fun i => wallSlope normal i * x + barrierIntercept normal (fun i => support U (normal i)) i) := by
    funext x
    exact finiteBarrier_eq_eval normal _ (fun _ => rfl) corners terminal x
  rw [heq]
  exact (barrierExpr corners terminal).continuous_eval (fun _ => by fun_prop)

theorem finiteBarrier_eq_affineEnvelope_update [DecidableEq ι]
    {U : Set Plane} (normal : ι → Plane) (height : ι → ℝ) (j : ι) (ε : ℝ)
    (hexact : ∀ i, support U (normal i) = Function.update height j (height j + ε) i)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteBarrier U normal corners terminal =
      (barrierExpr corners terminal).affineEnvelope (wallSlope normal)
        (barrierIntercept normal height) (outwardVelocity normal j) ε := by
  funext x
  rw [finiteBarrier_eq_eval normal _ hexact]
  unfold WallExpr.affineEnvelope
  congr 1
  funext i
  cases i with
  | none => simp [wallSlope, barrierIntercept, outwardVelocity]
  | some i =>
    by_cases hij : i = j
    · subst i
      simp only [wallSlope, barrierIntercept, outwardVelocity, Function.update_same, if_pos rfl]
      ring
    · simp [wallSlope, barrierIntercept, outwardVelocity, Function.update_of_ne hij, hij]

/-- Actual finite barriers lie below the whole-angle barrier whenever every
sample is an actual visited corner and the terminal source is the true
terminal first wall. -/
theorem finiteBarrier_le_partialBarrier {U : Set Plane} (hU : IsCompact U)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι)
    {α : ℝ} (hα : α ≤ Real.pi / 2)
    (hcorners : ∀ ij ∈ corners, ∃ θ ∈ Ioo 0 α,
      normal ij.1 = unitNormal θ ∧ normal ij.2 = companionNormal θ)
    (hterminal : ∀ j, terminal = some j → normal j = unitNormal α) (x : ℝ) :
    finiteBarrier U normal corners terminal x ≤ partialBarrier U α x := by
  have hniche_all : ∀ is : List (ι × ι),
      (∀ ij ∈ is, ∃ θ ∈ Ioo 0 α,
        normal ij.1 = unitNormal θ ∧ normal ij.2 = companionNormal θ) →
      finiteNiche U normal is x ≤ sweptNiche U α x := by
    intro is
    induction is with
    | nil => exact fun _ => sweptNiche_nonneg U α x
    | cons ij rest ih =>
      intro hlist
      obtain ⟨θ, hθ, hfirst, hsecond⟩ := hlist ij (by simp)
      apply max_le
      · rw [hfirst, hsecond, supportWall_unitNormal, supportWall_companionNormal]
        exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU hα x) hθ
      · exact ih (fun ij hij => hlist ij (List.mem_cons_of_mem _ hij))
  have hniche := hniche_all corners hcorners
  cases terminal with
  | none => exact hniche.trans (le_max_left _ _)
  | some j =>
    apply max_le (hniche.trans (le_max_left _ _))
    rw [hterminal j rfl, supportWall_unitNormal]
    exact le_max_right _ _

theorem horizontalLeft_upperPolygon {l r : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hlr : l ≤ r)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalLeft (upperPolygon l r normal height) = l := by
  rw [horizontalLeft, horizontalProjection_upperPolygon l r normal height hbaseline]
  exact csInf_Icc hlr

theorem horizontalRight_upperPolygon {l r : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hlr : l ≤ r)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalRight (upperPolygon l r normal height) = r := by
  rw [horizontalRight, horizontalProjection_upperPolygon l r normal height hbaseline]
  exact csSup_Icc hlr

/-- The finite geometric score uses the actual projection endpoints and
actual support values of its cap. -/
def finiteSpatialScore (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  intervalSpatialScore (capRoof U) (finiteBarrier U normal corners terminal)
    (horizontalLeft U) (horizontalRight U)

theorem intervalSpatialScore_congr_roof {roof roof' niche : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hroof : EqOn roof roof' (Icc l r)) :
    intervalSpatialScore roof niche l r = intervalSpatialScore roof' niche l r := by
  have hlmid : l ≤ l + (r - l) / 4 := by linarith
  have hrmid : r - (r - l) / 4 ≤ r := by linarith
  have hfirst : (∫ x in l..(l + (r - l) / 4), roof x) =
      ∫ x in l..(l + (r - l) / 4), roof' x := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hlmid]
    intro x hx
    exact hroof ⟨hx.1, by linarith [hx.2]⟩
  have hlast : (∫ x in (r - (r - l) / 4)..r, roof x) =
      ∫ x in (r - (r - l) / 4)..r, roof' x := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hrmid]
    intro x hx
    exact hroof ⟨by linarith [hx.1], hx.2⟩
  unfold intervalSpatialScore
  rw [hfirst, hlast]

/-- Actual polygon geometry, rather than an abstract envelope hypothesis,
identifies all terms of the finite spatial objective. -/
theorem finiteSpatialScore_upperPolygon [Fintype ι] {l r : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hlr : l ≤ r)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteSpatialScore (upperPolygon l r normal height) normal corners terminal =
      intervalSpatialScore (roofEnvelope normal height)
        (fun x => (barrierExpr corners terminal).eval
          (fun i => wallSlope normal i * x + barrierIntercept normal height i)) l r := by
  unfold finiteSpatialScore
  rw [horizontalLeft_upperPolygon normal height hlr hbaseline,
    horizontalRight_upperPolygon normal height hlr hbaseline]
  have hbarrier : finiteBarrier (upperPolygon l r normal height) normal corners terminal =
      fun x => (barrierExpr corners terminal).eval
        (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
    funext x
    exact finiteBarrier_eq_eval normal height hexact corners terminal x
  rw [hbarrier]
  exact intervalSpatialScore_congr_roof hlr
    (fun _ hx => capRoof_upperPolygon l r normal height hnormal hbaseline hx)

end FinitePolygon

end AmbidextrousSofa
