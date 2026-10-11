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
  induction is <;> simp [roofExprList, WallExpr.eval, *, and_left_comm]

theorem le_eval_roofExpr_iff [Fintype ι] (v : Option ι → ℝ) (y : ℝ) :
    y ≤ (roofExpr (ι := ι)).eval v ↔ y ≤ v none ∧ ∀ i, y ≤ v (some i) := by
  simp [roofExpr, le_eval_roofExprList_iff]

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
  rintro (_ | i) (_ | j) heq
  · rfl
  · simp [wallSlope, neg_div, hnx j, (hnormal j).ne'] at heq
  · simp [wallSlope, neg_div, hnx i, (hnormal i).ne'] at heq
  · congr 1
    by_contra hij
    rw [wallSlope, wallSlope, div_eq_div_iff (hnormal i).ne' (hnormal j).ne'] at heq
    exact hdet i j hij (by linarith)

def roofEnvelope [Fintype ι] (normal : ι → Plane) (height : ι → ℝ) (x : ℝ) : ℝ :=
  (roofExpr (ι := ι)).eval (fun i => wallSlope normal i * x + roofIntercept normal height i)

theorem le_roofEnvelope_iff [Fintype ι] (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2) (x y : ℝ) :
    y ≤ roofEnvelope normal height x ↔
      y ≤ 1 ∧ ∀ i, coordDot (x, y) (normal i) ≤ height i := by
  simp only [roofEnvelope, le_eval_roofExpr_iff, wallSlope, roofIntercept, zero_mul, zero_add]
  refine and_congr_right' (forall_congr' fun i => ?_)
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ (hnormal i), coordDot]
  constructor <;> intro h <;> linarith

/-- The finite upper expression is the actual fiber supremum, including
the vertical endpoint faces. -/
theorem capRoof_upperPolygon [Fintype ι] (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    {x : ℝ} (hx : x ∈ Icc l r) :
    capRoof (upperPolygon l r normal height) x = roofEnvelope normal height x := by
  have hK := isCompact_upperPolygon l r normal height
  have hmem (y : ℝ) : (x, y) ∈ upperPolygon l r normal height ↔
      0 ≤ y ∧ y ≤ roofEnvelope normal height x := by
    rw [mem_upperPolygon_iff, le_roofEnvelope_iff normal height hnormal]
    simp only [mem_Icc, hx]
    tauto
  refine le_antisymm ((hmem _).mp (capRoof_mem hK ?_)).2
    (le_capRoof hK ((hmem _).mpr ⟨?_, le_rfl⟩))
  · rwa [horizontalProjection_upperPolygon l r normal height hbaseline]
  · exact (le_roofEnvelope_iff normal height hnormal x 0).mpr ⟨zero_le_one, hbaseline x hx⟩

theorem continuous_roofEnvelope [Fintype ι] (normal : ι → Plane) (height : ι → ℝ) :
    Continuous (roofEnvelope normal height) :=
  (roofExpr (ι := ι)).continuous_eval (fun _ => by fun_prop)

theorem roofEnvelope_update [Fintype ι] [DecidableEq ι]
    (normal : ι → Plane) (height : ι → ℝ) (j : ι) (ε : ℝ) :
    roofEnvelope normal (Function.update height j (height j + ε)) =
      (roofExpr (ι := ι)).affineEnvelope (wallSlope normal) (roofIntercept normal height)
        (outwardVelocity normal j) ε := by
  funext x
  refine congrArg (roofExpr (ι := ι)).eval (funext fun i => ?_)
  rcases i with _ | i
  · simp [wallSlope, roofIntercept, outwardVelocity]
  rcases eq_or_ne i j with rfl | hij <;> simp [wallSlope, roofIntercept, outwardVelocity, *]
  ring

/-- One inner wall written without an angular coordinate chart. -/
def supportWall (U : Set Plane) (n : Plane) (x : ℝ) : ℝ :=
  (support U n - 1 - x * n.1) / n.2

theorem supportWall_unitNormal (U : Set Plane) (θ x : ℝ) :
    supportWall U (unitNormal θ) x = firstWall U θ x := rfl

theorem supportWall_companionNormal (U : Set Plane) (θ x : ℝ) :
    supportWall U (companionNormal θ) x = secondWall U θ x := by
  simp only [supportWall, secondWall, companionNormal]; ring

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
  induction corners <;> simp [finiteNiche, *, and_left_comm]

theorem finiteNiche_nonneg (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (x : ℝ) : 0 ≤ finiteNiche U normal corners x :=
  ((finiteNiche_le_iff U normal corners x _).mp le_rfl).1

theorem finiteBarrier_nonneg (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    0 ≤ finiteBarrier U normal corners terminal x := by
  cases terminal <;> simp [finiteBarrier, finiteNiche_nonneg]

theorem finiteBarrier_eq_eval {U : Set Plane} (normal : ι → Plane) (height : ι → ℝ)
    (hexact : ∀ i, support U (normal i) = height i)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    finiteBarrier U normal corners terminal x = (barrierExpr corners terminal).eval
      (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
  have hline (i : ι) : supportWall U (normal i) x =
      wallSlope normal (some i) * x + barrierIntercept normal height (some i) := by
    simp only [supportWall, wallSlope, barrierIntercept, hexact]; ring
  have hniche : finiteNiche U normal corners x = (nicheExpr corners).eval
      (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
    induction corners <;>
      simp [finiteNiche, nicheExpr, cornerExpr, WallExpr.eval, wallSlope, barrierIntercept, *]
  cases terminal <;> simp only [finiteBarrier, barrierExpr, WallExpr.eval, hniche, hline]

theorem continuous_finiteBarrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (finiteBarrier U normal corners terminal) := by
  rw [funext (finiteBarrier_eq_eval normal _ (fun _ => rfl) corners terminal)]
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
  refine congrArg (barrierExpr corners terminal).eval (funext fun i => ?_)
  rcases i with _ | i
  · simp [wallSlope, barrierIntercept, outwardVelocity]
  rcases eq_or_ne i j with rfl | hij <;> simp [wallSlope, barrierIntercept, outwardVelocity, *]
  ring

theorem horizontalLeft_upperPolygon {l r : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hlr : l ≤ r)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalLeft (upperPolygon l r normal height) = l := by
  rw [horizontalLeft, horizontalProjection_upperPolygon _ _ _ _ hbaseline, csInf_Icc hlr]

theorem horizontalRight_upperPolygon {l r : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hlr : l ≤ r)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalRight (upperPolygon l r normal height) = r := by
  rw [horizontalRight, horizontalProjection_upperPolygon _ _ _ _ hbaseline, csSup_Icc hlr]

/-- The finite geometric score uses the actual projection endpoints and
actual support values of its cap. -/
def finiteSpatialScore (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  intervalSpatialScore (capRoof U) (finiteBarrier U normal corners terminal)
    (horizontalLeft U) (horizontalRight U)

theorem intervalSpatialScore_congr_roof {roof roof' niche : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hroof : EqOn roof roof' (Icc l r)) :
    intervalSpatialScore roof niche l r = intervalSpatialScore roof' niche l r := by
  unfold intervalSpatialScore
  congr 2 <;> refine intervalIntegral.integral_congr (hroof.mono (uIcc_subset_Icc ?_ ?_)) <;>
    constructor <;> linarith

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
  rw [finiteSpatialScore, horizontalLeft_upperPolygon normal height hlr hbaseline,
    horizontalRight_upperPolygon normal height hlr hbaseline,
    funext (finiteBarrier_eq_eval normal height hexact corners terminal)]
  exact intervalSpatialScore_congr_roof hlr
    (fun _ hx => capRoof_upperPolygon l r normal height hnormal hbaseline hx)

end FinitePolygon

end AmbidextrousSofa
