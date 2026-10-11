module

public import AmbidextrousSofa.Analysis.PolygonEnvelope

@[expose] public section

/-!
# Exposure inequality at an actual selected polygonal maximum

The maximization hypothesis concerns actual downward caps and their actual
support values. A positive floating facet supplies an admissible outward
family by `exists_outward_support_variation`. The finite roof and physical
barrier formulas then identify its ordinary derivative. The selection
penalty is a displayed finite quadratic sum, whose derivative is proved
here. Thus the exposure inequality is a consequence of maximization, not
an additional variational certificate.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

def heightPenalty [Fintype ι] (weight target height : ι → ℝ) : ℝ :=
  ∑ i, weight i * (height i - target i) ^ 2

def sampledPenalty [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (weight target : ι → ℝ) : ℝ :=
  heightPenalty weight target (fun i => support U (normal i))

theorem sampledPenalty_eq_heightPenalty [Fintype ι] {U : Set Plane}
    (normal : ι → Plane) (weight target height : ι → ℝ)
    (hexact : ∀ i, support U (normal i) = height i) :
    sampledPenalty U normal weight target = heightPenalty weight target height :=
  congrArg (heightPenalty weight target) (funext hexact)

theorem hasDerivAt_heightPenalty_update [Fintype ι] [DecidableEq ι]
    (weight target height : ι → ℝ) (j : ι) :
    HasDerivAt (fun ε : ℝ =>
      heightPenalty weight target (Function.update height j (height j + ε)))
      (2 * weight j * (height j - target j)) 0 := by
  have hi (i : ι) : HasDerivAt (fun ε : ℝ =>
      weight i * (Function.update height j (height j + ε) i - target i) ^ 2)
      (if i = j then 2 * weight j * (height j - target j) else 0) 0 := by
    rcases eq_or_ne i j with rfl | hij
    · convert ((((hasDerivAt_id (0 : ℝ)).const_add (height i)).sub_const (target i)).pow
        2).const_mul (weight i) using 1 <;> simp; ring
    · simpa [hij] using hasDerivAt_const (0 : ℝ) (weight i * (height i - target i) ^ 2)
  simpa [heightPenalty] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)

/-- The maximization premise is over actual caps with the same projection.
Any maximum in a larger cap domain implies this premise whenever these
fixed-projection competitors belong to that domain. -/
theorem selected_polygon_exposure_inequality [Fintype ι] [DecidableEq ι]
    {l r : ℝ} (normal : ι → Plane) (height weight target : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) (j : ι)
    (hlr : l ≤ r) (hnormal : ∀ i, 0 < (normal i).2)
    (hslopes : Function.Injective (wallSlope normal))
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    {p q : Plane} (hp : p ∈ upperPolygon l r normal height)
    (hq : q ∈ upperPolygon l r normal height) (hpq : p ≠ q)
    (hpface : coordDot p (normal j) = height j) (hqface : coordDot q (normal j) = height j)
    (hnx : (normal j).1 ≠ 0)
    (hdet : ∀ i, i ≠ j →
      (normal j).1 * (normal i).2 - (normal j).2 * (normal i).1 ≠ 0)
    (hunit : coordDot (normal j) (normal j) = 1)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → horizontalProjection V = Icc l r →
      finiteSpatialScore V normal corners terminal - sampledPenalty V normal weight target ≤
        finiteSpatialScore (upperPolygon l r normal height) normal corners terminal -
          sampledPenalty (upperPolygon l r normal height) normal weight target) :
    (∫ x in l..(l + (r - l) / 4),
        (roofExpr (ι := ι)).sourceDensity (wallSlope normal) (roofIntercept normal height)
          (outwardVelocity normal j) x) +
      (∫ x in (r - (r - l) / 4)..r,
        (roofExpr (ι := ι)).sourceDensity (wallSlope normal) (roofIntercept normal height)
          (outwardVelocity normal j) x) ≤
      (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4),
        (barrierExpr corners terminal).sourceDensity (wallSlope normal)
          (barrierIntercept normal height) (outwardVelocity normal j) x) +
        2 * weight j * (height j - target j) := by
  obtain ⟨δ, hδ, hfamily⟩ := exists_outward_support_variation j hlr
    (fun i => (hnormal i).le) hbaseline hexact hp hq hpq hpface hqface hnx
    (hnormal j).ne' hdet hunit
  -- the score of the moved polygon, as an affine envelope in the displacement `ε`
  have hscore {ε : ℝ} (hε : 0 ≤ ε) (hsup : ∀ i, support
      (upperPolygon l r normal (Function.update height j (height j + ε))) (normal i) =
        Function.update height j (height j + ε) i) :
      finiteSpatialScore (upperPolygon l r normal (Function.update height j (height j + ε)))
        normal corners terminal = intervalSpatialScore
        ((roofExpr (ι := ι)).affineEnvelope (wallSlope normal) (roofIntercept normal height)
          (outwardVelocity normal j) ε)
        ((barrierExpr corners terminal).affineEnvelope (wallSlope normal)
          (barrierIntercept normal height) (outwardVelocity normal j) ε) l r := by
    have hbaseline' : ∀ x ∈ Icc l r, ∀ i,
        coordDot (x, 0) (normal i) ≤ Function.update height j (height j + ε) i :=
      fun x hx i => (hbaseline x hx i).trans (le_update_self_iff.2 (le_add_of_nonneg_right hε) i)
    rw [finiteSpatialScore, horizontalLeft_upperPolygon normal _ hlr hbaseline',
      horizontalRight_upperPolygon normal _ hlr hbaseline',
      finiteBarrier_eq_affineEnvelope_update normal height j ε hsup corners terminal,
      ← roofEnvelope_update]
    exact intervalSpatialScore_congr_roof hlr
      (fun _ hx => capRoof_upperPolygon l r normal _ hnormal hbaseline' hx)
  have hscore0 := hscore le_rfl (by simpa only [add_zero, Function.update_eq_self] using hexact)
  simp only [add_zero, Function.update_eq_self] at hscore0
  apply finite_selected_exposure_inequality _ _ _ _ _ _ _ _ hslopes hslopes l r
    (hasDerivAt_heightPenalty_update weight target height j)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  obtain ⟨hcap, hprojection, hsupport⟩ := hfamily ε ⟨hε.1.le, hε.2⟩
  have h := hmax _ hcap hprojection
  rw [hscore hε.1.le hsupport, sampledPenalty_eq_heightPenalty normal weight target _ hsupport,
    hscore0, sampledPenalty_eq_heightPenalty normal weight target height hexact] at h
  simpa only [add_zero, Function.update_eq_self] using h

theorem outwardVelocity_eq_single [DecidableEq ι] (normal : ι → Plane) (j : ι) :
    outwardVelocity normal j =
      fun i : Option ι => if i = some j then 1 / (normal j).2 else 0 := by
  funext i
  cases i <;> simp +contextual [outwardVelocity]

/-- The derivative densities above are literal horizontal exposure
measures divided by the vertical component of the moved unit normal. -/
theorem integral_sourceDensity_outward [Fintype ι] [DecidableEq ι]
    (e : WallExpr (Option ι)) (normal : ι → Plane) (intercept : Option ι → ℝ)
    (j : ι) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, e.sourceDensity (wallSlope normal) intercept (outwardVelocity normal j) x) =
      volume.real (Ioc a b ∩ e.sourceSet (wallSlope normal) intercept (some j)) /
        (normal j).2 := by
  rw [outwardVelocity_eq_single, e.sourceDensity_single, intervalIntegral.integral_of_le hab,
    setIntegral_indicator (e.measurableSet_sourceSet _ _ _), setIntegral_const, smul_eq_mul]
  ring

end FinitePolygon

end AmbidextrousSofa
