module

public import AmbidextrousSofa.Analysis.FiniteNicheOscillation

@[expose] public section

/-!
# Exact Green identities for the literal finite graphs

The affine intercept of the selected wall is the graph value minus the
abscissa times its spatial slope. Absolutely continuous integration by
parts therefore gives an exact graph identity, with all endpoint terms.
For an actual circumscribed cap, subtraction of the central niche identity
from the two wing identities gives the spatial score in terms of actual
finite source masses. The horizontal top leaf has length factor one and
the niche floor leaf has intercept zero; neither is omitted.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace WallExpr

variable {ι : Type*}

theorem sourceIntercept_eq (e : WallExpr ι) (a b : ι → ℝ) (x : ℝ) :
    e.sourceDensity a b b x = e.affineGraph a b x - x * e.sourceDensity a b a x := by
  unfold sourceDensity affineGraph
  rw [eval_eq_source]
  ring

theorem integral_sourceIntercept [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ)
    (ha : Function.Injective a) (l r : ℝ) :
    (∫ x in l..r, e.sourceDensity a b b x) =
      2 * (∫ x in l..r, e.affineGraph a b x) -
        r * e.affineGraph a b r + l * e.affineGraph a b l := by
  have hac : AbsolutelyContinuousOnInterval (fun x : ℝ => x) l r :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hparts := hac.integral_mul_deriv_eq_deriv_mul
    (e.absolutelyContinuousOnInterval_affineGraph a b l r)
  have hid (x : ℝ) : deriv (fun y : ℝ => y) x = 1 := (hasDerivAt_id x).deriv
  simp only [hid, one_mul] at hparts
  have hderiv : (∫ x in l..r, x * e.sourceDensity a b a x) =
      ∫ x in l..r, x * deriv (e.affineGraph a b) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_injective_affine (b := b) ha] with x hx _
    rw [(e.hasDerivAt_affineGraph a b x hx).deriv]
  have hsplit : (∫ x in l..r, e.sourceDensity a b b x) =
      (∫ x in l..r, e.affineGraph a b x) -
        ∫ x in l..r, x * e.sourceDensity a b a x := by
    simp_rw [e.sourceIntercept_eq a b]
    exact intervalIntegral.integral_sub
      ((e.continuous_affineGraph a b).intervalIntegrable l r)
      ((e.intervalIntegrable_sourceDensity a b a l r).continuousOn_mul continuous_id.continuousOn)
  linarith

theorem two_mul_integral_affineGraph [Fintype ι] (e : WallExpr ι) (a b : ι → ℝ)
    (ha : Function.Injective a) {l r : ℝ} (hlr : l ≤ r) :
    2 * (∫ x in l..r, e.affineGraph a b x) =
      (∑ i, e.sourceMass a b l r i * b i) +
        r * e.affineGraph a b r - l * e.affineGraph a b l := by
  have h := e.integral_sourceIntercept a b ha l r
  rw [e.integral_sourceDensity_eq_sum a b b hlr] at h
  linarith

end WallExpr

theorem finiteSourceVariation_intercepts {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c) {l r : ℝ} (hlr : l ≤ r) :
    2 * intervalSpatialScore (outer.affineGraph a b) (inner.affineGraph c d) l r =
      finiteSourceVariation outer inner a b c d l r b d +
        r * (outer.affineGraph a b r -
          rightEndpointPressure (outer.affineGraph a b) (inner.affineGraph c d) l r) -
        l * (outer.affineGraph a b l -
          leftEndpointPressure (outer.affineGraph a b) (inner.affineGraph c d) l r) := by
  have hleft := outer.integral_sourceIntercept a b ha l (l + (r - l) / 4)
  have hright := outer.integral_sourceIntercept a b ha (r - (r - l) / 4) r
  have hmiddle := inner.integral_sourceIntercept c d hc
    (l + (r - l) / 4) (r - (r - l) / 4)
  rw [finiteSourceVariation_eq_integrals outer inner a b b c d d hlr]
  unfold intervalSpatialScore rightEndpointPressure leftEndpointPressure
  nlinarith

namespace FinitePolygon

variable {ι : Type*}

def finiteWingMass [Fintype ι] (U : Set Plane) (normal : ι → Plane) (i : Option ι) : ℝ :=
  (roofExpr (ι := ι)).sourceMass (wallSlope normal)
      (roofIntercept normal (fun j => support U (normal j)))
      (horizontalLeft U) (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) i +
    (roofExpr (ι := ι)).sourceMass (wallSlope normal)
      (roofIntercept normal (fun j => support U (normal j)))
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U) i

def normalArcFactor (normal : ι → Plane) : Option ι → ℝ
  | none => 1
  | some i => 1 / (normal i).2

def finiteWingLength [Fintype ι] (U : Set Plane) (normal : ι → Plane) : ℝ :=
  ∑ i, finiteWingMass U normal i * normalArcFactor normal i

def finiteSupportDefect [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  ∑ i, (finiteExposureDefect U normal corners terminal i / (normal i).2) *
    (support U (normal i) - 1)

theorem finiteWingLength_sub_supportDefect_eq_variation [Fintype ι]
    (U : Set Plane) (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    finiteWingLength U normal - finiteSupportDefect U normal corners terminal =
      finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
        (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
        (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
        (horizontalLeft U) (horizontalRight U)
        (roofIntercept normal (fun i => support U (normal i)))
        (barrierIntercept normal (fun i => support U (normal i))) := by
  let O := finiteWingMass U normal
  let N := (barrierExpr corners terminal).sourceMass (wallSlope normal)
    (barrierIntercept normal (fun i => support U (normal i)))
    (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)
  have hdef (i : ι) : finiteExposureDefect U normal corners terminal i =
      N (some i) - O (some i) := by
    dsimp [N, O, finiteExposureDefect, finiteWingMass]
    ring
  unfold finiteWingLength finiteSupportDefect finiteSourceVariation
  simp only [Fintype.sum_option, normalArcFactor, roofIntercept, barrierIntercept,
    mul_one, mul_zero, zero_add, add_zero, hdef]
  change O none + (∑ i, O (some i) * (1 / (normal i).2)) -
      (∑ i, ((N (some i) - O (some i)) / (normal i).2) * (support U (normal i) - 1)) =
    O none + (∑ i, O (some i) * (support U (normal i) / (normal i).2)) -
      ∑ i, N (some i) * ((support U (normal i) - 1) / (normal i).2)
  calc
    _ = O none + ∑ i, (O (some i) * (1 / (normal i).2) -
        ((N (some i) - O (some i)) / (normal i).2) * (support U (normal i) - 1)) := by
      rw [Finset.sum_sub_distrib]
      ring
    _ = O none + ∑ i, (O (some i) * (support U (normal i) / (normal i).2) -
        N (some i) * ((support U (normal i) - 1) / (normal i).2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]; ring

/-- Exact finite Green formula with both actual endpoint pressure defects.
The top mass is included in `finiteWingLength`; the floor intercept is zero. -/
theorem finiteSpatialScore_green [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι) :
    2 * finiteSpatialScore U normal corners terminal =
      finiteWingLength U normal - finiteSupportDefect U normal corners terminal +
        horizontalRight U * (capRoof U (horizontalRight U) -
          rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
            (horizontalLeft U) (horizontalRight U)) -
        horizontalLeft U * (capRoof U (horizontalLeft U) -
          leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
            (horizontalLeft U) (horizontalRight U)) := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  have h := finiteSourceVariation_intercepts (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i))) hslope hslope hlr
  rw [← finiteWingLength_sub_supportDefect_eq_variation] at h
  change 2 * intervalSpatialScore (roofEnvelope normal (fun i => support U (normal i)))
      ((barrierExpr corners terminal).affineGraph (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))))
      (horizontalLeft U) (horizontalRight U) = _ at h
  rw [affineGraph_barrier] at h
  have hroof' : EqOn ((roofExpr (ι := ι)).affineGraph (wallSlope normal)
      (roofIntercept normal (fun i => support U (normal i)))) (capRoof U)
      (Icc (horizontalLeft U) (horizontalRight U)) := hroof
  rw [intervalSpatialScore_congr_roof hlr hroof,
    rightEndpointPressure_congr_roof hlr hroof', leftEndpointPressure_congr_roof hlr hroof',
    hroof' ⟨hlr, le_rfl⟩, hroof' ⟨le_rfl, hlr⟩] at h
  exact h

end FinitePolygon

end AmbidextrousSofa
