module

public import AmbidextrousSofa.Measure.GraphIntegral
public import AmbidextrousSofa.Analysis.RoofContinuity
public import AmbidextrousSofa.Reference.Realization

@[expose] public section

/-!
# Support coordinates of the tangent and corner points

The support point of a quarter, its companion point, the inner corner and
the two support momenta, with the coordinate determinants of the support
point arcs. A point attaining an upward support is the actual roof point
over its abscissa.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def innerCornerPoint (f g : ℝ → ℝ) (t : ℝ) : Plane :=
  ((f t - 1) * Real.cos t - (g t - 1) * Real.sin t,
    (f t - 1) * Real.sin t + (g t - 1) * Real.cos t)

def firstTangentPoint (f fD : ℝ → ℝ) (t : ℝ) : Plane :=
  Reference.supportPoint (fun s => f s - 1) fD t

def secondTangentPoint (g gD : ℝ → ℝ) (t : ℝ) : Plane :=
  Reference.companionSupportPoint (fun s => g s - 1) gD t

def supportP (fD g : ℝ → ℝ) (t : ℝ) : ℝ := fD t - g t + 1

def supportQ (gD f : ℝ → ℝ) (t : ℝ) : ℝ := gD t + f t - 1

def supportPointDX (f fDD : ℝ → ℝ) (t : ℝ) : ℝ := -(f t + fDD t) * Real.sin t

def supportPointDY (f fDD : ℝ → ℝ) (t : ℝ) : ℝ := (f t + fDD t) * Real.cos t

def companionSupportPointDX (g gDD : ℝ → ℝ) (t : ℝ) : ℝ := -(g t + gDD t) * Real.cos t

def companionSupportPointDY (g gDD : ℝ → ℝ) (t : ℝ) : ℝ := -(g t + gDD t) * Real.sin t

theorem companionSupportPoint_coordinates (g gD : ℝ → ℝ) (t : ℝ) :
    Reference.companionSupportPoint g gD t =
      (-g t * Real.sin t - gD t * Real.cos t,
        g t * Real.cos t - gD t * Real.sin t) := by
  simp [Reference.companionSupportPoint, Reference.supportPoint, rotate]
  ring

theorem coordDet_supportPoint (f fD fDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.supportPoint f fD t)
      (supportPointDX f fDD t, supportPointDY f fDD t) = f t * (f t + fDD t) := by
  simp only [coordDet, Reference.supportPoint, supportPointDX, supportPointDY]
  linear_combination f t * (f t + fDD t) * Real.sin_sq_add_cos_sq t

theorem coordDet_companionSupportPoint (g gD gDD : ℝ → ℝ) (t : ℝ) :
    coordDet (Reference.companionSupportPoint g gD t)
      (companionSupportPointDX g gDD t, companionSupportPointDY g gDD t) =
      g t * (g t + gDD t) := by
  simp only [companionSupportPoint_coordinates, coordDet, companionSupportPointDX,
    companionSupportPointDY]
  linear_combination g t * (g t + gDD t) * Real.sin_sq_add_cos_sq t

/-- A point attaining an upward support is the actual roof point over its
own abscissa. The sine condition makes the normal genuinely upward-facing. -/
theorem IsDownwardCap.capRoof_eq_of_support_eq {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) {θ : ℝ} (hsin : 0 < Real.sin θ)
    (hsupport : coordDot p (unitNormal θ) = support U (unitNormal θ)) :
    capRoof U p.1 = p.2 := by
  refine le_antisymm ?_ (le_capRoof hU.isCompact hp)
  have h := hsupport ▸ coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (mem_image_of_mem Prod.fst hp)) (unitNormal θ)
  simp only [coordDot, unitNormal] at h
  exact le_of_mul_le_mul_right (by linarith) hsin

end AmbidextrousSofa
