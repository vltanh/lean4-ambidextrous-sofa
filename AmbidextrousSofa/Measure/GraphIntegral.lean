module

public import AmbidextrousSofa.Measure.CapScore
public import AmbidextrousSofa.Analysis.PositivePartCalculus

@[expose] public section

/-!
# Actual cap area and absolutely continuous primitives

A cap is the region under its attained roof, so Cavalieri gives its area,
which splits into two curved wings and a horizontal top face. A function
with an exact integral representation is absolutely continuous; this covers
continuous functions with an integrable right derivative, such as piecewise
smooth support derivatives with curvature jumps, and almost everywhere their
right derivative is their derivative.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def coordDet (p q : Plane) : ℝ := p.1 * q.2 - p.2 * q.1

/-- A cap is the actual region under its attained roof, including endpoint fibers. -/
theorem IsDownwardCap.eq_verticalIntervalRegion {U : Set Plane} (hU : IsDownwardCap U) :
    U = verticalIntervalRegion (Icc (horizontalLeft U) (horizontalRight U))
      (fun _ => 0) (capRoof U) := by
  ext p
  rw [hU.mem_iff_projection_and_roof,
    hU.horizontalProjection_eq_Icc]
  rfl

/-- Cavalieri for the area of an intrinsic downward cap. -/
theorem IsDownwardCap.volumeReal_eq_integral_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) :
    volume.real U = ∫ x in Icc (horizontalLeft U) (horizontalRight U), capRoof U x := by
  have hroof : ∀ x, 0 ≤ capRoof U x := capRoof_nonneg hU.isCompact fun p hp => (hU.inStrip hp).1
  have hvol := volume_verticalIntervalRegion_eq_lintegral (lower := fun _ => 0)
    (I := Icc (horizontalLeft U) (horizontalRight U)) measurableSet_Icc measurable_const
    hU.measurable_capRoof
  rw [← hU.eq_verticalIntervalRegion] at hvol
  simp only [sub_zero, ← ofReal_integral_eq_lintegral_ofReal (hU.integrableOn_capRoof_Icc _ _)
    (.of_forall hroof)] at hvol
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal (integral_nonneg hroof)]

theorem IsDownwardCap.intervalIntegrable_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) : IntervalIntegrable (capRoof U) volume a b :=
  (intervalIntegrable_iff').mpr (hU.integrableOn_capRoof_Icc _ _)

/-- Two curved wings and an actual horizontal top face partition cap area.
The wing integrals are oriented from the right toward the left. -/
theorem IsDownwardCap.volumeReal_eq_wing_integrals {U : Set Plane}
    (hU : IsDownwardCap U) {l r a b : ℝ}
    (hl : horizontalLeft U = l) (hr : horizontalRight U = r) (hab : a ≤ b)
    (hface : ∀ x ∈ Icc a b, capRoof U x = 1) :
    volume.real U = -(∫ x in a..l, capRoof U x) + (b - a) -
      ∫ x in r..b, capRoof U x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_capRoof l a) (hU.intervalIntegrable_capRoof a r)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_capRoof a b) (hU.intervalIntegrable_capRoof b r)
  have h3 : (∫ x in a..b, capRoof U x) = b - a :=
    (intervalIntegral.integral_congr fun x hx => hface x (uIcc_of_le hab ▸ hx)).trans (by simp)
  rw [hU.volumeReal_eq_integral_capRoof, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact),
    hl, hr, intervalIntegral.integral_symm l a, intervalIntegral.integral_symm b r]
  linarith

/-- An exact integral representation supplies absolute continuity. -/
theorem absolutelyContinuousOnInterval_of_integral_sub
    {f g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (heq : ∀ x ∈ uIcc a b, f x - f a = ∫ t in a..x, g t) :
    AbsolutelyContinuousOnInterval f a b :=
  ((absolutelyContinuousOnInterval_const (f a) a b).add
    (hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)).congr
    fun x hx => by simp [← heq x hx]

/-- A continuous function with an integrable right derivative is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hf' : ∀ t, HasDerivWithinAt f (f' t) (Ioi t) t)
    (hi : IntervalIntegrable f' volume a b) : AbsolutelyContinuousOnInterval f a b :=
  absolutelyContinuousOnInterval_of_integral_sub hi fun _ hx =>
    (intervalIntegral.integral_eq_sub_of_hasDeriv_right hf.continuousOn
      (fun t _ => hf' t) (hi.mono_set (uIcc_subset_uIcc_left hx))).symm

/-- Almost everywhere, the right derivative of an absolutely continuous function is its
derivative. -/
theorem ae_hasDerivAt_of_hasDerivWithinAt_Ioi {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ t, HasDerivWithinAt f (f' t) (Ioi t) t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (f' t) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hf.ae_differentiableAt]
    with t ht hd
  have h := (hd (Ioo_subset_Icc_self.trans Icc_subset_uIcc ht)).hasDerivAt
  rwa [(uniqueDiffWithinAt_Ioi t).eq_deriv _ h.hasDerivWithinAt (hf' t)] at h

end AmbidextrousSofa
