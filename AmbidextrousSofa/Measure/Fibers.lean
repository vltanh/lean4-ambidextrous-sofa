module

public import AmbidextrousSofa.Algebra.Deficit
public import AmbidextrousSofa.Geometry.Plane
public import AmbidextrousSofa.Topology.RegularClosed

@[expose] public section

/-!
# Measurable envelopes and their exact vertical-fiber areas

The plane carries product Lebesgue measure. Tonelli's theorem first gives an
extended nonnegative integral, without a finiteness or nonempty-fiber
assumption. A four-wall fiber contributes the positive part of its signed
length. Replacing that positive part by the signed length is a separate step
requiring almost-everywhere nonnegativity.

The final containment lemmas explain how an actual body with the full
horizontal projection supplies pointwise nonempty fibers. No cap bound or
motion-reduction theorem is assumed by these definitions.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-! ## General measurable vertical intervals -/

/-- A family of closed vertical intervals above a horizontal set. The endpoints
may be in either order, in which case the corresponding interval may be empty. -/
def verticalIntervalRegion (I : Set ℝ) (lower upper : ℝ → ℝ) : Set Plane :=
  {p | p.1 ∈ I ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}

@[simp]
theorem mem_verticalIntervalRegion (I : Set ℝ) (lower upper : ℝ → ℝ) (p : Plane) :
    p ∈ verticalIntervalRegion I lower upper ↔
      p.1 ∈ I ∧ lower p.1 ≤ p.2 ∧ p.2 ≤ upper p.1 :=
  Iff.rfl

/-- Cavalieri's formula for measurable, possibly empty vertical intervals.
No integrability assumption is needed for the extended nonnegative integral. -/
theorem volume_verticalIntervalRegion_eq_lintegral
    {I : Set ℝ} {lower upper : ℝ → ℝ}
    (hI : MeasurableSet I) (hLower : Measurable lower) (hUpper : Measurable upper) :
    volume (verticalIntervalRegion I lower upper) =
      ∫⁻ x in I, ENNReal.ofReal (upper x - lower x) := by
  have hm : MeasurableSet (verticalIntervalRegion I lower upper) :=
    measurableSet_region_between_cc hLower hUpper hI
  rw [Measure.volume_eq_prod, Measure.prod_apply hm, ← lintegral_indicator hI]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ I <;> simp [verticalIntervalRegion, hx, Icc_def]

/-! ## Four-wall envelopes -/

/-- The exact four-wall envelope over the actual horizontal projection. -/
def fourWallEnvelope (I : Set ℝ) (dU dV nU nV : ℝ → ℝ) : Set Plane :=
  {p | p.1 ∈ I ∧ p.2 ∈ fourWallFiber (dU p.1) (dV p.1) (nU p.1) (nV p.1)}

/-- Integrable wall data on a finite-measure set give an integrable signed length. -/
theorem integrableOn_signedFiberLength {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hFinite : volume I ≠ ⊤)
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I :=
  ((integrableOn_const hFinite).sub (Integrable.sup hdV hnU)).sub (Integrable.sup hdU hnV)

/-- The signed integral computes area only after nonnegative physical fibers
have been justified, here in the sufficient almost-everywhere form. -/
theorem volume_fourWallEnvelope_eq_ofReal_signedIntegral
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hI : MeasurableSet I) (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hSigned : IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I, 0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    volume (fourWallEnvelope I dU dV nU nV) =
      ENNReal.ofReal (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) := by
  have h : fourWallEnvelope I dU dV nU nV = verticalIntervalRegion I
      (fun x => max (dV x) (nU x)) (fun x => 1 - max (dU x) (nV x)) :=
    ext fun p => and_congr_right fun _ => by rw [fourWallFiber_eq_Icc]
  rw [h, volume_verticalIntervalRegion_eq_lintegral (upper := fun x => 1 - max (dU x) (nV x)) hI
    (hdV.max hnU) (measurable_const.sub (hdU.max hnV)),
    ofReal_integral_eq_lintegral_ofReal hSigned hNonneg]
  exact lintegral_congr fun x => by rw [signedFiberLength, sub_right_comm]

theorem volumeReal_fourWallEnvelope_eq_signedIntegral
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hI : MeasurableSet I) (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hSigned : IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I, 0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    volume.real (fourWallEnvelope I dU dV nU nV) =
      ∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x) := by
  rw [measureReal_def,
    volume_fourWallEnvelope_eq_ofReal_signedIntegral hI hdU hdV hnU hnV hSigned hNonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hNonneg)]

/-! ## The actual body supplies physical fibers -/

/-- A nonempty body fiber forces nonnegative signed envelope length at the
same horizontal coordinate. This uses actual set containment. -/
theorem signedFiberLength_nonneg_on_of_subset_projection
    {S : Set Plane} {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hS : S ⊆ fourWallEnvelope I dU dV nU nV)
    (hProjection : I ⊆ Prod.fst '' S) :
    ∀ x ∈ I, 0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x) := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hProjection hx
  exact signedFiberLength_nonneg_of_mem _ _ _ _ _ (hS hp).2

/-! ## The filling defect and literal recovery -/

/-- A measurable body's missing part of the finite envelope has exactly the
area difference used in ED.4. This is ordinary set difference, not a signed
or multiplicity-weighted area. -/
theorem volumeReal_sdiff_fourWallEnvelope_eq_signedIntegral_sub
    {S : Set Plane} {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hS : S ⊆ fourWallEnvelope I dU dV nU nV) (hMeasS : MeasurableSet S)
    (hI : MeasurableSet I) (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hSigned : IntegrableOn (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I, 0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    volume.real (fourWallEnvelope I dU dV nU nV \ S) =
      (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) - volume.real S := by
  rw [measureReal_sdiff hS hMeasS ((volume_fourWallEnvelope_eq_ofReal_signedIntegral
    hI hdU hdV hnU hnV hSigned hNonneg).trans_ne ENNReal.ofReal_ne_top),
    volumeReal_fourWallEnvelope_eq_signedIntegral hI hdU hdV hnU hnV hSigned hNonneg]

end AmbidextrousSofa
