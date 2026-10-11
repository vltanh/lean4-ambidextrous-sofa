module

public import AmbidextrousSofa.Measure.Fibers

@[expose] public section

/-!
# Integrated spatial partition and its equality conditions

This module passes from the pointwise identities to real Lebesgue integrals.
The horizontal projection is split into a measurable middle set and its
complement. Equal measure of those pieces cancels the constant terms. The
standard middle half of a closed interval is proved to have that property.

The resulting spatial scores are genuine integrals of roofs and barriers.
The exact identity holds even when some signed fibers are negative. Only
the final ordinary-area corollaries use nonnegative physical fibers and
measurable envelope containment. No universal sharp bound on a spatial
score is postulated or proved here.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-! ## The middle half has the required measure -/

/-- The middle half of the closed horizontal interval `[l,r]`. -/
def middleHalfInterval (l r : ℝ) : Set ℝ :=
  Icc (l + (r - l) / 4) (r - (r - l) / 4)

theorem measurableSet_middleHalfInterval (l r : ℝ) :
    MeasurableSet (middleHalfInterval l r) :=
  measurableSet_Icc

theorem middleHalfInterval_subset {l r : ℝ} (hlr : l ≤ r) :
    middleHalfInterval l r ⊆ Icc l r :=
  Icc_subset_Icc (by linarith) (by linarith)

theorem volumeReal_middleHalfInterval {l r : ℝ} (hlr : l ≤ r) :
    volume.real (middleHalfInterval l r) = (r - l) / 2 := by
  rw [middleHalfInterval, Real.volume_real_Icc_of_le (by linarith)]
  ring

theorem volumeReal_exterior_middleHalfInterval {l r : ℝ} (hlr : l ≤ r) :
    volume.real (Icc l r \ middleHalfInterval l r) = (r - l) / 2 := by
  rw [measureReal_sdiff (middleHalfInterval_subset hlr) measurableSet_Icc measure_Icc_lt_top.ne,
    Real.volume_real_Icc_of_le hlr, volumeReal_middleHalfInterval hlr]
  ring

/-- The two exterior quarters together have the same measure as the middle half. -/
theorem middleHalfInterval_measure_balance {l r : ℝ} (hlr : l ≤ r) :
    volume.real (middleHalfInterval l r) =
      volume.real (Icc l r \ middleHalfInterval l r) := by
  rw [volumeReal_middleHalfInterval hlr, volumeReal_exterior_middleHalfInterval hlr]

/-! ## Scores, defects, and integrability -/

/-- The spatial score associated with a roof deficit `d` and a niche barrier `n`.
The actual roof is `1-d`; the middle barrier is charged separately. -/
def spatialScore (I J : Set ℝ) (d n : ℝ → ℝ) : ℝ :=
  (∫ x in I \ J, 1 - d x) - ∫ x in J, n x

/-- The integrated relaxation defect, keeping the middle and exterior terms separate. -/
def integratedPartitionDefect (I J : Set ℝ) (dU dV nU nV : ℝ → ℝ) : ℝ :=
  (∫ x in J, middlePartitionDefect (dU x) (dV x) (nU x) (nV x)) +
    ∫ x in I \ J, exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x)

theorem integratedPartitionDefect_nonneg
    (I J : Set ℝ) (dU dV nU nV : ℝ → ℝ) :
    0 ≤ integratedPartitionDefect I J dU dV nU nV :=
  add_nonneg (integral_nonneg fun x => middlePartitionDefect_nonneg (dU x) (dV x) (nU x) (nV x))
    (integral_nonneg fun x => exteriorPartitionDefect_nonneg (dU x) (dV x) (nU x) (nV x))

/-! ## Integrating the exact pointwise identities -/

/-- ED.3 for any measurable equal-measure split. Signed fibers need not be
nonnegative. All integral identifications are proved from the wall functions. -/
theorem integrated_partition_defect_identity
    {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hJ : MeasurableSet J) (hJI : J ⊆ I) (hFinite : volume I ≠ ⊤)
    (hBalance : volume.real J = volume.real (I \ J))
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    spatialScore I J dU nU + spatialScore I J dV nV -
        (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) =
      integratedPartitionDefect I J dU dV nU nV := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I := integrableOn_const hFinite
  have hs := integrableOn_signedFiberLength hFinite hdU hdV hnU hnV
  have hE : I \ J ⊆ I := sdiff_subset
  unfold spatialScore integratedPartitionDefect
  simp only [← middle_partition_defect_identity, ← exterior_partition_defect_identity]
  rw [integral_sub (IntegrableOn.mono_set ((h1.sub' hnU).sub' hnV) hJI) (hs.mono_set hJI),
    integral_sub (IntegrableOn.mono_set ((h1.sub' hdU).sub' hdV) hE) (hs.mono_set hE),
    integral_sub (IntegrableOn.mono_set (h1.sub' hnU) hJI) (hnV.mono_set hJI),
    integral_sub (IntegrableOn.mono_set (h1.sub' hdU) hE) (hdV.mono_set hE),
    integral_sub (h1.mono_set hJI) (hnU.mono_set hJI),
    integral_sub (h1.mono_set hE) (hdU.mono_set hE), integral_sub (h1.mono_set hE) (hdV.mono_set hE),
    setIntegral_sdiff hJ hs hJI]
  simp only [setIntegral_const, smul_eq_mul, mul_one]
  linarith

/-! ## Ordinary-area enclosure, with physical fibers -/

/-! ## Exact actual-body decomposition -/

/-- ED.5 as an exact ordinary-area identity with explicitly constructed
integral scores and set-difference filling defect. It is valid for every real
comparison constant `C`; establishing sharp score bounds is a later task. -/
theorem actualBody_four_term_deficit_identity
    (C : ℝ) {S : Set Plane} {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hS : S ⊆ fourWallEnvelope I dU dV nU nV) (hMeasS : MeasurableSet S)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hJI : J ⊆ I)
    (hFinite : volume I ≠ ⊤) (hBalance : volume.real J = volume.real (I \ J))
    (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hidU : IntegrableOn dU I) (hidV : IntegrableOn dV I)
    (hinU : IntegrableOn nU I) (hinV : IntegrableOn nV I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I,
      0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    C - volume.real S =
      (C / 2 - spatialScore I J dU nU) +
        (C / 2 - spatialScore I J dV nV) +
        integratedPartitionDefect I J dU dV nU nV +
        volume.real (fourWallEnvelope I dU dV nU nV \ S) := by
  have := integrated_partition_defect_identity hJ hJI hFinite hBalance hidU hidV hinU hinV
  have := volumeReal_sdiff_fourWallEnvelope_eq_signedIntegral_sub hS hMeasS hI hdU hdV hnU hnV
    (integrableOn_signedFiberLength hFinite hidU hidV hinU hinV) hNonneg
  linarith

end AmbidextrousSofa
