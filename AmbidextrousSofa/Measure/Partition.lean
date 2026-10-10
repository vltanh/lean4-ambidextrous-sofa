import AmbidextrousSofa.Measure.Fibers

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
    middleHalfInterval l r ⊆ Icc l r := by
  intro x hx
  change l + (r - l) / 4 ≤ x ∧ x ≤ r - (r - l) / 4 at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem volumeReal_middleHalfInterval {l r : ℝ} (hlr : l ≤ r) :
    volume.real (middleHalfInterval l r) = (r - l) / 2 := by
  unfold middleHalfInterval
  rw [Real.volume_real_Icc_of_le (by linarith :
    l + (r - l) / 4 ≤ r - (r - l) / 4)]
  ring

theorem volumeReal_exterior_middleHalfInterval {l r : ℝ} (hlr : l ≤ r) :
    volume.real (Icc l r \ middleHalfInterval l r) = (r - l) / 2 := by
  have hFinite : volume (Icc l r) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [measureReal_sdiff (middleHalfInterval_subset hlr)
    (measurableSet_middleHalfInterval l r) hFinite,
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

theorem integrableOn_middlePartitionDefect
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    IntegrableOn (fun x => middlePartitionDefect (dU x) (dV x) (nU x) (nV x)) I :=
  Integrable.add (Integrable.pos_part (Integrable.sub hdV hnU))
    (Integrable.pos_part (Integrable.sub hdU hnV))

theorem integrableOn_exteriorPartitionDefect
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    IntegrableOn (fun x => exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x)) I :=
  Integrable.add (Integrable.pos_part (Integrable.sub hnU hdV))
    (Integrable.pos_part (Integrable.sub hnV hdU))

theorem integral_middlePartitionDefect_nonneg
    (I : Set ℝ) (dU dV nU nV : ℝ → ℝ) :
    0 ≤ ∫ x in I, middlePartitionDefect (dU x) (dV x) (nU x) (nV x) :=
  integral_nonneg (fun x => middlePartitionDefect_nonneg (dU x) (dV x) (nU x) (nV x))

theorem integral_exteriorPartitionDefect_nonneg
    (I : Set ℝ) (dU dV nU nV : ℝ → ℝ) :
    0 ≤ ∫ x in I, exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x) :=
  integral_nonneg (fun x => exteriorPartitionDefect_nonneg (dU x) (dV x) (nU x) (nV x))

theorem integratedPartitionDefect_nonneg
    (I J : Set ℝ) (dU dV nU nV : ℝ → ℝ) :
    0 ≤ integratedPartitionDefect I J dU dV nU nV :=
  add_nonneg (integral_middlePartitionDefect_nonneg J dU dV nU nV)
    (integral_exteriorPartitionDefect_nonneg (I \ J) dU dV nU nV)

/-! ## Integrating the exact pointwise identities -/

theorem integral_middle_partition_defect_identity
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I)
    (hSigned : IntegrableOn
      (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I) :
    (∫ x in I, 1 - nU x - nV x) -
        (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) =
      ∫ x in I, middlePartitionDefect (dU x) (dV x) (nU x) (nV x) := by
  rw [← integral_sub (Integrable.sub (Integrable.sub hOne hnU) hnV) hSigned]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (fun x => middle_partition_defect_identity (dU x) (dV x) (nU x) (nV x))

theorem integral_exterior_partition_defect_identity
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I)
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hSigned : IntegrableOn
      (fun x => signedFiberLength (dU x) (dV x) (nU x) (nV x)) I) :
    (∫ x in I, 1 - dU x - dV x) -
        (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) =
      ∫ x in I, exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x) := by
  rw [← integral_sub (Integrable.sub (Integrable.sub hOne hdU) hdV) hSigned]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (fun x => exterior_partition_defect_identity (dU x) (dV x) (nU x) (nV x))

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
  have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I := integrableOn_const hFinite
  have hOneJ := hOne.mono_set hJI
  have hOneE := hOne.mono_set (sdiff_subset : I \ J ⊆ I)
  have hdUE := hdU.mono_set (sdiff_subset : I \ J ⊆ I)
  have hdVE := hdV.mono_set (sdiff_subset : I \ J ⊆ I)
  have hnUJ := hnU.mono_set hJI
  have hnVJ := hnV.mono_set hJI
  have hSigned := integrableOn_signedFiberLength hFinite hdU hdV hnU hnV
  have hMiddle := integral_middle_partition_defect_identity hOneJ hnUJ hnVJ
    (hSigned.mono_set hJI)
  have hExterior := integral_exterior_partition_defect_identity hOneE hdUE hdVE
    (hSigned.mono_set (sdiff_subset : I \ J ⊆ I))
  have hSplit := setIntegral_sdiff hJ hSigned hJI
  have hMiddleExpanded :
      (∫ x in J, 1 - nU x - nV x) =
        volume.real J - (∫ x in J, nU x) - ∫ x in J, nV x := by
    rw [integral_sub (Integrable.sub hOneJ hnUJ) hnVJ, integral_sub hOneJ hnUJ]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
  have hExteriorExpanded :
      (∫ x in I \ J, 1 - dU x - dV x) =
        volume.real (I \ J) - (∫ x in I \ J, dU x) - ∫ x in I \ J, dV x := by
    rw [integral_sub (Integrable.sub hOneE hdUE) hdVE, integral_sub hOneE hdUE]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
  unfold spatialScore integratedPartitionDefect
  rw [integral_sub hOneE hdUE, integral_sub hOneE hdVE]
  simp only [setIntegral_const, smul_eq_mul, mul_one]
  linarith

/-- The intended middle-half specialization discharges the measure-balance
and finite-measure conditions explicitly. -/
theorem integrated_partition_defect_identity_middleHalf
    {l r : ℝ} {dU dV nU nV : ℝ → ℝ} (hlr : l ≤ r)
    (hdU : IntegrableOn dU (Icc l r)) (hdV : IntegrableOn dV (Icc l r))
    (hnU : IntegrableOn nU (Icc l r)) (hnV : IntegrableOn nV (Icc l r)) :
    spatialScore (Icc l r) (middleHalfInterval l r) dU nU +
        spatialScore (Icc l r) (middleHalfInterval l r) dV nV -
        (∫ x in Icc l r, signedFiberLength (dU x) (dV x) (nU x) (nV x)) =
      integratedPartitionDefect (Icc l r) (middleHalfInterval l r) dU dV nU nV := by
  exact integrated_partition_defect_identity (measurableSet_middleHalfInterval l r)
    (middleHalfInterval_subset hlr) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (middleHalfInterval_measure_balance hlr) hdU hdV hnU hnV

theorem signedIntegral_le_spatialScore_sum
    {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hJ : MeasurableSet J) (hJI : J ⊆ I) (hFinite : volume I ≠ ⊤)
    (hBalance : volume.real J = volume.real (I \ J))
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) ≤
      spatialScore I J dU nU + spatialScore I J dV nV := by
  have hIdentity := integrated_partition_defect_identity hJ hJI hFinite hBalance hdU hdV hnU hnV
  have hNonneg := integratedPartitionDefect_nonneg I J dU dV nU nV
  linarith

/-! ## Exact almost-everywhere equality conditions -/

theorem integral_middlePartitionDefect_eq_zero_iff
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hIntegrable : IntegrableOn
      (fun x => middlePartitionDefect (dU x) (dV x) (nU x) (nV x)) I) :
    (∫ x in I, middlePartitionDefect (dU x) (dV x) (nU x) (nV x)) = 0 ↔
      ∀ᵐ x ∂volume.restrict I, dV x ≤ nU x ∧ dU x ≤ nV x := by
  rw [integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x =>
      middlePartitionDefect_nonneg (dU x) (dV x) (nU x) (nV x))) hIntegrable]
  constructor
  · intro hZero
    filter_upwards [hZero] with x hx
    exact (middlePartitionDefect_eq_zero_iff (dU x) (dV x) (nU x) (nV x)).mp hx
  · intro hOrder
    filter_upwards [hOrder] with x hx
    exact (middlePartitionDefect_eq_zero_iff (dU x) (dV x) (nU x) (nV x)).mpr hx

theorem integral_exteriorPartitionDefect_eq_zero_iff
    {I : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hIntegrable : IntegrableOn
      (fun x => exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x)) I) :
    (∫ x in I, exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x)) = 0 ↔
      ∀ᵐ x ∂volume.restrict I, nU x ≤ dV x ∧ nV x ≤ dU x := by
  rw [integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x =>
      exteriorPartitionDefect_nonneg (dU x) (dV x) (nU x) (nV x))) hIntegrable]
  constructor
  · intro hZero
    filter_upwards [hZero] with x hx
    exact (exteriorPartitionDefect_eq_zero_iff (dU x) (dV x) (nU x) (nV x)).mp hx
  · intro hOrder
    filter_upwards [hOrder] with x hx
    exact (exteriorPartitionDefect_eq_zero_iff (dU x) (dV x) (nU x) (nV x)).mpr hx

/-- ED.6: vanishing integrated relaxation is exactly the two a.e. wall orders.
Integrability is explicit, so the zero value of an undefined Bochner integral
cannot be mistaken for a vanishing nonnegative defect. -/
theorem integratedPartitionDefect_eq_zero_iff
    {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hMiddle : IntegrableOn
      (fun x => middlePartitionDefect (dU x) (dV x) (nU x) (nV x)) J)
    (hExterior : IntegrableOn
      (fun x => exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x)) (I \ J)) :
    integratedPartitionDefect I J dU dV nU nV = 0 ↔
      (∀ᵐ x ∂volume.restrict J, dV x ≤ nU x ∧ dU x ≤ nV x) ∧
        (∀ᵐ x ∂volume.restrict (I \ J), nU x ≤ dV x ∧ nV x ≤ dU x) := by
  have hMiddleNonneg := integral_middlePartitionDefect_nonneg J dU dV nU nV
  have hExteriorNonneg := integral_exteriorPartitionDefect_nonneg (I \ J) dU dV nU nV
  constructor
  · intro hZero
    unfold integratedPartitionDefect at hZero
    have hm : (∫ x in J, middlePartitionDefect (dU x) (dV x) (nU x) (nV x)) = 0 := by
      linarith
    have he : (∫ x in I \ J, exteriorPartitionDefect (dU x) (dV x) (nU x) (nV x)) = 0 := by
      linarith
    exact ⟨(integral_middlePartitionDefect_eq_zero_iff hMiddle).mp hm,
      (integral_exteriorPartitionDefect_eq_zero_iff hExterior).mp he⟩
  · rintro ⟨hMiddleOrder, hExteriorOrder⟩
    unfold integratedPartitionDefect
    rw [(integral_middlePartitionDefect_eq_zero_iff hMiddle).mpr hMiddleOrder,
      (integral_exteriorPartitionDefect_eq_zero_iff hExterior).mpr hExteriorOrder,
      zero_add]

/-- Equality in the integrated signed partition has exactly the a.e. wall-order
conditions. This is independent of any sharp one-cap score inequality. -/
theorem spatialScore_sum_eq_signedIntegral_iff
    {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hJ : MeasurableSet J) (hJI : J ⊆ I) (hFinite : volume I ≠ ⊤)
    (hBalance : volume.real J = volume.real (I \ J))
    (hdU : IntegrableOn dU I) (hdV : IntegrableOn dV I)
    (hnU : IntegrableOn nU I) (hnV : IntegrableOn nV I) :
    spatialScore I J dU nU + spatialScore I J dV nV =
        (∫ x in I, signedFiberLength (dU x) (dV x) (nU x) (nV x)) ↔
      (∀ᵐ x ∂volume.restrict J, dV x ≤ nU x ∧ dU x ≤ nV x) ∧
        (∀ᵐ x ∂volume.restrict (I \ J), nU x ≤ dV x ∧ nV x ≤ dU x) := by
  have hIdentity := integrated_partition_defect_identity hJ hJI hFinite hBalance hdU hdV hnU hnV
  have hMiddle := (integrableOn_middlePartitionDefect hdU hdV hnU hnV).mono_set hJI
  have hExterior := (integrableOn_exteriorPartitionDefect hdU hdV hnU hnV).mono_set
    (sdiff_subset : I \ J ⊆ I)
  rw [← integratedPartitionDefect_eq_zero_iff hMiddle hExterior]
  constructor <;> intro h <;> linarith

/-! ## Ordinary-area enclosure, with physical fibers -/

/-- A contained body's actual area is bounded by the two spatial scores.
The geometric and analytic hypotheses are all exposed, including nonnegative
signed fibers; no sharp scalar cap inequality occurs among the assumptions. -/
theorem volumeReal_le_spatialScore_sum_of_subset_fourWallEnvelope
    {S : Set Plane} {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hS : S ⊆ fourWallEnvelope I dU dV nU nV)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hJI : J ⊆ I)
    (hFinite : volume I ≠ ⊤) (hBalance : volume.real J = volume.real (I \ J))
    (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hidU : IntegrableOn dU I) (hidV : IntegrableOn dV I)
    (hinU : IntegrableOn nU I) (hinV : IntegrableOn nV I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I,
      0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    volume.real S ≤ spatialScore I J dU nU + spatialScore I J dV nV := by
  have hSigned := integrableOn_signedFiberLength hFinite hidU hidV hinU hinV
  exact (volumeReal_le_signedIntegral_of_subset_fourWallEnvelope
    hS hI hdU hdV hnU hnV hSigned hNonneg).trans
    (signedIntegral_le_spatialScore_sum hJ hJI hFinite hBalance hidU hidV hinU hinV)

/-- The standard projection split supplies all partition geometry. -/
theorem volumeReal_le_spatialScore_sum_middleHalf
    {S : Set Plane} {l r : ℝ} {dU dV nU nV : ℝ → ℝ} (hlr : l ≤ r)
    (hS : S ⊆ fourWallEnvelope (Icc l r) dU dV nU nV)
    (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hidU : IntegrableOn dU (Icc l r)) (hidV : IntegrableOn dV (Icc l r))
    (hinU : IntegrableOn nU (Icc l r)) (hinV : IntegrableOn nV (Icc l r))
    (hProjection : Icc l r ⊆ Prod.fst '' S) :
    volume.real S ≤
      spatialScore (Icc l r) (middleHalfInterval l r) dU nU +
        spatialScore (Icc l r) (middleHalfInterval l r) dV nV := by
  have hNonneg := signedFiberLength_nonneg_on_of_subset_projection hS hProjection
  have hNonnegAE : ∀ᵐ x ∂volume.restrict (Icc l r),
      0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hNonneg x hx
  exact volumeReal_le_spatialScore_sum_of_subset_fourWallEnvelope
    hS measurableSet_Icc (measurableSet_middleHalfInterval l r)
    (middleHalfInterval_subset hlr) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (middleHalfInterval_measure_balance hlr) hdU hdV hnU hnV hidU hidV hinU hinV hNonnegAE

/-! ## Exact actual-body decomposition -/

/-- The difference between the two scores and the actual body's area splits
into the nonnegative partition defect and the ordinary missing-envelope area. -/
theorem spatialScore_sum_sub_volumeReal_eq_defects
    {S : Set Plane} {I J : Set ℝ} {dU dV nU nV : ℝ → ℝ}
    (hS : S ⊆ fourWallEnvelope I dU dV nU nV) (hMeasS : MeasurableSet S)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hJI : J ⊆ I)
    (hFinite : volume I ≠ ⊤) (hBalance : volume.real J = volume.real (I \ J))
    (hdU : Measurable dU) (hdV : Measurable dV)
    (hnU : Measurable nU) (hnV : Measurable nV)
    (hidU : IntegrableOn dU I) (hidV : IntegrableOn dV I)
    (hinU : IntegrableOn nU I) (hinV : IntegrableOn nV I)
    (hNonneg : ∀ᵐ x ∂volume.restrict I,
      0 ≤ signedFiberLength (dU x) (dV x) (nU x) (nV x)) :
    spatialScore I J dU nU + spatialScore I J dV nV - volume.real S =
      integratedPartitionDefect I J dU dV nU nV +
        volume.real (fourWallEnvelope I dU dV nU nV \ S) := by
  have hPartition := integrated_partition_defect_identity
    hJ hJI hFinite hBalance hidU hidV hinU hinV
  have hSigned := integrableOn_signedFiberLength hFinite hidU hidV hinU hinV
  have hFill := volumeReal_sdiff_fourWallEnvelope_eq_signedIntegral_sub
    hS hMeasS hI hdU hdV hnU hnV hSigned hNonneg
  linarith

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
  have hDefects := spatialScore_sum_sub_volumeReal_eq_defects
    hS hMeasS hI hJ hJI hFinite hBalance hdU hdV hnU hnV hidU hidV hinU hinV hNonneg
  linarith

end AmbidextrousSofa
