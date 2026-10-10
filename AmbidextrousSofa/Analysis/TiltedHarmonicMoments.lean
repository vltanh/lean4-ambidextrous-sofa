import AmbidextrousSofa.Analysis.TiltedMomentumConvolution

/-!
# Exact harmonic first-floor and right-window moments

The cosine self-interaction is evaluated by applying the absolutely
continuous fundamental theorem to the squared sine and cosine
primitives. Together with the actual momentum reconstruction, this
calculates the two weighted momentum integrals and their literal sine
remainders.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

theorem forward_cosine_self_interaction
    {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hr : IntervalIntegrable r volume a b) :
    (∫ t in a..b, r t * forwardCosineConvolution r a t) =
      1 / 2 * ((∫ t in a..b, r t * Real.cos t) ^ 2 +
        (∫ t in a..b, r t * Real.sin t) ^ 2) := by
  let A : ℝ → ℝ := fun t => ∫ s in a..t, r s * Real.cos s
  let B : ℝ → ℝ := fun t => ∫ s in a..t, r s * Real.sin s
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hA : AbsolutelyContinuousOnInterval A a b :=
    hcos.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hB : AbsolutelyContinuousOnInterval B a b :=
    hsin.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE : AbsolutelyContinuousOnInterval (fun t => 1 / 2 * (A t ^ 2 + B t ^ 2)) a b := by
    simpa only [pow_two, Pi.mul_apply, Pi.add_apply] using
      (absolutelyContinuousOnInterval_const_real (1 / 2) a b).mul
        ((hA.mul hA).add (hB.mul hB))
  have hD : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s => 1 / 2 * (A s ^ 2 + B s ^ 2))
        (r t * forwardCosineConvolution r a t) t := by
    filter_upwards [hcos.ae_hasDerivAt_integral, hsin.ae_hasDerivAt_integral] with t hct hst ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    have hrt := hr.mono_set (show uIcc a t ⊆ uIcc a b by
      simpa only [uIcc_of_le ht'.1, uIcc_of_le hab] using
        (Icc_subset_Icc (le_refl a) ht'.2))
    have hd := (((hct ht a (by simp)).pow 2).add ((hst ht a (by simp)).pow 2)).const_mul (1 / 2)
    apply hd.congr_deriv
    rw [forwardCosineConvolution_eq_moments hrt]
    dsimp [A, B]
    ring
  have hi := ac_intervalIntegral_eq_sub_of_ae_hasDerivAt hE hD
  have hzero : 1 / 2 * (A a ^ 2 + B a ^ 2) = 0 := by simp [A, B]
  change (∫ t in a..b, r t * forwardCosineConvolution r a t) =
    1 / 2 * (A b ^ 2 + B b ^ 2) - 1 / 2 * (A a ^ 2 + B a ^ 2) at hi
  rw [hzero, sub_zero] at hi
  exact hi

theorem backward_cosine_self_interaction
    {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hr : IntervalIntegrable r volume a b) :
    (∫ t in a..b, r t * backwardCosineConvolution r b t) =
      1 / 2 * ((∫ t in a..b, r t * Real.cos t) ^ 2 +
        (∫ t in a..b, r t * Real.sin t) ^ 2) := by
  let A : ℝ → ℝ := fun t => ∫ s in t..b, r s * Real.cos s
  let B : ℝ → ℝ := fun t => ∫ s in t..b, r s * Real.sin s
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hA : AbsolutelyContinuousOnInterval A a b := absolutelyContinuousOnInterval_integral_left hcos
  have hB : AbsolutelyContinuousOnInterval B a b := absolutelyContinuousOnInterval_integral_left hsin
  have hE : AbsolutelyContinuousOnInterval (fun t => 1 / 2 * (A t ^ 2 + B t ^ 2)) a b := by
    simpa only [pow_two, Pi.mul_apply, Pi.add_apply] using
      (absolutelyContinuousOnInterval_const_real (1 / 2) a b).mul
        ((hA.mul hA).add (hB.mul hB))
  have hAeq : A = (fun t => -(∫ s in b..t, r s * Real.cos s)) := by
    funext t
    exact intervalIntegral.integral_symm b t
  have hBeq : B = (fun t => -(∫ s in b..t, r s * Real.sin s)) := by
    funext t
    exact intervalIntegral.integral_symm b t
  have hD : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s => 1 / 2 * (A s ^ 2 + B s ^ 2))
        (-(r t * backwardCosineConvolution r b t)) t := by
    filter_upwards [hcos.ae_hasDerivAt_integral, hsin.ae_hasDerivAt_integral] with t hct hst ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    have hrt := hr.mono_set (show uIcc t b ⊆ uIcc a b by
      simpa only [uIcc_of_le ht'.2, uIcc_of_le hab] using
        (Icc_subset_Icc ht'.1 (le_refl b)))
    have hAd : HasDerivAt A (-(r t * Real.cos t)) t := by
      rw [hAeq]
      exact (hct ht b (by simp)).neg
    have hBd : HasDerivAt B (-(r t * Real.sin t)) t := by
      rw [hBeq]
      exact (hst ht b (by simp)).neg
    have hd := ((hAd.pow 2).add (hBd.pow 2)).const_mul (1 / 2)
    apply hd.congr_deriv
    rw [backwardCosineConvolution_eq_moments hrt]
    dsimp [A, B]
    ring
  have hi := ac_intervalIntegral_eq_sub_of_ae_hasDerivAt hE hD
  rw [intervalIntegral.integral_neg] at hi
  have hzero : 1 / 2 * (A b ^ 2 + B b ^ 2) = 0 := by simp [A, B]
  change -(∫ t in a..b, r t * backwardCosineConvolution r b t) =
    1 / 2 * (A b ^ 2 + B b ^ 2) - 1 / 2 * (A a ^ 2 + B a ^ 2) at hi
  rw [hzero] at hi
  change (∫ t in a..b, r t * backwardCosineConvolution r b t) =
    1 / 2 * (A a ^ 2 + B a ^ 2)
  linarith

theorem firstUnit_initial_harmonic_moment
    {p q u v : ℝ → ℝ} {γ C S h eR : ℝ} (hγ : 0 ≤ γ)
    (hp : AbsolutelyContinuousOnInterval p 0 γ)
    (hq : AbsolutelyContinuousOnInterval q 0 γ)
    (hu : IntervalIntegrable u volume 0 γ) (hv : IntervalIntegrable v volume 0 γ)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 γ),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hp0 : p 0 = eR + h) (hq0 : q 0 = 3 * C - 1)
    (hS : (∫ t in 0..γ, (1 - v t) * Real.cos t) = S)
    (hh : (∫ t in 0..γ, (1 - v t) * Real.sin t) = h) :
    (∫ t in 0..γ, (q t + 1) * (1 - v t)) =
      3 * C * S - S ^ 2 / 2 + eR * h + h ^ 2 / 2 +
        firstUnitLeftRemainder (fun t => 1 - v t) u γ := by
  let r : ℝ → ℝ := fun t => 1 - v t
  have hr : IntervalIntegrable r volume 0 γ := (intervalIntegrable_const (c := (1 : ℝ))).sub hv
  have hrc := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hrs := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hru := hr.mul_continuousOn (absolutelyContinuousOnInterval_forwardSineConvolution hγ hu).continuousOn
  have hrr := hr.mul_continuousOn (absolutelyContinuousOnInterval_forwardCosineConvolution hγ hr).continuousOn
  have hpoint : ∀ t ∈ Icc (0 : ℝ) γ,
      q t + 1 = 3 * C * Real.cos t + (eR + h) * Real.sin t +
        forwardSineConvolution u 0 t - forwardCosineConvolution r 0 t := by
    intro t ht
    have hsub : uIcc 0 t ⊆ uIcc 0 γ := by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hγ] using
        (Icc_subset_Icc (le_refl (0 : ℝ)) ht.2)
    have hvt := hv.mono_set hsub
    have heq := secondMomentum_forward_convolution ht.1 (hp.mono hsub) (hq.mono hsub)
      (hu.mono_set hsub) hvt (ae_restrict_Icc_subinterval le_rfl ht.2 hode)
    have hc := forwardCosineConvolution_add_complement hvt
    rw [hp0, hq0] at heq
    dsimp [r]
    nlinarith
  have hint : (∫ t in 0..γ, (q t + 1) * r t) =
      3 * C * (∫ t in 0..γ, r t * Real.cos t) +
      (eR + h) * (∫ t in 0..γ, r t * Real.sin t) +
      (∫ t in 0..γ, r t * forwardSineConvolution u 0 t) -
        ∫ t in 0..γ, r t * forwardCosineConvolution r 0 t := by
    calc
      _ = ∫ t in 0..γ,
          3 * C * (r t * Real.cos t) + (eR + h) * (r t * Real.sin t) +
          r t * forwardSineConvolution u 0 t - r t * forwardCosineConvolution r 0 t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [hpoint t (by simpa only [uIcc_of_le hγ] using ht)]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (((hrc.const_mul _).add (hrs.const_mul _)).add hru) hrr,
          intervalIntegral.integral_add ((hrc.const_mul _).add (hrs.const_mul _)) hru,
          intervalIntegral.integral_add (hrc.const_mul _) (hrs.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [forward_cosine_self_interaction hγ hr] at hint
  change (∫ t in 0..γ, (q t + 1) * r t) = _
  change (∫ t in 0..γ, r t * Real.cos t) = S at hS
  change (∫ t in 0..γ, r t * Real.sin t) = h at hh
  rw [hS, hh] at hint
  change (∫ t in 0..γ, (q t + 1) * r t) =
    3 * C * S - S ^ 2 / 2 + eR * h + h ^ 2 / 2 +
      ∫ t in 0..γ, r t * forwardSineConvolution u 0 t
  nlinarith

theorem firstUnit_right_harmonic_moment
    {p q u v : ℝ → ℝ} {β C T z eL : ℝ} (hβ : β ≤ Real.pi / 2)
    (hp : AbsolutelyContinuousOnInterval p β (Real.pi / 2))
    (hq : AbsolutelyContinuousOnInterval q β (Real.pi / 2))
    (hu : IntervalIntegrable u volume β (Real.pi / 2))
    (hv : IntervalIntegrable v volume β (Real.pi / 2))
    (hode : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hpL : p (Real.pi / 2) = 1 - 3 * C - T) (hqL : q (Real.pi / 2) = -eL)
    (hT : (∫ t in β..(Real.pi / 2), (1 - u t) * Real.sin t) = T)
    (hz : (∫ t in β..(Real.pi / 2), (1 - u t) * Real.cos t) = z) :
    (∫ t in β..(Real.pi / 2), firstUnitGainDensity (p t) (u t)) =
      3 * C * T + T ^ 2 / 2 + eL * z - z ^ 2 / 2 +
        firstUnitRightRemainder (fun t => 1 - u t) v β (Real.pi / 2) := by
  let r : ℝ → ℝ := fun t => 1 - u t
  have hr : IntervalIntegrable r volume β (Real.pi / 2) := (intervalIntegrable_const (c := (1 : ℝ))).sub hu
  have hrc := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hrs := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hrv := hr.mul_continuousOn (absolutelyContinuousOnInterval_backwardSineConvolution hβ hv).continuousOn
  have hrr := hr.mul_continuousOn (absolutelyContinuousOnInterval_backwardCosineConvolution hβ hr).continuousOn
  have hpoint : ∀ t ∈ Icc β (Real.pi / 2),
      1 - p t = (3 * C + T) * Real.sin t + eL * Real.cos t +
        backwardSineConvolution v (Real.pi / 2) t - backwardCosineConvolution r (Real.pi / 2) t := by
    intro t ht
    have hsub : uIcc t (Real.pi / 2) ⊆ uIcc β (Real.pi / 2) := by
      simpa only [uIcc_of_le ht.2, uIcc_of_le hβ] using
        (Icc_subset_Icc ht.1 (le_refl (Real.pi / 2)))
    have hut := hu.mono_set hsub
    have heq := firstMomentum_backward_convolution ht.2 (hp.mono hsub) (hq.mono hsub)
      hut (hv.mono_set hsub) (ae_restrict_Icc_subinterval ht.1 le_rfl hode)
    have hc := backwardCosineConvolution_add_complement hut
    rw [hpL, hqL] at heq
    dsimp [r]
    nlinarith
  have hint : (∫ t in β..(Real.pi / 2), (1 - p t) * r t) =
      (3 * C + T) * (∫ t in β..(Real.pi / 2), r t * Real.sin t) +
      eL * (∫ t in β..(Real.pi / 2), r t * Real.cos t) +
      (∫ t in β..(Real.pi / 2), r t * backwardSineConvolution v (Real.pi / 2) t) -
        ∫ t in β..(Real.pi / 2), r t * backwardCosineConvolution r (Real.pi / 2) t := by
    calc
      _ = ∫ t in β..(Real.pi / 2),
          (3 * C + T) * (r t * Real.sin t) + eL * (r t * Real.cos t) +
          r t * backwardSineConvolution v (Real.pi / 2) t -
            r t * backwardCosineConvolution r (Real.pi / 2) t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [hpoint t (by simpa only [uIcc_of_le hβ] using ht)]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (((hrs.const_mul _).add (hrc.const_mul _)).add hrv) hrr,
          intervalIntegral.integral_add ((hrs.const_mul _).add (hrc.const_mul _)) hrv,
          intervalIntegral.integral_add (hrs.const_mul _) (hrc.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [backward_cosine_self_interaction hβ hr] at hint
  change (∫ t in β..(Real.pi / 2), (1 - p t) * r t) = _
  change (∫ t in β..(Real.pi / 2), r t * Real.sin t) = T at hT
  change (∫ t in β..(Real.pi / 2), r t * Real.cos t) = z at hz
  rw [hT, hz] at hint
  change (∫ t in β..(Real.pi / 2), (1 - p t) * r t) =
    3 * C * T + T ^ 2 / 2 + eL * z - z ^ 2 / 2 +
      ∫ t in β..(Real.pi / 2), r t * backwardSineConvolution v (Real.pi / 2) t
  nlinarith

end AmbidextrousSofa.Analysis
