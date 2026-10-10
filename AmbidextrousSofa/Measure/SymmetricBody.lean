module

public import AmbidextrousSofa.Measure.GraphIntegral
public import AmbidextrousSofa.Geometry.Reflection

@[expose] public section

/-!
# The area of a symmetric hull with two actual niches removed

Compactness and convexity identify the original hull fibers between the
roof and its reflection. A barrier at most one half preserves the actual
midline of every fiber. If the barrier is supported where the roof equals
one, the four-wall length has no overlap loss and integrates exactly to
twice the cap area minus the projection width and the two niche areas.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def symmetricTrim (K : Set Plane) (N : ℝ → ℝ) : Set Plane :=
  {p | p ∈ K ∧ N p.1 ≤ p.2 ∧ N p.1 ≤ 1 - p.2}

theorem verticalFiber_eq_Icc_of_reflection {K : Set Plane}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) {x : ℝ}
    (hx : x ∈ horizontalProjection K) :
    verticalFiber K x = Icc (1 - capRoof K x) (capRoof K x) := by
  have hroof := capRoof_mem hK hx
  have hlower : (x, 1 - capRoof K x) ∈ K := hreflect _ hroof
  ext y
  constructor
  · intro hy
    have hyUpper := le_capRoof hK hy
    have hyLower := le_capRoof hK (hreflect (x, y) hy)
    change 1 - y ≤ capRoof K x at hyLower
    exact ⟨by linarith, hyUpper⟩
  · intro hy
    exact (convex_verticalFiber hconv x).ordConnected.out hlower hroof hy

theorem mem_symmetricHull_iff_roof {K : Set Plane}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) (p : Plane) :
    p ∈ K ↔ p.1 ∈ horizontalProjection K ∧
      1 - capRoof K p.1 ≤ p.2 ∧ p.2 ≤ capRoof K p.1 := by
  constructor
  · intro hp
    have hx : p.1 ∈ horizontalProjection K := mem_image_of_mem Prod.fst hp
    refine ⟨hx, ?_⟩
    have hfiber : p.2 ∈ verticalFiber K p.1 := hp
    rwa [verticalFiber_eq_Icc_of_reflection hK hconv hreflect hx] at hfiber
  · rintro ⟨hx, hy⟩
    have hfiber : p.2 ∈ verticalFiber K p.1 := by
      rw [verticalFiber_eq_Icc_of_reflection hK hconv hreflect hx]
      exact hy
    exact hfiber

theorem half_le_capRoof_of_reflection {K : Set Plane} (hK : IsCompact K)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) {x : ℝ}
    (hx : x ∈ horizontalProjection K) : 1 / 2 ≤ capRoof K x := by
  have h := le_capRoof hK (hreflect _ (capRoof_mem hK hx))
  change 1 - capRoof K x ≤ capRoof K x at h
  linarith

/-- This is equality with the actual trimmed hull, including every endpoint
fiber. Convexity and reflection supply the lower hull wall. -/
theorem symmetricTrim_eq_fourWallEnvelope {K : Set Plane}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hstrip : K ⊆ unitStrip)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) (N : ℝ → ℝ) :
    symmetricTrim K N = fourWallEnvelope (horizontalProjection K)
      (roofDeficit (upperCap K)) (roofDeficit (upperCap K)) N N := by
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hstrip hp).1
  ext p
  change (p ∈ K ∧ N p.1 ≤ p.2 ∧ N p.1 ≤ 1 - p.2) ↔
    (p.1 ∈ horizontalProjection K ∧
      roofDeficit (upperCap K) p.1 ≤ p.2 ∧ N p.1 ≤ p.2 ∧
      p.2 ≤ 1 - roofDeficit (upperCap K) p.1 ∧ p.2 ≤ 1 - N p.1)
  rw [mem_symmetricHull_iff_roof hK hconv hreflect]
  unfold roofDeficit
  rw [capRoof_upperCap hK hK0]
  constructor
  · rintro ⟨⟨hx, hlo, hhi⟩, hnlo, hnhi⟩
    exact ⟨hx, hlo, hnlo, by linarith, by linarith⟩
  · rintro ⟨hx, hlo, hnlo, hhi, hnhi⟩
    exact ⟨⟨hx, hlo, by linarith⟩, hnlo, by linarith⟩

theorem symmetricTrim_signedFiber_nonneg {K : Set Plane}
    (hK : IsCompact K) (hstrip : K ⊆ unitStrip)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) {N : ℝ → ℝ}
    (hNhalf : ∀ x ∈ horizontalProjection K, N x ≤ 1 / 2)
    {x : ℝ} (hx : x ∈ horizontalProjection K) :
    0 ≤ signedFiberLength (roofDeficit (upperCap K) x)
      (roofDeficit (upperCap K) x) (N x) (N x) := by
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hstrip hp).1
  have hroof : 1 / 2 ≤ capRoof (upperCap K) x := by
    rw [capRoof_upperCap hK hK0]
    exact half_le_capRoof_of_reflection hK hreflect hx
  have hmax : max (roofDeficit (upperCap K) x) (N x) ≤ 1 / 2 :=
    max_le (by unfold roofDeficit; linarith) (hNhalf x hx)
  unfold signedFiberLength
  linarith

theorem symmetricTrim_signedFiber_eq {U : Set Plane} (hU : IsDownwardCap U)
    {N : ℝ → ℝ} {x : ℝ} (hN : 0 ≤ N x)
    (hseparate : capRoof U x = 1 ∨ N x = 0) :
    signedFiberLength (roofDeficit U x) (roofDeficit U x) (N x) (N x) =
      2 * capRoof U x - 1 - 2 * N x := by
  unfold signedFiberLength roofDeficit
  rcases hseparate with hroof | hn
  · rw [hroof, sub_self, max_eq_right hN]
    ring
  · have hd : 0 ≤ 1 - capRoof U x := sub_nonneg.mpr (capRoof_le_one hU.isCompact hU.inStrip x)
    rw [hn, max_eq_left hd]
    ring

/-- The ordinary area of the original trimmed hull. Fiber nonnegativity is
derived from the retained midline; the support restriction removes overlap
between the roof deficit and each niche. -/
theorem volumeReal_symmetricTrim_eq_cap_area {K : Set Plane} (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (hstrip : K ⊆ unitStrip)
    (hreflect : ∀ p ∈ K, reflect p ∈ K) {N : ℝ → ℝ}
    (hN : Continuous N) (hNnonneg : ∀ x ∈ horizontalProjection K, 0 ≤ N x)
    (hNhalf : ∀ x ∈ horizontalProjection K, N x ≤ 1 / 2)
    (hseparate : ∀ x ∈ horizontalProjection K, capRoof (upperCap K) x = 1 ∨ N x = 0) :
    volume.real (symmetricTrim K N) = 2 * volume.real (upperCap K) -
      capWidth (upperCap K) - 2 * ∫ x in horizontalProjection K, N x := by
  have hcap := isDownwardCap_upperCap hne hK hconv hstrip
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hstrip hp).1
  have hprojection := isCompact_horizontalProjection hK
  have hI : MeasurableSet (horizontalProjection K) := hprojection.measurableSet
  have hfinite : volume (horizontalProjection K) ≠ ⊤ := hprojection.measure_ne_top
  have hproj := horizontalProjection_eq_Icc hne hK hconv
  have hroofI : IntegrableOn (capRoof (upperCap K)) (horizontalProjection K) := by
    rw [hproj]
    exact hcap.integrableOn_capRoof_Icc _ _
  have hdI : IntegrableOn (roofDeficit (upperCap K)) (horizontalProjection K) := by
    rw [hproj]
    exact hcap.integrableOn_roofDeficit_Icc _ _
  have hNI : IntegrableOn N (horizontalProjection K) := hN.continuousOn.integrableOn_compact hprojection
  have hSigned := integrableOn_signedFiberLength hfinite hdI hdI hNI hNI
  have hNonneg : ∀ᵐ x ∂volume.restrict (horizontalProjection K),
      0 ≤ signedFiberLength (roofDeficit (upperCap K) x)
        (roofDeficit (upperCap K) x) (N x) (N x) := by
    filter_upwards [ae_restrict_mem hI] with x hx
    exact symmetricTrim_signedFiber_nonneg hK hstrip hreflect hNhalf hx
  have hvol := volumeReal_fourWallEnvelope_eq_signedIntegral hI
    hcap.measurable_roofDeficit hcap.measurable_roofDeficit
    hN.measurable hN.measurable hSigned hNonneg
  rw [← symmetricTrim_eq_fourWallEnvelope hK hconv hstrip hreflect N] at hvol
  have hlength : (∫ x in horizontalProjection K,
      signedFiberLength (roofDeficit (upperCap K) x)
        (roofDeficit (upperCap K) x) (N x) (N x)) =
      ∫ x in horizontalProjection K, 2 * capRoof (upperCap K) x - 1 - 2 * N x := by
    apply setIntegral_congr_fun hI
    intro x hx
    exact symmetricTrim_signedFiber_eq hcap (hNnonneg x hx) (hseparate x hx)
  rw [hlength] at hvol
  have hOne : IntegrableOn (fun _x : ℝ => (1 : ℝ)) (horizontalProjection K) :=
    integrableOn_const hfinite
  have hroof2 : IntegrableOn (fun x => 2 * capRoof (upperCap K) x) (horizontalProjection K) :=
    hroofI.const_mul 2
  have hroof21 : IntegrableOn (fun x => 2 * capRoof (upperCap K) x - 1)
      (horizontalProjection K) := hroof2.sub hOne
  have hN2 : IntegrableOn (fun x => 2 * N x) (horizontalProjection K) := hNI.const_mul 2
  rw [integral_sub hroof21 hN2,
    integral_sub hroof2 hOne, integral_const_mul, integral_const_mul,
    setIntegral_const, smul_eq_mul, mul_one] at hvol
  have hcapArea := hcap.volumeReal_eq_integral_capRoof
  rw [← horizontalProjection_eq_Icc hcap.nonempty hcap.isCompact hcap.convex,
    horizontalProjection_upperCap hK0] at hcapArea
  have hwidth : volume.real (horizontalProjection K) = capWidth (upperCap K) := by
    rw [← horizontalProjection_upperCap hK0,
      horizontalProjection_eq_Icc hcap.nonempty hcap.isCompact hcap.convex,
      Real.volume_real_Icc_of_le
        (horizontalLeft_le_horizontalRight hcap.nonempty hcap.isCompact)]
    rfl
  rw [hwidth, ← hcapArea] at hvol
  exact hvol

/-- Restrict a barrier integral to its actual support interval or measurable
support set. This uses the ordinary finite integral, including its sign. -/
theorem setIntegral_eq_subset_of_zero_off {I J : Set ℝ} {f : ℝ → ℝ}
    (hIset : MeasurableSet I) (hJ : MeasurableSet J) (hI : IntegrableOn f I) (hJI : J ⊆ I)
    (hzero : ∀ x ∈ I \ J, f x = 0) :
    (∫ x in I, f x) = ∫ x in J, f x := by
  have hdifference : (∫ x in I \ J, f x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (hIset.diff hJ)] with x hx
    exact hzero x hx
  have hsplit := setIntegral_sdiff hJ hI hJI
  rw [hdifference] at hsplit
  linarith

end AmbidextrousSofa
