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
  have hroof := capRoof_upperCap hK hK0
  -- Convexity and reflection supply the lower hull wall, so the trimmed hull is
  -- exactly the four-wall envelope, including every endpoint fiber.
  have htrim : symmetricTrim K N = fourWallEnvelope (horizontalProjection K)
      (roofDeficit (upperCap K)) (roofDeficit (upperCap K)) N N := by
    ext p
    simp only [symmetricTrim, fourWallEnvelope, fourWallFiber, roofDeficit, hroof, sub_sub_cancel]
    constructor
    · rintro ⟨hp, hlo, hhi⟩
      have h : 1 - p.2 ≤ capRoof K p.1 := le_capRoof hK (hreflect p hp)
      exact ⟨mem_image_of_mem Prod.fst hp, by linarith, hlo, le_capRoof hK hp, by linarith⟩
    · rintro ⟨hx, hlo, hnlo, hhi, hnhi⟩
      have hl : (p.1, 1 - capRoof K p.1) ∈ K := hreflect _ (capRoof_mem hK hx)
      exact ⟨(convex_verticalFiber hconv p.1).ordConnected.out hl (capRoof_mem hK hx) ⟨hlo, hhi⟩,
        hnlo, by linarith⟩
  -- The support restriction removes the overlap between roof deficit and niche.
  have hfiber : ∀ x ∈ horizontalProjection K, signedFiberLength (roofDeficit (upperCap K) x)
      (roofDeficit (upperCap K) x) (N x) (N x) = 2 * capRoof (upperCap K) x - 1 - 2 * N x := by
    intro x hx
    simp only [signedFiberLength, roofDeficit]
    rcases hseparate x hx with h | h
    · rw [h, sub_self, max_eq_right (hNnonneg x hx)]; ring
    · rw [h, max_eq_left (sub_nonneg.2 (capRoof_le_one hcap.isCompact hcap.inStrip x))]; ring
  have hprojection := isCompact_horizontalProjection hK
  have hI := hprojection.measurableSet
  have hfinite : volume (horizontalProjection K) ≠ ⊤ := hprojection.measure_ne_top
  have hP : horizontalProjection K =
      Icc (horizontalLeft (upperCap K)) (horizontalRight (upperCap K)) := by
    rw [← horizontalProjection_upperCap hK0,
      hcap.horizontalProjection_eq_Icc]
  have hroofI : IntegrableOn (capRoof (upperCap K)) (horizontalProjection K) :=
    hP ▸ hcap.integrableOn_capRoof_Icc _ _
  have hdI : IntegrableOn (roofDeficit (upperCap K)) (horizontalProjection K) :=
    hP ▸ hcap.integrableOn_roofDeficit_Icc _ _
  have hNI : IntegrableOn N (horizontalProjection K) :=
    hN.continuousOn.integrableOn_compact hprojection
  have hvol := volumeReal_fourWallEnvelope_eq_signedIntegral hI hcap.measurable_roofDeficit
    hcap.measurable_roofDeficit hN.measurable hN.measurable
    (integrableOn_signedFiberLength hfinite hdI hdI hNI hNI) <| by
      filter_upwards [ae_restrict_mem hI] with x hx
      have h : 1 - capRoof K x ≤ capRoof K x := le_capRoof hK (hreflect _ (capRoof_mem hK hx))
      rw [hfiber x hx, hroof]
      rcases hseparate x hx with h' | h' <;> linarith [hroof x, hNhalf x hx]
  have hOne := integrableOn_const (μ := volume) (C := (1 : ℝ)) hfinite
  have h2 := hroofI.const_mul 2
  rw [← htrim, setIntegral_congr_fun hI hfiber, integral_sub (IntegrableOn.fun_sub h2 hOne)
    (hNI.const_mul 2), integral_sub h2 hOne, integral_const_mul, integral_const_mul,
    setIntegral_const, smul_eq_mul, mul_one] at hvol
  have hwidth : volume.real (horizontalProjection K) = capWidth (upperCap K) := by
    rw [hP, Real.volume_real_Icc_of_le
      (horizontalLeft_le_horizontalRight hcap.nonempty hcap.isCompact)]
    rfl
  rw [hvol, hwidth, hcap.volumeReal_eq_integral_capRoof, ← hP]

end AmbidextrousSofa
