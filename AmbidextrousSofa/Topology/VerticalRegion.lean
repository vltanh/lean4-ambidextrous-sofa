import AmbidextrousSofa.Measure.Fibers

/-!
# Connected regions between continuous ordered vertical graphs

The region is the actual continuous image of its horizontal base times the
closed unit interval. The construction also covers collapsed fibers. It
does not require the lower graph to be convex or the upper graph concave.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def verticalRegionParametrization (lower upper : ℝ → ℝ) (p : Plane) : Plane :=
  (p.1, lower p.1 + p.2 * (upper p.1 - lower p.1))

theorem verticalIntervalRegion_eq_image {I : Set ℝ} {lower upper : ℝ → ℝ}
    (horder : ∀ x ∈ I, lower x ≤ upper x) :
    verticalIntervalRegion I lower upper =
      verticalRegionParametrization lower upper '' (I ×ˢ Icc (0 : ℝ) 1) := by
  ext p
  constructor
  · rintro ⟨hpI, hlo, hup⟩
    by_cases heq : lower p.1 = upper p.1
    · have hp : p.2 = lower p.1 := by linarith
      refine ⟨(p.1, 0), ⟨hpI, ⟨le_rfl, by norm_num⟩⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simpa only [verticalRegionParametrization, zero_mul, add_zero] using hp.symm
    · have hgap : 0 < upper p.1 - lower p.1 :=
        sub_pos.mpr (lt_of_le_of_ne (horder p.1 hpI) heq)
      let t : ℝ := (p.2 - lower p.1) / (upper p.1 - lower p.1)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hgap.le
      have ht1 : t ≤ 1 := by
        rw [div_le_iff₀ hgap]
        linarith
      refine ⟨(p.1, t), ⟨hpI, ⟨ht0, ht1⟩⟩, ?_⟩
      apply Prod.ext
      · rfl
      · change lower p.1 + t * (upper p.1 - lower p.1) = p.2
        dsimp only [t]
        rw [div_mul_cancel₀ _ hgap.ne']
        ring
  · rintro ⟨q, ⟨hqI, hq0, hq1⟩, rfl⟩
    have hgap : 0 ≤ upper q.1 - lower q.1 := sub_nonneg.mpr (horder q.1 hqI)
    refine ⟨hqI, ?_, ?_⟩
    · change lower q.1 ≤ lower q.1 + q.2 * (upper q.1 - lower q.1)
      exact le_add_of_nonneg_right (mul_nonneg hq0 hgap)
    · change lower q.1 + q.2 * (upper q.1 - lower q.1) ≤ upper q.1
      have h := mul_le_mul_of_nonneg_right hq1 hgap
      linarith

theorem continuousOn_verticalRegionParametrization {I : Set ℝ} {lower upper : ℝ → ℝ}
    (hlower : ContinuousOn lower I) (hupper : ContinuousOn upper I) :
    ContinuousOn (verticalRegionParametrization lower upper) (I ×ˢ Icc (0 : ℝ) 1) := by
  have hlo : ContinuousOn (fun p : Plane => lower p.1) (I ×ˢ Icc (0 : ℝ) 1) :=
    hlower.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hup : ContinuousOn (fun p : Plane => upper p.1) (I ×ˢ Icc (0 : ℝ) 1) :=
    hupper.comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact continuous_fst.continuousOn.prodMk
    (hlo.add (continuous_snd.continuousOn.mul (hup.sub hlo)))

theorem isConnected_verticalIntervalRegion {I : Set ℝ} {lower upper : ℝ → ℝ}
    (hI : IsConnected I) (hlower : ContinuousOn lower I)
    (hupper : ContinuousOn upper I) (horder : ∀ x ∈ I, lower x ≤ upper x) :
    IsConnected (verticalIntervalRegion I lower upper) := by
  rw [verticalIntervalRegion_eq_image horder]
  exact (hI.prod (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))).image _
    (continuousOn_verticalRegionParametrization hlower hupper)

end AmbidextrousSofa
