module

public import AmbidextrousSofa.Measure.Fibers

@[expose] public section

/-!
# Connected regions between continuous ordered vertical graphs

The region is the actual continuous image of its horizontal base times the
closed unit interval. The construction also covers collapsed fibers. It
does not require the lower graph to be convex or the upper graph concave.
-/

open Set

namespace AmbidextrousSofa

theorem isConnected_verticalIntervalRegion {I : Set ℝ} {lower upper : ℝ → ℝ}
    (hI : IsConnected I) (hlower : ContinuousOn lower I)
    (hupper : ContinuousOn upper I) (horder : ∀ x ∈ I, lower x ≤ upper x) :
    IsConnected (verticalIntervalRegion I lower upper) := by
  have hlo : ContinuousOn (fun p : Plane => lower p.1) (I ×ˢ Icc (0 : ℝ) 1) :=
    hlower.comp continuous_fst.continuousOn fun _ hp => hp.1
  have hup : ContinuousOn (fun p : Plane => upper p.1) (I ×ˢ Icc (0 : ℝ) 1) :=
    hupper.comp continuous_fst.continuousOn fun _ hp => hp.1
  convert (hI.prod (isConnected_Icc zero_le_one)).image
    (fun p : Plane => (p.1, lower p.1 + p.2 * (upper p.1 - lower p.1)))
    (continuous_fst.continuousOn.prodMk (hlo.add (continuous_snd.continuousOn.mul (hup.sub hlo))))
  ext p
  constructor
  · rintro ⟨hpI, h1, h2⟩
    have h0 : upper p.1 - lower p.1 = 0 → p.2 - lower p.1 = 0 := fun h => by linarith
    refine ⟨(p.1, (p.2 - lower p.1) / (upper p.1 - lower p.1)), ⟨hpI,
      div_nonneg (by linarith) (by linarith), div_le_one_of_le₀ (by linarith) (by linarith)⟩,
      Prod.ext rfl ?_⟩
    simp only [div_mul_cancel_of_imp h0, add_sub_cancel]
  · rintro ⟨q, ⟨hqI, hq0, hq1⟩, rfl⟩
    have h := sub_nonneg.2 (horder q.1 hqI)
    simp only [mem_verticalIntervalRegion]
    exact ⟨hqI, le_add_of_nonneg_right (mul_nonneg hq0 h),
      by linarith [mul_le_of_le_one_left h hq1]⟩

end AmbidextrousSofa
