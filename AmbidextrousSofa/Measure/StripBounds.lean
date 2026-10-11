module

public import AmbidextrousSofa.Measure.Fibers
public import AmbidextrousSofa.Geometry.Hallway

@[expose] public section

/-!
# Horizontal sections of strips and of the wrong-way hallway

These are direct area bounds for subsets of actual strips and hallways. At
the wrong-handed angle `-π/4`, every horizontal hallway section lies in an
interval of length `√2`, regardless of the two hallway offsets. The resulting area
obstruction uses only the incoming unit strip, not convexity or full height.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- A measurable family of horizontal sections of length at most `√2` in the incoming
unit strip bounds the area of every subset, including nonconvex subsets. -/
theorem volumeReal_le_sqrt_two_of_horizontal_intervals {S : Set Plane} {left right : ℝ → ℝ}
    (hstrip : S ⊆ unitStrip) (hleft : Measurable left) (hright : Measurable right)
    (hwidth : ∀ y, right y - left y ≤ √2) (hS : ∀ p ∈ S, p.1 ∈ Icc (left p.2) (right p.2)) :
    volume.real S ≤ √2 := by
  refine ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg 2) ?_
  calc
    volume S ≤ volume (Prod.swap ⁻¹' verticalIntervalRegion (Icc 0 1) left right) :=
      measure_mono fun p hp => ⟨hstrip hp, hS p hp⟩
    _ = ∫⁻ y in Icc 0 1, ENNReal.ofReal (right y - left y) := by
      rw [Measure.volume_eq_prod, Measure.measurePreserving_swap.measure_preimage_emb
        MeasurableEquiv.prodComm.measurableEmbedding, ← Measure.volume_eq_prod,
        volume_verticalIntervalRegion_eq_lintegral measurableSet_Icc hleft hright]
    _ ≤ ∫⁻ _ in Icc 0 1, ENNReal.ofReal √2 :=
      lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hwidth y)
    _ = ENNReal.ofReal √2 := by simp

theorem volumeReal_le_sqrt_two_of_unitStrip_and_smallAngleStrip
    {S : Set Plane} {θ a : ℝ} (hstrip : S ⊆ unitStrip)
    (hθ : θ ∈ Icc (-(Real.pi / 4)) (Real.pi / 4))
    (hframe : ∀ p ∈ S, a ≤ coordDot p (unitNormal θ) ∧
      coordDot p (unitNormal θ) ≤ a + 1) :
    volume.real S ≤ Real.sqrt 2 := by
  have hcos : √2 / 2 ≤ Real.cos θ := by
    simpa only [Real.cos_abs, Real.cos_pi_div_four] using Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg θ) (by linarith [Real.pi_pos]) (abs_le.2 hθ)
  have hc : 0 < Real.cos θ := lt_of_lt_of_le (by positivity) hcos
  refine volumeReal_le_sqrt_two_of_horizontal_intervals
    (left := fun y => (a - Real.sin θ * y) / Real.cos θ)
    (right := fun y => (a + 1 - Real.sin θ * y) / Real.cos θ)
    hstrip (by fun_prop) (by fun_prop) (fun y => ?_) fun p hp => ?_
  · rw [← sub_div, div_le_iff₀ hc]
    linarith [mul_le_mul_of_nonneg_left hcos (Real.sqrt_nonneg 2),
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · obtain ⟨hlo, hhi⟩ := hframe p hp
    simp only [coordDot, unitNormal] at hlo hhi
    exact ⟨(div_le_iff₀ hc).2 (by linarith), (le_div_iff₀ hc).2 (by linarith)⟩

/-- Visiting the wrong-handed angle forces the actual body area below `√2`.
Both hallway offsets are arbitrary and the body need not be convex. -/
theorem volumeReal_le_sqrt_two_of_wrongWay_frameHall {S : Set Plane}
    (hstrip : S ⊆ unitStrip) {a b : ℝ}
    (hhall : S ⊆ frameHall (unitNormal (-(Real.pi / 4)))
      (companionNormal (-(Real.pi / 4))) a b) :
    volume.real S ≤ Real.sqrt 2 := by
  refine volumeReal_le_sqrt_two_of_horizontal_intervals
    (left := fun y => min (√2 * a + y) (√2 * b - y))
    (right := fun y => min (√2 * a + y) (√2 * b - y) + √2)
    hstrip (by fun_prop) (by fun_prop) (fun y => (add_sub_cancel_left _ _).le) fun p hp => ?_
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs := Real.sqrt_nonneg 2
  have hU : √2 * coordDot p (unitNormal (-(Real.pi / 4))) = p.1 - p.2 := by
    simp only [coordDot, unitNormal, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    linear_combination (p.1 - p.2) / 2 * h2
  have hV : √2 * coordDot p (companionNormal (-(Real.pi / 4))) = p.1 + p.2 := by
    simp only [coordDot, companionNormal, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
      Real.sin_pi_div_four, neg_neg]
    linear_combination (p.1 + p.2) / 2 * h2
  obtain ⟨hu, hv, hin⟩ := hhall hp
  have := mul_le_mul_of_nonneg_left hu hs
  have := mul_le_mul_of_nonneg_left hv hs
  refine ⟨min_le_iff.2 (hin.imp (fun h => ?_) fun h => ?_),
    (le_min (by linarith) (by linarith)).trans_eq (min_add_add_right _ _ _)⟩
  · linarith [mul_le_mul_of_nonneg_left h hs]
  · linarith [mul_le_mul_of_nonneg_left h hs]

end AmbidextrousSofa
