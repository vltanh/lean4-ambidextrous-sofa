module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.Hallway

@[expose] public section

/-!
# Determination of a downward cap by its upward supports

The two quarter families cover the upper half-plane of directions. In a
downward direction every support maximum lies on the actual baseline, so
it is already determined by the horizontal supports. The polar argument
is the same coordinate construction used for the reference body's hull.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem exists_quarter_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      (a, b) = r • unitNormal t := by
  by_cases ha0 : a = 0
  · refine ⟨b, hb, Real.pi / 2, ⟨by linarith [Real.pi_pos], le_rfl⟩, ?_⟩
    simp [ha0, unitNormal]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let t := Real.arctan (b / a)
    have hc : 0 < Real.cos t := Real.cos_arctan_pos _
    have ht : t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.arctan_nonneg.mpr (div_nonneg hb ha), (Real.arctan_lt_pi_div_two _).le⟩
    have htan : Real.sin t / Real.cos t = b / a := by
      simpa only [Real.tan_eq_sin_div_cos] using Real.tan_arctan (b / a)
    have hs : Real.sin t = b / a * Real.cos t := (div_eq_iff hc.ne').mp htan
    refine ⟨a / Real.cos t, (div_pos hap hc).le, t, ht, ?_⟩
    apply Prod.ext
    · change a = a / Real.cos t * Real.cos t
      exact (div_mul_cancel₀ a hc.ne').symm
    · change b = a / Real.cos t * Real.sin t
      rw [hs]
      field_simp [ha0, hc.ne'] <;> ring

theorem exists_upper_polar {v : Plane} (hv : 0 ≤ v.2) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      v = r • unitNormal t ∨ v = r • companionNormal t := by
  by_cases hx : 0 ≤ v.1
  · obtain ⟨r, hr, t, ht, h⟩ := exists_quarter_polar hx hv
    exact ⟨r, hr, t, ht, Or.inl (by simpa only [Prod.mk.eta] using h)⟩
  · obtain ⟨r, hr, t, ht, h⟩ := exists_quarter_polar hv (neg_nonneg.mpr (le_of_not_ge hx))
    refine ⟨r, hr, t, ht, Or.inr ?_⟩
    have hx' := congrArg Prod.snd h
    have hy' := congrArg Prod.fst h
    apply Prod.ext
    · change v.1 = r * -Real.sin t
      change -v.1 = r * Real.sin t at hx'
      linarith
    · change v.2 = r * Real.cos t
      exact hy'

theorem IsDownwardCap.support_eq_horizontal_of_snd_nonpos {U : Set Plane}
    (hU : IsDownwardCap U) {v : Plane} (hv : v.2 ≤ 0) :
    support U v = support U (v.1, 0) := by
  apply le_antisymm
  · apply support_le_of_forall hU.nonempty
    intro p hp
    have hzero := coordDot_le_support hU.isCompact hp (v.1, 0)
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hU.inStrip hp).1 hv
    simp only [coordDot, mul_zero, add_zero] at hzero
    unfold coordDot
    linarith
  · obtain ⟨p, hp, hmax⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (v.1, 0)
    have h := coordDot_le_support hU.isCompact (hU.baseline_mem hp) v
    simp only [coordDot, mul_zero, zero_mul, add_zero] at hmax h
    rwa [hmax] at h

theorem IsDownwardCap.eq_of_upward_support_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    (hsupport : ∀ v : Plane, 0 ≤ v.2 → support U v = support V v) : U = V := by
  apply eq_of_support_eq hU.isCompact hU.nonempty hU.convex
    hV.isCompact hV.nonempty hV.convex
  intro v
  by_cases hv : 0 ≤ v.2
  · exact hsupport v hv
  · rw [hU.support_eq_horizontal_of_snd_nonpos (le_of_not_ge hv),
      hV.support_eq_horizontal_of_snd_nonpos (le_of_not_ge hv)]
    exact hsupport (v.1, 0) le_rfl

theorem IsDownwardCap.eq_of_quarter_support_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    (hfirst : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      support U (unitNormal t) = support V (unitNormal t))
    (hsecond : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      support U (companionNormal t) = support V (companionNormal t)) : U = V := by
  apply hU.eq_of_upward_support_eq hV
  intro v hv
  obtain ⟨r, hr, t, ht, h | h⟩ := exists_upper_polar hv
  · rw [h, support_smul_direction hU.isCompact hU.nonempty _ hr,
      support_smul_direction hV.isCompact hV.nonempty _ hr, hfirst t ht]
  · rw [h, support_smul_direction hU.isCompact hU.nonempty _ hr,
      support_smul_direction hV.isCompact hV.nonempty _ hr, hsecond t ht]

end AmbidextrousSofa
