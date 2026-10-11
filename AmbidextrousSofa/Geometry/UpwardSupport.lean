module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.Hallway

@[expose] public section

/-!
# Determination of a downward cap by its upward supports

The two quarter families cover the upper half-plane of directions. In a
downward direction every support maximum lies on the actual baseline, so
it is already determined by the horizontal supports. The polar coordinates
of a direction come from its complex argument.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem exists_quarter_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc (0 : ℝ) (Real.pi / 2), (a, b) = r • unitNormal t :=
  ⟨‖(⟨a, b⟩ : ℂ)‖, norm_nonneg _, Complex.arg ⟨a, b⟩,
    ⟨Complex.arg_nonneg_iff.2 hb, Complex.arg_le_pi_div_two_iff.2 (Or.inl ha)⟩,
    by simp [unitNormal, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]⟩

theorem exists_upper_polar {v : Plane} (hv : 0 ≤ v.2) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      v = r • unitNormal t ∨ v = r • companionNormal t := by
  rcases le_total 0 v.1 with hx | hx
  · obtain ⟨r, hr, t, ht, h⟩ := exists_quarter_polar hx hv
    exact ⟨r, hr, t, ht, Or.inl h⟩
  · obtain ⟨r, hr, t, ht, h⟩ := exists_quarter_polar hv (neg_nonneg.mpr hx)
    simp only [unitNormal, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h
    refine ⟨r, hr, t, ht, Or.inr (Prod.ext ?_ ?_)⟩ <;> simp [companionNormal] <;> linarith

theorem IsDownwardCap.support_eq_horizontal_of_snd_nonpos {U : Set Plane}
    (hU : IsDownwardCap U) {v : Plane} (hv : v.2 ≤ 0) :
    support U v = support U (v.1, 0) := by
  obtain ⟨p, hp, hmax⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (v.1, 0)
  refine support_eq_of_mem hU.isCompact (fun q hq => ?_) (hU.baseline_mem hp)
    (by simpa [coordDot] using hmax)
  have h := coordDot_le_support hU.isCompact hq (v.1, 0)
  simp only [coordDot] at h ⊢
  linarith [mul_nonpos_of_nonneg_of_nonpos (hU.inStrip hq).1 hv]

theorem IsDownwardCap.eq_of_quarter_support_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    (hfirst : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      support U (unitNormal t) = support V (unitNormal t))
    (hsecond : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      support U (companionNormal t) = support V (companionNormal t)) : U = V := by
  have hup (v : Plane) (hv : 0 ≤ v.2) : support U v = support V v := by
    obtain ⟨r, hr, t, ht, rfl | rfl⟩ := exists_upper_polar hv <;>
      simp only [support_smul_direction hU.isCompact hU.nonempty _ hr,
        support_smul_direction hV.isCompact hV.nonempty _ hr, hfirst t ht, hsecond t ht]
  refine eq_of_support_eq hU.isCompact hU.nonempty hU.convex hV.isCompact hV.nonempty hV.convex
    fun v => (le_total 0 v.2).elim (hup v) fun hv => ?_
  rw [hU.support_eq_horizontal_of_snd_nonpos hv, hV.support_eq_horizontal_of_snd_nonpos hv]
  exact hup _ le_rfl

end AmbidextrousSofa
