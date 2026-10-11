module

public import AmbidextrousSofa.Analysis.DiagonalTent
public import AmbidextrousSofa.Analysis.LowHeightAlgebra
public import AmbidextrousSofa.Analysis.Chord
public import AmbidextrousSofa.Analysis.FiniteScore
public import AmbidextrousSofa.Measure.GraphIntegral

@[expose] public section

/-!
# Actual roofs below the low-middle-height ceiling

The projection is centered as [-2C,2C]. An affine middle roof joining a
value at most one half to height one lies below the displayed affine
ceiling through the first three quarters. Concavity extends that bound
to the charged left wing. The diagonal support excesses are then bounded
using actual points and the actual support maximum.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def lowCeiling (C x : ℝ) : ℝ := 3 / 4 + x / (4 * C)

theorem continuous_lowCeiling (C : ℝ) : Continuous (lowCeiling C) :=
  continuous_const.add (continuous_id.div_const _)

theorem eqOn_roofChord_of_affine {f : ℝ → ℝ} {a b m c : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, f x = m * x + c) : EqOn f (roofChord f a b) (Icc a b) := fun x hx => by
  rw [roofChord, hf a ⟨le_rfl, hab.le⟩, hf b ⟨hab.le, le_rfl⟩, hf x hx]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem IsDownwardCap.capRoof_le_lowCeiling_of_affine_middle
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hlow : capRoof U (-C) ≤ 1 / 2) (hhigh : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c) :
    ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x := by
  obtain ⟨m, c, haffine⟩ := haffine
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  intro x hx
  -- The roof lies below its chord through `-C` and `C`: by concavity left of `-C`,
  -- and with equality on the affine middle.
  have hchord : capRoof U x ≤ roofChord (capRoof U) (-C) C x := by
    rcases le_or_gt x (-C) with hxc | hxc
    · exact ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof
        (hproj ▸ ⟨hx.1, by linarith [hx.2]⟩) (hproj ▸ ⟨by linarith, by linarith⟩) (by linarith) hxc
    · exact (eqOn_roofChord_of_affine (by linarith) haffine ⟨hxc.le, hx.2⟩).le
  have ht : (x + C) / (2 * C) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [hx.2])
  calc capRoof U x ≤ capRoof U (-C) + (1 - capRoof U (-C)) * ((x + C) / (2 * C)) :=
        hchord.trans_eq (by rw [roofChord, hhigh]; ring)
    _ ≤ 1 / 2 + (x + C) / (2 * C) / 2 := by
        linarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr ht)]
    _ = lowCeiling C x := by rw [lowCeiling]; field_simp; ring

theorem integral_lowCeiling_left {C : ℝ} (hC : 0 < C) :
    (∫ x in (-2 * C)..(-C), lowCeiling C x) = 3 * C / 8 := by
  simp [lowCeiling, intervalIntegral.integral_add, intervalIntegral.integral_div, integral_id]
  field_simp
  ring

theorem lowCeiling_eq_quarter_add {C : ℝ} (hC : C ≠ 0) (x : ℝ) :
    lowCeiling C x = 1 / 4 + (x + 2 * C) / (4 * C) := by
  rw [lowCeiling]; field_simp; ring

/-- The excesses are defined from the true diagonal supports, rather than
introduced as independent relaxed support parameters. -/
theorem IsDownwardCap.lowHeight_diagonal_excess_bounds
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 1 / 2 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hhigh : capRoof U C = 1)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    0 ≤ diagonalRight U - 2 * C ∧ 1 - C ≤ diagonalRight U - 2 * C ∧
      diagonalRight U - 2 * C ≤ 1 ∧
      0 ≤ diagonalLeft U - 2 * C ∧ diagonalLeft U - 2 * C ≤ 1 / 4 := by
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  have hr := hU.diagonalRight_ge hU.right_baseline_mem
  have hl := hU.diagonalLeft_ge hU.left_baseline_mem
  have hhighSupport := hU.diagonalRight_ge (p := (C, 1))
    (hhigh ▸ capRoof_mem hU.isCompact (hproj ▸ ⟨by linarith, by linarith⟩))
  have hrUpper := hU.diagonalRight_le
  have hlUpper : diagonalLeft U ≤ 2 * C + 1 / 4 := support_le_of_forall hU.nonempty fun p hp => by
    have hx : p.1 ∈ Icc (-2 * C) (2 * C) := hproj ▸ ⟨p, hp, rfl⟩
    have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U from hp)
    simp only [coordDot, mul_neg_one, mul_one]
    rcases le_or_gt p.1 C with hxc | hxc
    · have hroof := hceiling p.1 ⟨hx.1, hxc⟩
      rw [lowCeiling_eq_quarter_add (by linarith)] at hroof
      linarith [div_le_self (by linarith [hx.1] : 0 ≤ p.1 + 2 * C) (by linarith : (1 : ℝ) ≤ 4 * C)]
    · linarith [(hU.inStrip hp).2]
  rw [hright] at hr hrUpper
  rw [hleft] at hl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The unrefined two-wing reward bound used at small and large widths. -/
theorem IsDownwardCap.lowHeight_reward_le
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    (∫ x in (-2 * C)..(-C), capRoof U x) +
      (∫ x in C..(2 * C), capRoof U x) ≤ 11 * C / 8 := by
  have hleft := intervalIntegral.integral_mono_on (by linarith : -2 * C ≤ -C)
    (hU.intervalIntegrable_capRoof _ _) ((continuous_lowCeiling C).intervalIntegrable _ _)
    fun x hx => hceiling x ⟨hx.1, by linarith [hx.2]⟩
  have hright := intervalIntegral.integral_mono_on (by linarith : C ≤ 2 * C)
    (hU.intervalIntegrable_capRoof C (2 * C)) (continuous_const.intervalIntegrable _ _)
    fun x _ => capRoof_le_one hU.isCompact hU.inStrip x
  rw [integral_lowCeiling_left hC] at hleft
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hright
  linarith

end AmbidextrousSofa
