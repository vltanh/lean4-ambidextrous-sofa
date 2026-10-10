import AmbidextrousSofa.Measure.RealRadonNikodym
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# One bounded family of source coefficients

The four angular branch densities determine the two tangent
coefficients and a single common corner coefficient. The ratios are
clipped to the unit interval outside the almost-everywhere branch
identities, so their measurable representatives are bounded everywhere.
On the actual branch bounds, clipping does not change the ratios.

The first coefficient is one on a specified measurable charged set.
This convention retains saturation even where both first tangent mass
and tangent speed vanish. The companion and corner coefficients use a
zero value when their denominators are nonpositive.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def sourceFraction (mass slack : ℝ) : ℝ :=
  if 0 < slack then min (max (mass / slack) 0) 1 else 0

theorem sourceFraction_bounds (mass slack : ℝ) :
    0 ≤ sourceFraction mass slack ∧ sourceFraction mass slack ≤ 1 := by
  unfold sourceFraction
  split_ifs with hslack
  · exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_sourceFraction {mass slack : ℝ → ℝ}
    (hmass : Measurable mass) (hslack : Measurable slack) :
    Measurable (fun t => sourceFraction (mass t) (slack t)) := by
  unfold sourceFraction
  exact Measurable.ite (measurableSet_lt measurable_const hslack)
    (((hmass.div hslack).max measurable_const).min measurable_const) measurable_const

theorem sourceFraction_zero (slack : ℝ) : sourceFraction 0 slack = 0 := by
  simp only [sourceFraction, zero_div, max_self, min_eq_left zero_le_one, ite_self]

theorem sourceFraction_eq_zero_of_nonpositive {mass slack : ℝ} (hslack : slack ≤ 0) :
    sourceFraction mass slack = 0 := by
  rw [sourceFraction, if_neg (not_lt_of_ge hslack)]

theorem sourceFraction_eq_div {mass slack : ℝ}
    (hmass : 0 ≤ mass) (hslack : 0 < slack) (hle : mass ≤ slack) :
    sourceFraction mass slack = mass / slack := by
  have hquot : mass / slack ≤ 1 := (div_le_iff₀ hslack).mpr (by simpa using hle)
  rw [sourceFraction, if_pos hslack, max_eq_left (div_nonneg hmass hslack.le),
    min_eq_left hquot]

theorem sourceFraction_self {slack : ℝ} (hslack : 0 < slack) :
    sourceFraction slack slack = 1 := by
  rw [sourceFraction_eq_div hslack.le hslack le_rfl, div_self hslack.ne']

/-- The positive-part bound includes the zero and negative denominator
cases: the corresponding branch mass then vanishes. -/
theorem sourceFraction_reconstruct {mass slack : ℝ}
    (hmass : 0 ≤ mass) (hle : mass ≤ max slack 0) :
    mass = slack * sourceFraction mass slack := by
  by_cases hslack : 0 < slack
  · have hbound : mass ≤ slack := by
      simpa only [max_eq_left hslack.le] using hle
    rw [sourceFraction_eq_div hmass hslack hbound]
    calc
      mass = (mass / slack) * slack := (div_mul_cancel₀ mass hslack.ne').symm
      _ = slack * (mass / slack) := mul_comm _ _
  · have hnonpos : slack ≤ 0 := le_of_not_gt hslack
    have hzero : mass = 0 := le_antisymm
      (by simpa only [max_eq_right hnonpos] using hle) hmass
    rw [hzero, sourceFraction_zero, mul_zero]

def firstSourceCoefficient (charged : Set ℝ) (aB u : ℝ → ℝ) : ℝ → ℝ := by
  classical
  exact fun t => if t ∈ charged then 1 else sourceFraction (aB t) (1 - u t)

def companionSourceCoefficient (aD v : ℝ → ℝ) (t : ℝ) : ℝ :=
  sourceFraction (aD t) (1 - v t)

def cornerSourceCoefficient (aZ q : ℝ → ℝ) (t : ℝ) : ℝ :=
  sourceFraction (aZ t) (q t)

theorem measurable_firstSourceCoefficient {charged : Set ℝ} {aB u : ℝ → ℝ}
    (hcharged : MeasurableSet charged) (haB : Measurable aB) (hu : Measurable u) :
    Measurable (firstSourceCoefficient charged aB u) := by
  classical
  unfold firstSourceCoefficient
  exact Measurable.ite hcharged measurable_const
    (measurable_sourceFraction haB (measurable_const.sub hu))

theorem measurable_companionSourceCoefficient {aD v : ℝ → ℝ}
    (haD : Measurable aD) (hv : Measurable v) :
    Measurable (companionSourceCoefficient aD v) :=
  measurable_sourceFraction haD (measurable_const.sub hv)

theorem measurable_cornerSourceCoefficient {aZ q : ℝ → ℝ}
    (haZ : Measurable aZ) (hq : Measurable q) :
    Measurable (cornerSourceCoefficient aZ q) :=
  measurable_sourceFraction haZ hq

theorem firstSourceCoefficient_bounds (charged : Set ℝ) (aB u : ℝ → ℝ) (t : ℝ) :
    0 ≤ firstSourceCoefficient charged aB u t ∧
      firstSourceCoefficient charged aB u t ≤ 1 := by
  classical
  unfold firstSourceCoefficient
  split_ifs with ht
  · exact ⟨zero_le_one, le_rfl⟩
  · exact sourceFraction_bounds _ _

theorem companionSourceCoefficient_bounds (aD v : ℝ → ℝ) (t : ℝ) :
    0 ≤ companionSourceCoefficient aD v t ∧ companionSourceCoefficient aD v t ≤ 1 :=
  sourceFraction_bounds _ _

theorem cornerSourceCoefficient_bounds (aZ q : ℝ → ℝ) (t : ℝ) :
    0 ≤ cornerSourceCoefficient aZ q t ∧ cornerSourceCoefficient aZ q t ≤ 1 :=
  sourceFraction_bounds _ _

theorem firstSourceCoefficient_eq_one_of_mem {charged : Set ℝ} {aB u : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ charged) : firstSourceCoefficient charged aB u t = 1 := by
  classical
  simp only [firstSourceCoefficient, if_pos ht]

theorem firstSourceCoefficient_eq_zero_of_not_mem
    {charged : Set ℝ} {aB u : ℝ → ℝ} {t : ℝ}
    (ht : t ∉ charged) (hzero : aB t = 0) : firstSourceCoefficient charged aB u t = 0 := by
  classical
  simp only [firstSourceCoefficient, if_neg ht, hzero, sourceFraction_zero]

theorem companionSourceCoefficient_eq_zero_of_mass_zero {aD v : ℝ → ℝ} {t : ℝ}
    (hzero : aD t = 0) : companionSourceCoefficient aD v t = 0 := by
  simp only [companionSourceCoefficient, hzero, sourceFraction_zero]

theorem companionSourceCoefficient_eq_zero_of_one_le {aD v : ℝ → ℝ} {t : ℝ}
    (hv : 1 ≤ v t) : companionSourceCoefficient aD v t = 0 :=
  sourceFraction_eq_zero_of_nonpositive (sub_nonpos.mpr hv)

theorem cornerSourceCoefficient_eq_zero_of_mass_zero {aZ q : ℝ → ℝ} {t : ℝ}
    (hzero : aZ t = 0) : cornerSourceCoefficient aZ q t = 0 := by
  simp only [cornerSourceCoefficient, hzero, sourceFraction_zero]

theorem cornerSourceCoefficient_eq_one_of_mass_eq {aZ q : ℝ → ℝ} {t : ℝ}
    (hq : 0 < q t) (hmass : aZ t = q t) : cornerSourceCoefficient aZ q t = 1 := by
  rw [cornerSourceCoefficient, hmass, sourceFraction_self hq]

theorem firstSourceCoefficient_reconstruct {charged : Set ℝ} {aB u : ℝ → ℝ} {t : ℝ}
    (haB : 0 ≤ aB t) (hbound : aB t ≤ 1 - u t)
    (hcharged : t ∈ charged → aB t = 1 - u t) :
    aB t = (1 - u t) * firstSourceCoefficient charged aB u t := by
  classical
  by_cases ht : t ∈ charged
  · rw [firstSourceCoefficient_eq_one_of_mem ht, mul_one]
    exact hcharged ht
  · simp only [firstSourceCoefficient, if_neg ht]
    exact sourceFraction_reconstruct haB (hbound.trans (le_max_left _ _))

theorem companionSourceCoefficient_reconstruct {aD v : ℝ → ℝ} {t : ℝ}
    (haD : 0 ≤ aD t) (hbound : aD t ≤ max (1 - v t) 0) :
    aD t = (1 - v t) * companionSourceCoefficient aD v t :=
  sourceFraction_reconstruct haD hbound

/-- The sum of the two weighted corner branches bounds the first
branch by its own momentum. Both families use this same ratio. -/
theorem corner_first_mass_le_of_weighted_projection {p q aZ aW s c : ℝ}
    (hq : 0 < q) (hden : 0 < q * s - p * c)
    (hbalance : p * aZ + q * aW = 0)
    (hprojection : aZ * s + aW * c ≤ q * s - p * c) : aZ ≤ q := by
  have hcompanion : q * aW = -p * aZ := by nlinarith only [hbalance]
  have hidentity : q * (aZ * s + aW * c) = aZ * (q * s - p * c) := by
    calc
      _ = aZ * (q * s) + (q * aW) * c := by ring
      _ = aZ * (q * s) + (-p * aZ) * c := by rw [hcompanion]
      _ = _ := by ring
  have hbound := mul_le_mul_of_nonneg_left hprojection hq.le
  rw [hidentity] at hbound
  exact (mul_le_mul_iff_of_pos_right hden).mp hbound

theorem cornerSourceCoefficient_reconstruct
    {aZ aW p q : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (haZ : 0 ≤ aZ t)
    (hzero : ¬ (p t < 0 ∧ 0 < q t) → aZ t = 0 ∧ aW t = 0)
    (hbalance : p t * aZ t + q t * aW t = 0)
    (hprojection : p t < 0 → 0 < q t →
      aZ t * Real.sin t + aW t * Real.cos t ≤ q t * Real.sin t - p t * Real.cos t) :
    aZ t = q t * cornerSourceCoefficient aZ q t ∧
      aW t = -p t * cornerSourceCoefficient aZ q t := by
  by_cases hcore : p t < 0 ∧ 0 < q t
  · have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith only [ht.2, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hden : 0 < q t * Real.sin t - p t * Real.cos t := by
      have hpositive := mul_pos hcore.2 hs
      have hnegative := mul_neg_of_neg_of_pos hcore.1 hc
      linarith only [hpositive, hnegative]
    have hle := corner_first_mass_le_of_weighted_projection hcore.2 hden
      hbalance (hprojection hcore.1 hcore.2)
    have hratio : cornerSourceCoefficient aZ q t = aZ t / q t :=
      sourceFraction_eq_div haZ hcore.2 hle
    constructor
    · exact sourceFraction_reconstruct haZ (hle.trans (le_max_left _ _))
    · rw [hratio, ← mul_div_assoc]
      apply (eq_div_iff hcore.2.ne').mpr
      nlinarith only [hbalance]
  · obtain ⟨hZ, hW⟩ := hzero hcore
    have hχ := cornerSourceCoefficient_eq_zero_of_mass_zero (q := q) hZ
    simp only [hZ, hW, hχ, mul_zero, and_self]

/-- Pointwise reconstruction is arranged for direct almost-everywhere
assembly from the four actual Radon--Nikodym branch identities. -/
theorem commonSourceCoefficients_balance
    {charged : Set ℝ} {aB aZ aD aW p q u v : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (haB : 0 ≤ aB t) (haZ : 0 ≤ aZ t) (haD : 0 ≤ aD t)
    (hfirst : u t = aB t + aZ t) (hsecond : v t = aD t + aW t)
    (hBbound : aB t ≤ 1 - u t) (hDbound : aD t ≤ max (1 - v t) 0)
    (hcharged : t ∈ charged → aB t = 1 - u t)
    (hzero : ¬ (p t < 0 ∧ 0 < q t) → aZ t = 0 ∧ aW t = 0)
    (hbalance : p t * aZ t + q t * aW t = 0)
    (hprojection : p t < 0 → 0 < q t →
      aZ t * Real.sin t + aW t * Real.cos t ≤ q t * Real.sin t - p t * Real.cos t) :
    u t = (1 - u t) * firstSourceCoefficient charged aB u t +
        q t * cornerSourceCoefficient aZ q t ∧
      v t = (1 - v t) * companionSourceCoefficient aD v t -
        p t * cornerSourceCoefficient aZ q t := by
  have hB := firstSourceCoefficient_reconstruct haB hBbound hcharged
  have hD := companionSourceCoefficient_reconstruct haD hDbound
  obtain ⟨hZ, hW⟩ := cornerSourceCoefficient_reconstruct ht haZ hzero hbalance hprojection
  constructor
  · calc
      u t = aB t + aZ t := hfirst
      _ = _ := congrArg₂ (fun x y : ℝ => x + y) hB hZ
  · calc
      v t = aD t + aW t := hsecond
      _ = (1 - v t) * companionSourceCoefficient aD v t +
          (-p t) * cornerSourceCoefficient aZ q t :=
        congrArg₂ (fun x y : ℝ => x + y) hD hW
      _ = _ := by ring

end AmbidextrousSofa.Analysis
