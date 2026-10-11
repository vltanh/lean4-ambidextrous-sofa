module

public import AmbidextrousSofa.Analysis.DiagonalDeficit

@[expose] public section

/-!
# Actual near-diagonal supports of a tilted cap

Unnormalized normals keep the geometry elementary. The deficits at
`(k,1)` and `(-k,1)` are literal support deficits. Actual attaining
diagonal points also give the two companion support lower bounds.
The lower wing is treated at its actual height throughout.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def nearDiagonalRightDeficit (U : Set Plane) (k u : ℝ) : ℝ :=
  1 + k * u - support U (k, 1)

def nearDiagonalLeftDeficit (U : Set Plane) (h k v : ℝ) : ℝ :=
  1 - h + k * v - support U (-k, 1)

theorem IsDownwardCap.capRoof_le_nearDiagonalRight {U : Set Plane}
    (hU : IsDownwardCap U) (k u : ℝ) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 + k * u - nearDiagonalRightDeficit U k u - k * x := by
  have h := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (k, 1)
  simp only [coordDot, mul_one] at h
  unfold nearDiagonalRightDeficit
  linarith

theorem IsDownwardCap.capRoof_le_nearDiagonalLeft {U : Set Plane}
    (hU : IsDownwardCap U) (h k v : ℝ) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 - h + k * v - nearDiagonalLeftDeficit U h k v + k * x := by
  have hbound := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-k, 1)
  simp only [coordDot, mul_neg, mul_one] at hbound
  unfold nearDiagonalLeftDeficit
  linarith

theorem IsDownwardCap.nearDiagonalRightDeficit_mem {U : Set Plane}
    (hU : IsDownwardCap U) {a k u : ℝ} (ha : 0 < a) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hright : capRoof U (a / 2) = 1) (hu : diagonalRight U = 1 + u) :
    nearDiagonalRightDeficit U k u ∈ Icc 0 (k * (u - a / 2)) := by
  have hupper : support U (k, 1) ≤ 1 + k * u := support_le_of_forall hU.nonempty fun p hp => by
    simp only [coordDot, mul_one]
    linarith [mul_le_mul_of_nonneg_left ((hU.diagonalRight_ge hp).trans_eq hu) hk0,
      mul_le_mul_of_nonneg_left (hU.inStrip hp).2 (sub_nonneg.mpr hk1)]
  have hproj := hU.horizontalProjection_eq_of hl hr
  have hlower := hU.capRoof_le_nearDiagonalRight k u
    (hproj ▸ ⟨by linarith, by linarith⟩ : a / 2 ∈ horizontalProjection U)
  rw [hright] at hlower
  exact ⟨by unfold nearDiagonalRightDeficit; linarith, by linarith⟩

theorem tilted_middle_slope {f : ℝ → ℝ} {a h m c : ℝ} (ha : 0 < a)
    (haffine : ∀ x ∈ Icc (-a / 2) (a / 2), f x = m * x + c)
    (hleft : f (-a / 2) = 1 - h) (hright : f (a / 2) = 1) :
    m * a = h ∧ m * (-a / 2) + c = 1 - h := by
  have hL := haffine (-a / 2) ⟨le_rfl, by linarith⟩
  have hR := haffine (a / 2) ⟨by linarith, le_rfl⟩
  constructor <;> linarith

theorem IsDownwardCap.nearDiagonalLeftDeficit_mem {U : Set Plane}
    (hU : IsDownwardCap U) {a h k v : ℝ} (ha : 0 < a)
    (hh : 0 ≤ h) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hhk : h ≤ k * a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 - h + v) (hv0 : a / 2 ≤ v) :
    nearDiagonalLeftDeficit U h k v ∈ Icc 0 (k * (v - a / 2)) := by
  obtain ⟨m, c, hm⟩ := haffine
  obtain ⟨hma, hmc⟩ := tilted_middle_slope ha hm hleft hright
  have hmk : m ≤ k := le_of_mul_le_mul_right (hma.trans_le hhk) ha
  have hproj := hU.horizontalProjection_eq_of hl hr
  have hupper : support U (-k, 1) ≤ 1 - h + k * v := support_le_of_forall hU.nonempty fun p hp => by
    have hx : p.1 ∈ Icc (-a) a := hproj ▸ ⟨p, hp, rfl⟩
    have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U from hp)
    have hkv := mul_nonneg hk0 (sub_nonneg.mpr hv0)
    simp only [coordDot, mul_neg, mul_one]
    rcases le_or_gt p.1 (-a / 2) with hpx | hpx
    · linarith [mul_le_mul_of_nonneg_left ((hU.diagonalLeft_ge hp).trans_eq hv) hk0,
        mul_le_mul_of_nonneg_left (hy.trans (hU.left_roof_le_middle_height ha hh hl hr hleft
          hright p.1 ⟨hx.1, hpx⟩)) (sub_nonneg.mpr hk1)]
    rcases le_or_gt p.1 (a / 2) with hpx1 | hpx1
    · rw [hm p.1 ⟨hpx.le, hpx1⟩] at hy
      linarith [mul_nonneg (sub_nonneg.mpr hmk) (show 0 ≤ p.1 + a / 2 by linarith)]
    · linarith [(hU.inStrip hp).2, mul_nonneg hk0 (sub_nonneg.mpr hpx1.le)]
  have hlower := hU.capRoof_le_nearDiagonalLeft h k v
    (hproj ▸ ⟨by linarith, by linarith⟩ : -a / 2 ∈ horizontalProjection U)
  rw [hleft] at hlower
  exact ⟨by unfold nearDiagonalLeftDeficit; linarith, by linarith⟩

theorem IsDownwardCap.diagonalRight_companion_support_ge {U : Set Plane}
    (hU : IsDownwardCap U) {k u : ℝ} (hk1 : k ≤ 1)
    (hu : diagonalRight U = 1 + u) : u + k ≤ support U (1, k) := by
  obtain ⟨p, hp, hpd⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (1, 1)
  have hs := coordDot_le_support hU.isCompact hp (1, k)
  simp only [coordDot, mul_one] at hpd hs
  have hpd : p.1 + p.2 = 1 + u := hpd.trans hu
  linarith [congrArg (k * ·) hpd,
    mul_nonneg (sub_nonneg.mpr hk1) (show 0 ≤ p.1 - u by linarith [(hU.inStrip hp).2])]

/-- The companion support bound is attained either at a maximizing diagonal
point on the actual lower wing, or, when the maximizer lies elsewhere, at
the lower middle endpoint, which then attains the same diagonal support. -/
theorem IsDownwardCap.diagonalLeft_companion_support_ge {U : Set Plane}
    (hU : IsDownwardCap U) {a h k v : ℝ} (ha : 0 < a)
    (hh : 0 ≤ h) (hha : h ≤ a) (hk1 : k ≤ 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 - h + v) :
    v + k * (1 - h) ≤ support U (-1, k) := by
  obtain ⟨m, c, hm⟩ := haffine
  obtain ⟨hma, hmc⟩ := tilted_middle_slope ha hm hleft hright
  have hproj := hU.horizontalProjection_eq_of hl hr
  obtain ⟨p, hp, hpd⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (-1, 1)
  have hs := coordDot_le_support hU.isCompact hp (-1, k)
  simp only [coordDot, mul_neg_one, mul_one] at hpd hs
  have hpd : -p.1 + p.2 = 1 - h + v := hpd.trans hv
  have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U from hp)
  rcases le_or_gt p.1 (-a / 2) with hpx | hpx
  · have hx : p.1 ∈ Icc (-a) a := hproj ▸ ⟨p, hp, rfl⟩
    have := hU.left_roof_le_middle_height ha hh hl hr hleft hright p.1 ⟨hx.1, hpx⟩
    linarith [congrArg (k * ·) hpd,
      mul_nonneg (sub_nonneg.mpr hk1) (show 0 ≤ -p.1 - v by linarith)]
  have hq := coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (hproj ▸ ⟨by linarith, by linarith⟩ :
      -a / 2 ∈ horizontalProjection U)) (-1, k)
  simp only [coordDot, hleft, mul_neg_one] at hq
  rcases le_or_gt p.1 (a / 2) with hpx1 | hpx1
  · rw [hm p.1 ⟨hpx.le, hpx1⟩] at hy
    linarith [mul_nonneg (sub_nonneg.mpr (le_of_mul_le_mul_right (by linarith : m * a ≤ 1 * a) ha))
      (show 0 ≤ p.1 + a / 2 by linarith)]
  · linarith [(hU.inStrip hp).2]

end AmbidextrousSofa
