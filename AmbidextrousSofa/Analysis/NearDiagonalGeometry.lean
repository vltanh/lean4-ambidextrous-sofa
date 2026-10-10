import AmbidextrousSofa.Analysis.DiagonalDeficit

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

theorem IsDownwardCap.nearDiagonalRightDeficit_mem {U : Set Plane}
    (hU : IsDownwardCap U) {a k u : ℝ} (ha : 0 < a) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hright : capRoof U (a / 2) = 1) (hu : diagonalRight U = 1 + u) :
    nearDiagonalRightDeficit U k u ∈ Icc 0 (k * (u - a / 2)) := by
  have hupper : support U (k, 1) ≤ 1 + k * u := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hd := hU.diagonalRight_ge hp
    rw [hu] at hd
    have hy := (hU.inStrip hp).2
    have h1 := mul_le_mul_of_nonneg_left hd hk0
    have h2 := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hk1)
    simp only [coordDot, mul_one]
    nlinarith only [h1, h2]
  have hx : a / 2 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith
  have hlower := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (k, 1)
  rw [hright] at hlower
  simp only [coordDot, mul_one] at hlower
  unfold nearDiagonalRightDeficit
  constructor <;> nlinarith

theorem tilted_middle_slope {f : ℝ → ℝ} {a h m c : ℝ} (ha : 0 < a)
    (haffine : ∀ x ∈ Icc (-a / 2) (a / 2), f x = m * x + c)
    (hleft : f (-a / 2) = 1 - h) (hright : f (a / 2) = 1) :
    m * a = h ∧ m * (-a / 2) + c = 1 - h := by
  have hL := haffine (-a / 2) ⟨le_rfl, by linarith⟩
  have hR := haffine (a / 2) ⟨by linarith, le_rfl⟩
  rw [hleft] at hL
  rw [hright] at hR
  constructor <;> nlinarith

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
  have hmk : m ≤ k := by nlinarith
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hupper : support U (-k, 1) ≤ 1 - h + k * v := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hx : p.1 ∈ Icc (-a) a := by rw [← hproj]; exact ⟨p, hp, rfl⟩
    have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)
    simp only [coordDot, mul_neg, mul_one]
    by_cases hpx : p.1 ≤ -a / 2
    · have hlow := hU.left_roof_le_middle_height ha hh hl hr hleft hright p.1 ⟨hx.1, hpx⟩
      have hd := hU.diagonalLeft_ge hp
      rw [hv] at hd
      have h1 := mul_le_mul_of_nonneg_left hd hk0
      have h2 := mul_le_mul_of_nonneg_left (hy.trans hlow) (sub_nonneg.mpr hk1)
      nlinarith only [h1, h2]
    · have hpx0 : -a / 2 ≤ p.1 := le_of_not_ge hpx
      have hkv := mul_nonneg hk0 (sub_nonneg.mpr hv0)
      by_cases hpx1 : p.1 ≤ a / 2
      · rw [hm p.1 ⟨hpx0, hpx1⟩] at hy
        have hprod := mul_nonneg (sub_nonneg.mpr hmk) (show 0 ≤ p.1 + a / 2 by linarith)
        nlinarith only [hy, hprod, hmc, hkv]
      · have hpx1' : a / 2 ≤ p.1 := le_of_not_ge hpx1
        have hprod := mul_nonneg hk0 (sub_nonneg.mpr hpx1')
        nlinarith [(hU.inStrip hp).2]
  have hx : -a / 2 ∈ horizontalProjection U := by
    rw [hproj]
    constructor <;> linarith
  have hlower := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-k, 1)
  rw [hleft] at hlower
  simp only [coordDot, mul_neg, mul_one] at hlower
  unfold nearDiagonalLeftDeficit
  constructor <;> nlinarith

theorem IsDownwardCap.capRoof_le_nearDiagonalRight {U : Set Plane}
    (hU : IsDownwardCap U) (k u : ℝ) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 + k * u - nearDiagonalRightDeficit U k u - k * x := by
  have h := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (k, 1)
  simp only [coordDot, mul_one] at h
  unfold nearDiagonalRightDeficit
  nlinarith

theorem IsDownwardCap.capRoof_le_nearDiagonalLeft {U : Set Plane}
    (hU : IsDownwardCap U) (h k v : ℝ) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 - h + k * v - nearDiagonalLeftDeficit U h k v + k * x := by
  have hbound := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-k, 1)
  simp only [coordDot, mul_neg, mul_one] at hbound
  unfold nearDiagonalLeftDeficit
  nlinarith

/-- A maximizing diagonal point can be chosen on the actual lower wing.
When an attainer lies elsewhere, the lower middle endpoint attains the
same diagonal support. -/
theorem IsDownwardCap.exists_diagonalLeft_attainer_on_left_wing {U : Set Plane}
    (hU : IsDownwardCap U) {a h v : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hha : h ≤ a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 - h + v) :
    ∃ p ∈ U, p.1 ≤ -a / 2 ∧ -p.1 + p.2 = 1 - h + v ∧ v ≤ -p.1 := by
  obtain ⟨m, c, hm⟩ := haffine
  obtain ⟨hma, hmc⟩ := tilted_middle_slope ha hm hleft hright
  have hm1 : m ≤ 1 := by nlinarith
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  obtain ⟨p, hp, hpd⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (-1, 1)
  simp only [coordDot, mul_neg_one, mul_one] at hpd
  change -p.1 + p.2 = diagonalLeft U at hpd
  rw [hv] at hpd
  by_cases hpx : p.1 ≤ -a / 2
  · have hx : p.1 ∈ Icc (-a) a := by rw [← hproj]; exact ⟨p, hp, rfl⟩
    have hroof := hU.left_roof_le_middle_height ha hh hl hr hleft hright p.1 ⟨hx.1, hpx⟩
    have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)
    exact ⟨p, hp, hpx, hpd, by linarith⟩
  · have hpx0 : -a / 2 ≤ p.1 := le_of_not_ge hpx
    have hdiag : -p.1 + p.2 ≤ a / 2 + 1 - h := by
      by_cases hpx1 : p.1 ≤ a / 2
      · have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)
        rw [hm p.1 ⟨hpx0, hpx1⟩] at hy
        have hprod := mul_nonneg (sub_nonneg.mpr hm1) (show 0 ≤ p.1 + a / 2 by linarith)
        nlinarith only [hy, hmc, hprod]
      · linarith [le_of_not_ge hpx1, (hU.inStrip hp).2]
    have hx : -a / 2 ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
    have hq : (-a / 2, 1 - h) ∈ U := by
      simpa only [hleft] using capRoof_mem hU.isCompact hx
    have hqdiag := hU.diagonalLeft_ge hq
    rw [hv] at hqdiag
    refine ⟨(-a / 2, 1 - h), hq, le_rfl, ?_, ?_⟩ <;> dsimp at * <;> linarith

theorem IsDownwardCap.diagonalRight_companion_support_ge {U : Set Plane}
    (hU : IsDownwardCap U) {k u : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hu : diagonalRight U = 1 + u) : u + k ≤ support U (1, k) := by
  obtain ⟨p, hp, hpd⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (1, 1)
  simp only [coordDot, mul_one] at hpd
  change p.1 + p.2 = diagonalRight U at hpd
  rw [hu] at hpd
  have hpx : u ≤ p.1 := by linarith [(hU.inStrip hp).2]
  have hprod := mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hpx)
  have hscaled := congrArg (fun z : ℝ => k * z) hpd
  have hs := coordDot_le_support hU.isCompact hp (1, k)
  simp only [coordDot, mul_one] at hs
  nlinarith

theorem IsDownwardCap.diagonalLeft_companion_support_ge {U : Set Plane}
    (hU : IsDownwardCap U) {a h k v : ℝ} (ha : 0 < a)
    (hh : 0 ≤ h) (hha : h ≤ a) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 - h + v) :
    v + k * (1 - h) ≤ support U (-1, k) := by
  obtain ⟨p, hp, _, hpd, hpx⟩ :=
    hU.exists_diagonalLeft_attainer_on_left_wing ha hh hha hl hr hleft hright haffine hv
  have hprod := mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hpx)
  have hscaled := congrArg (fun z : ℝ => k * z) hpd
  have hs := coordDot_le_support hU.isCompact hp (-1, k)
  simp only [coordDot, mul_neg_one] at hs
  nlinarith

end AmbidextrousSofa
