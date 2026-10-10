module

public import AmbidextrousSofa.Analysis.WideDiagonalGeometry
public import AmbidextrousSofa.Analysis.RampCutIntegral

@[expose] public section

/-!
# The two actual near-vertical cuts of a wide tilted cap

The left cut is measured from the true tilted ceiling/diagonal
intersection. Only the inner half of each cut triangle is used, so no
outer-endpoint clipping assumption is required. Both deficits are literal
support values of the original cap.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def wideLeftSupportDeficit (U : Set Plane) (a h k v : ℝ) : ℝ :=
  1 - h / 2 + (k - h / a) * wideLeftIntersection a h v - support U (-k, 1)

def wideLeftTiltPenalty (a h k v : ℝ) : ℝ :=
  (1 - k) * h * (1 / 2 + wideLeftIntersection a h v / a)

theorem wideLeftIntersection_eqn {a h : ℝ} (ha : 0 < a) (hha : h < a) (v : ℝ) :
    wideLeftIntersection a h v * (1 - h / a) = v + h / 2 := by
  exact div_mul_cancel₀ _ (sub_pos.mpr ((div_lt_one ha).mpr hha)).ne'

theorem IsDownwardCap.wideLeftSupportDeficit_mem {U : Set Plane}
    (hU : IsDownwardCap U) {a h k v : ℝ} (ha : 0 < a) (hha : h < a)
    (hk : k ≤ 1) (hzk : h / a ≤ k)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 + v) :
    wideLeftSupportDeficit U a h k v ∈
      Icc 0 ((k - h / a) * (wideLeftIntersection a h v - a / 2)) := by
  let q := wideLeftIntersection a h v
  have hq : q * (1 - h / a) = v + h / 2 := wideLeftIntersection_eqn ha hha v
  have hza : (h / a) * a = h := div_mul_cancel₀ h ha.ne'
  have hupper : support U (-k, 1) ≤ 1 - h / 2 + (k - h / a) * q := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    simp only [coordDot, mul_neg, mul_one]
    by_cases hx : p.1 ≤ -q
    · have hd := hU.diagonalLeft_ge hp
      rw [hv] at hd
      have hprod := mul_nonneg (sub_nonneg.mpr hk)
        (show 0 ≤ -q - p.1 by linarith only [hx])
      nlinarith only [hd, hprod, hq]
    · have hceil := (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)).trans
        (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine p.1 ⟨p, hp, rfl⟩)
      have hprod := mul_nonneg (sub_nonneg.mpr hzk)
        (show 0 ≤ p.1 + q by linarith only [le_of_not_ge hx])
      unfold tiltedAffineCeiling at hceil
      nlinarith only [hceil, hprod]
  have hx : -a / 2 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith only [ha]
  have hlow := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-k, 1)
  rw [hleft] at hlow
  simp only [coordDot, mul_neg, mul_one] at hlow
  change 0 ≤ 1 - h / 2 + (k - h / a) * q - support U (-k, 1) ∧ _
  constructor
  · linarith only [hupper]
  · change 1 - h / 2 + (k - h / a) * q - support U (-k, 1) ≤
      (k - h / a) * (q - a / 2)
    nlinarith only [hlow, hza]

theorem wideLeftTiltPenalty_identity {a h : ℝ} (ha : 0 < a) (hha : h < a)
    (k v : ℝ) :
    1 + k * v - (1 - h / 2 + (k - h / a) * wideLeftIntersection a h v) =
      wideLeftTiltPenalty a h k v := by
  have hd : 1 - h / a ≠ 0 := (sub_pos.mpr ((div_lt_one ha).mpr hha)).ne'
  have hah : a - h ≠ 0 := (sub_pos.mpr hha).ne'
  unfold wideLeftTiltPenalty wideLeftIntersection
  field_simp [ha.ne', hd, hah] <;> ring

theorem wideLeftTiltPenalty_bounds {a h k v : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hk : k ≤ 1) (hq : wideLeftIntersection a h v ∈ Icc (a / 2) a) :
    0 ≤ wideLeftTiltPenalty a h k v ∧ wideLeftTiltPenalty a h k v ≤ 3 * (1 - k) * h / 2 := by
  have hcoef := mul_nonneg (sub_nonneg.mpr hk) hh
  have hq0 : 0 ≤ wideLeftIntersection a h v / a := div_nonneg (by linarith only [hq.1, ha]) ha.le
  have hq1 : wideLeftIntersection a h v / a ≤ 1 := (div_le_one ha).mpr hq.2
  unfold wideLeftTiltPenalty
  constructor
  · exact mul_nonneg hcoef (by linarith only [hq0])
  · nlinarith only [mul_nonneg hcoef (sub_nonneg.mpr hq1)]

theorem IsDownwardCap.wideRoofDeficit_ge_support_cuts {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hha : h < a) (hk : 0 < k) (hk1 : k ≤ 1) (hzk : h / a < k)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 + v)
    (huv : u ∈ Icc (a / 2) a) (hvv : v ∈ Icc (a / 2 - h) (a - 3 * h / 2)) :
    (nearDiagonalRightDeficit U k u ^ 2 + wideLeftSupportDeficit U a h k v ^ 2) / (2 * k) ≤
      wideRoofDeficit U a h u v := by
  let q := wideLeftIntersection a h v
  let δR := nearDiagonalRightDeficit U k u
  let δL := wideLeftSupportDeficit U a h k v
  have hq : q ∈ Icc (a / 2) a := wideLeftIntersection_mem ha hha hvv.1 hvv.2
  have hqd : q * (1 - h / a) = v + h / 2 := wideLeftIntersection_eqn ha hha v
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hk1 hl hr hright hu
  have hδL := hU.wideLeftSupportDeficit_mem ha hha hk1 hzk.le hl hr hleft hright haffine hv
  have hz : 0 ≤ h / a := div_nonneg hh ha.le
  have hkp : 0 < k - h / a := sub_pos.mpr hzk
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  let fR : ℝ → ℝ := fun x => min 1 (1 + u - x) - capRoof U x
  let fL : ℝ → ℝ := fun x => min (tiltedAffineCeiling a h x) (1 + v + x) - capRoof U x
  have hfR : ∀ l r, IntervalIntegrable fR volume l r := fun l r =>
    ((show Continuous (fun x : ℝ => min 1 (1 + u - x)) by fun_prop).intervalIntegrable l r).sub
      (hU.intervalIntegrable_capRoof l r)
  have hfL : ∀ l r, IntervalIntegrable fL volume l r := fun l r =>
    (((continuous_tiltedAffineCeiling a h).min (by fun_prop)).intervalIntegrable l r).sub
      (hU.intervalIntegrable_capRoof l r)
  have hfR0 : ∀ x ∈ Icc (a / 2) a, 0 ≤ fR x := by
    intro x hx
    have hxU : x ∈ horizontalProjection U := by rw [hproj]; exact ⟨by linarith only [hx.1, ha], hx.2⟩
    apply sub_nonneg.mpr
    exact le_min (capRoof_le_one hU.isCompact hU.inStrip x)
      (by linarith only [hU.capRoof_le_diagonalRight hxU, hu])
  have hfL0 : ∀ x ∈ Icc (-a) (-a / 2), 0 ≤ fL x := by
    intro x hx
    have hxU : x ∈ horizontalProjection U := by rw [hproj]; exact ⟨hx.1, by linarith only [hx.2, ha]⟩
    apply sub_nonneg.mpr
    exact le_min (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine x hxU)
      (by linarith only [hU.capRoof_le_diagonalLeft hxU, hv])
  have hR : δR ^ 2 / (2 * k) ≤ ∫ x in (a / 2)..a, fR x := by
    apply integral_gap_ge_left_ramp hfR hk hδR.1 huv hδR.2 hfR0
    intro x hx
    have hfit : δR / k ≤ u - a / 2 := (div_le_iff₀' hk).mpr hδR.2
    have hxU : x ∈ horizontalProjection U := by
      rw [hproj]
      exact ⟨by linarith only [hx.1, hfit, ha], hx.2.trans huv.2⟩
    have hcut := hU.capRoof_le_nearDiagonalRight k u hxU
    dsimp [fR]
    rw [min_eq_left (by linarith only [hx.2] : 1 ≤ 1 + u - x)]
    change _ ≤ 1 - capRoof U x
    change capRoof U x ≤ 1 + k * u - δR - k * x at hcut
    nlinarith only [hcut]
  have hL : δL ^ 2 / (2 * (k - h / a)) ≤ ∫ x in (-a)..(-a / 2), fL x := by
    apply integral_gap_ge_right_ramp hfL hkp hδL.1
      (show -q ∈ Icc (-a) (-a / 2) by constructor <;> linarith only [hq.1, hq.2])
      (show δL ≤ (k - h / a) * (-a / 2 - -q) by
        convert hδL.2 using 1 <;> dsimp [q] <;> ring) hfL0
    intro x hx
    have hfit : δL / (k - h / a) ≤ q - a / 2 := (div_le_iff₀' hkp).mpr hδL.2
    have hxU : x ∈ horizontalProjection U := by
      rw [hproj]
      exact ⟨by linarith only [hx.1, hq.2], by linarith only [hx.2, hfit, ha]⟩
    have hcut := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hxU) (-k, 1)
    simp only [coordDot, mul_neg, mul_one] at hcut
    have hceil : tiltedAffineCeiling a h x ≤ 1 + v + x := by
      have hprod := mul_nonneg (sub_pos.mpr ((div_lt_one ha).mpr hha)).le
        (show 0 ≤ x + q by linarith only [hx.1])
      unfold tiltedAffineCeiling
      nlinarith only [hprod, hqd]
    dsimp [fL]
    rw [min_eq_left hceil]
    dsimp [δL, wideLeftSupportDeficit, tiltedAffineCeiling, q]
    change _ ≤ 1 - h / 2 + (h / a) * x - capRoof U x
    nlinarith only [hcut]
  have hweaker : δL ^ 2 / (2 * k) ≤ δL ^ 2 / (2 * (k - h / a)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * k) (by positivity : 0 < 2 * (k - h / a))).mpr
    nlinarith only [mul_nonneg hz (sq_nonneg δL)]
  change (δR ^ 2 + δL ^ 2) / (2 * k) ≤ (∫ x in (-a)..(-a / 2), fL x) +
    ∫ x in (a / 2)..a, fR x
  rw [add_div]
  linarith only [hR, hL, hweaker]

end AmbidextrousSofa
