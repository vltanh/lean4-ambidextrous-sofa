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
    wideLeftIntersection a h v * (1 - h / a) = v + h / 2 :=
  div_mul_cancel₀ _ (sub_pos.mpr ((div_lt_one ha).mpr hha)).ne'

theorem IsDownwardCap.wideLeftSupportDeficit_mem {U : Set Plane}
    (hU : IsDownwardCap U) {a h k v : ℝ} (ha : 0 < a) (hha : h < a)
    (hk : k ≤ 1) (hzk : h / a ≤ k)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 + v) :
    wideLeftSupportDeficit U a h k v ∈
      Icc 0 ((k - h / a) * (wideLeftIntersection a h v - a / 2)) := by
  have hq := wideLeftIntersection_eqn ha hha v
  set q := wideLeftIntersection a h v
  have hupper : support U (-k, 1) ≤ 1 - h / 2 + (k - h / a) * q := by
    refine support_le_of_forall hU.nonempty fun p hp => ?_
    simp only [coordDot]
    rcases le_or_gt p.1 (-q) with hx | hx
    · linarith [hU.diagonalLeft_ge hp, mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hx)]
    · have := (le_capRoof (x := p.1) hU.isCompact hp).trans
        (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine p.1 ⟨p, hp, rfl⟩)
      unfold tiltedAffineCeiling at this
      linarith only [this, mul_nonneg (sub_nonneg.mpr hzk) (neg_lt_iff_pos_add.mp hx).le]
  have hx : -a / 2 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith only [ha]
  have hlow := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-k, 1)
  simp only [coordDot, hleft] at hlow
  have hza : h / a * a = h := div_mul_cancel₀ h ha.ne'
  constructor <;> simp only [wideLeftSupportDeficit] <;> linarith only [hupper, hlow, hza]

theorem wideLeftTiltPenalty_identity {a h : ℝ} (ha : 0 < a) (hha : h < a)
    (k v : ℝ) :
    1 + k * v - (1 - h / 2 + (k - h / a) * wideLeftIntersection a h v) =
      wideLeftTiltPenalty a h k v := by
  unfold wideLeftTiltPenalty wideLeftIntersection
  field_simp [(sub_pos.mpr hha).ne']
  ring

theorem wideLeftTiltPenalty_bounds {a h k v : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hk : k ≤ 1) (hq : wideLeftIntersection a h v ∈ Icc (a / 2) a) :
    0 ≤ wideLeftTiltPenalty a h k v ∧ wideLeftTiltPenalty a h k v ≤ 3 * (1 - k) * h / 2 := by
  have hcoef := mul_nonneg (sub_nonneg.mpr hk) hh
  have hq0 := div_nonneg (hq.1.trans' (half_pos ha).le) ha.le
  unfold wideLeftTiltPenalty
  exact ⟨mul_nonneg hcoef (by linarith only [hq0]),
    by linarith only [mul_nonneg hcoef (sub_nonneg.mpr ((div_le_one ha).mpr hq.2))]⟩

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
  obtain ⟨hq1, hq2⟩ := wideLeftIntersection_mem ha hha hvv.1 hvv.2
  have hqd := wideLeftIntersection_eqn ha hha v
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hk1 hl hr hright hu
  obtain ⟨hδL0, hδL1⟩ :=
    hU.wideLeftSupportDeficit_mem ha hha hk1 hzk.le hl hr hleft hright haffine hv
  set q := wideLeftIntersection a h v
  set δR := nearDiagonalRightDeficit U k u
  set δL := wideLeftSupportDeficit U a h k v with hδLdef
  have hkp : 0 < k - h / a := sub_pos.mpr hzk
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hR : δR ^ 2 / (2 * k) ≤ ∫ x in (a / 2)..a, min 1 (1 + u - x) - capRoof U x := by
    refine integral_gap_ge_left_ramp (fun l r =>
      ((Continuous.intervalIntegrable (by fun_prop) l r).sub (hU.intervalIntegrable_capRoof l r)))
      hk hδR.1 huv hδR.2 (fun x hx => ?_) fun x hx => ?_
    · have hxU : x ∈ horizontalProjection U := hproj ▸ ⟨by linarith only [hx.1, ha], hx.2⟩
      exact sub_nonneg.mpr (le_min (capRoof_le_one hU.isCompact hU.inStrip x)
        (by linarith only [hU.capRoof_le_diagonalRight hxU, hu]))
    · have hxU : x ∈ horizontalProjection U :=
        hproj ▸ ⟨by linarith only [hx.1, (div_le_iff₀' hk).mpr hδR.2, ha], hx.2.trans huv.2⟩
      rw [min_eq_left (by linarith only [hx.2])]
      linarith only [hU.capRoof_le_nearDiagonalRight k u hxU]
  have hL : δL ^ 2 / (2 * (k - h / a)) ≤
      ∫ x in (-a)..(-a / 2), min (tiltedAffineCeiling a h x) (1 + v + x) - capRoof U x := by
    refine integral_gap_ge_right_ramp (fun l r =>
      (((continuous_tiltedAffineCeiling a h).min (by fun_prop)).intervalIntegrable l r).sub
      (hU.intervalIntegrable_capRoof l r)) hkp hδL0 (p := -q)
      ⟨by linarith only [hq2], by linarith only [hq1]⟩ (by linarith only [hδL1])
      (fun x hx => ?_) fun x ⟨hx1, hx2⟩ => ?_
    · have hxU : x ∈ horizontalProjection U := hproj ▸ ⟨hx.1, by linarith only [hx.2, ha]⟩
      exact sub_nonneg.mpr (le_min (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright
        haffine x hxU) (by linarith only [hU.capRoof_le_diagonalLeft hxU, hv]))
    · have hxU : x ∈ horizontalProjection U :=
        hproj ▸ ⟨by linarith only [hx1, hq2],
          by linarith only [hx2, (div_le_iff₀' hkp).mpr hδL1, ha]⟩
      have hcut := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hxU) (-k, 1)
      simp only [coordDot] at hcut
      rw [min_eq_left (by unfold tiltedAffineCeiling; linarith only [hqd, mul_nonneg (sub_pos.mpr
        ((div_lt_one ha).mpr hha)).le (neg_le_iff_add_nonneg.mp hx1)])]
      simp only [hδLdef, wideLeftSupportDeficit, tiltedAffineCeiling]
      linarith only [hcut]
  rw [wideRoofDeficit, add_div]
  linarith only [hR, hL, div_le_div_of_nonneg_left (sq_nonneg δL)
    (by positivity : 0 < 2 * (k - h / a)) (by linarith only [div_nonneg hh ha.le] : _ ≤ 2 * k)]

end AmbidextrousSofa
