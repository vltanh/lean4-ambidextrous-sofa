import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

/-!
# Exact stopping bounds for a proper reflected excess

The first-zero and decay roots are compared jointly. Differences of
squares show that the decay gain under increasing width pays for the
opposite movement of the first zero. The analogous height comparison
uses only positive denominators and uniform rational root bounds.
Consequently the entire parameter boxes reduce to their displayed
endpoints, with a direct estimate for small initial heights.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

def properCrossingRoot (d e : ℝ) : ℝ := Real.sqrt (d ^ 2 - 2 * e)

def properEnergyRoot (d e δ : ℝ) : ℝ := Real.sqrt (d ^ 2 - e * (1 - e) + δ)

def properDecayRoot (d e δ : ℝ) : ℝ := Real.sqrt (4 * properEnergyRoot d e δ - 7)

def properFirstZeroTime (d e : ℝ) : ℝ := d - properCrossingRoot d e

def properDecayLength (d e δ : ℝ) : ℝ := properDecayRoot d e δ - 1

def properExcessEnd (d e δ : ℝ) : ℝ := properFirstZeroTime d e + properDecayLength d e δ

theorem properExcess_roots_bounds {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    (7 / 5 ≤ properCrossingRoot d e ∧ properCrossingRoot d e ≤ d ∧
      properCrossingRoot d e ^ 2 = d ^ 2 - 2 * e) ∧
    (19 / 10 ≤ properEnergyRoot d e δ ∧ properEnergyRoot d e δ ≤ 7 / 3 ∧
      properEnergyRoot d e δ ^ 2 = d ^ 2 - e * (1 - e) + δ) ∧
    (3 / 4 ≤ properDecayRoot d e δ ∧ properDecayRoot d e δ ≤ 8 / 5 ∧
      properDecayRoot d e δ ^ 2 = 4 * properEnergyRoot d e δ - 7) := by
  have hdsq0 : (199 / 100 : ℝ) ^ 2 ≤ d ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd0)
      (show 0 ≤ d + 199 / 100 by linarith only [hd0])]
  have hdsq1 : d ^ 2 ≤ (2311 / 1000 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd1)
      (show 0 ≤ 2311 / 1000 + d by linarith only [hd0])]
  have heprod0 := mul_nonneg he0 (sub_nonneg.mpr he1)
  have heprod1 : e * (1 - e) ≤ 1 / 4 := by nlinarith only [sq_nonneg (e - 1 / 2)]
  have hx2 : properCrossingRoot d e ^ 2 = d ^ 2 - 2 * e :=
    Real.sq_sqrt (by linarith only [hdsq0, he1])
  have hx0 : 0 ≤ properCrossingRoot d e := Real.sqrt_nonneg _
  have hxlo : 7 / 5 ≤ properCrossingRoot d e := by
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < 7 / 5 + properCrossingRoot d e by linarith only [hx0])
    nlinarith only [hp, hx2, hdsq0, he1]
  have hxhi : properCrossingRoot d e ≤ d := by
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < properCrossingRoot d e + d by linarith only [hx0, hd0])
    nlinarith only [hp, hx2, he0]
  have hy2 : properEnergyRoot d e δ ^ 2 = d ^ 2 - e * (1 - e) + δ :=
    Real.sq_sqrt (by linarith only [hdsq0, heprod1, hδ0])
  have hy0 : 0 ≤ properEnergyRoot d e δ := Real.sqrt_nonneg _
  have hylo : 19 / 10 ≤ properEnergyRoot d e δ := by
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < 19 / 10 + properEnergyRoot d e δ by linarith only [hy0])
    nlinarith only [hp, hy2, hdsq0, heprod1, hδ0]
  have hyhi : properEnergyRoot d e δ ≤ 7 / 3 := by
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < properEnergyRoot d e δ + 7 / 3 by linarith only [hy0])
    nlinarith only [hp, hy2, hdsq1, heprod0, hδ1]
  have hz2 : properDecayRoot d e δ ^ 2 = 4 * properEnergyRoot d e δ - 7 :=
    Real.sq_sqrt (by linarith only [hylo])
  have hz0 : 0 ≤ properDecayRoot d e δ := Real.sqrt_nonneg _
  have hzlo : 3 / 4 ≤ properDecayRoot d e δ := by
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < 3 / 4 + properDecayRoot d e δ by linarith only [hz0])
    nlinarith only [hp, hz2, hylo]
  have hzhi : properDecayRoot d e δ ≤ 8 / 5 := by
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < properDecayRoot d e δ + 8 / 5 by linarith only [hz0])
    nlinarith only [hp, hz2, hyhi]
  exact ⟨⟨hxlo, hxhi, hx2⟩, ⟨hylo, hyhi, hy2⟩, ⟨hzlo, hzhi, hz2⟩⟩

theorem properExcessEnd_mono_width {d D e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hdD : d ≤ D) (hD1 : D ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ ≤ properExcessEnd D e δ := by
  obtain ⟨hx, hy, hz⟩ := properExcess_roots_bounds hd0 (hdD.trans hD1) he0 he1 hδ0 hδ1
  obtain ⟨hX, hY, hZ⟩ := properExcess_roots_bounds (hd0.trans hdD) hD1 he0 he1 hδ0 hδ1
  have hsum : 0 < properCrossingRoot D e + properCrossingRoot d e := by
    linarith only [hx.1, hX.1]
  have hpay : properCrossingRoot D e - properCrossingRoot d e ≤ 2 * (D - d) := by
    apply (mul_le_mul_right hsum).mp
    have hp := mul_nonneg (sub_nonneg.mpr hdD)
      (show 0 ≤ 2 * (properCrossingRoot D e + properCrossingRoot d e) - D - d by
        linarith only [hx.1, hX.1, hD1, hdD])
    nlinarith only [hp, hx.2.2, hX.2.2]
  have hdenpos : 0 < (properDecayRoot D e δ + properDecayRoot d e δ) *
      (properEnergyRoot D e δ + properEnergyRoot d e δ) := by
    apply mul_pos <;> linarith only [hz.1, hZ.1, hy.1, hY.1]
  have hden : (properDecayRoot D e δ + properDecayRoot d e δ) *
      (properEnergyRoot D e δ + properEnergyRoot d e δ) ≤ 4 * (D + d) := by
    have hmul := mul_le_mul
      (show properDecayRoot D e δ + properDecayRoot d e δ ≤ 16 / 5 by
        linarith only [hz.2.1, hZ.2.1])
      (show properEnergyRoot D e δ + properEnergyRoot d e δ ≤ 14 / 3 by
        linarith only [hy.2.1, hY.2.1])
      (show 0 ≤ properEnergyRoot D e δ + properEnergyRoot d e δ by
        linarith only [hy.1, hY.1]) (by norm_num : (0 : ℝ) ≤ 16 / 5)
    linarith only [hmul, hd0, hdD]
  have hid : (properDecayRoot D e δ - properDecayRoot d e δ) *
      ((properDecayRoot D e δ + properDecayRoot d e δ) *
        (properEnergyRoot D e δ + properEnergyRoot d e δ)) = 4 * (D - d) * (D + d) := by
    calc
      _ = (properDecayRoot D e δ ^ 2 - properDecayRoot d e δ ^ 2) *
          (properEnergyRoot D e δ + properEnergyRoot d e δ) := by ring
      _ = 4 * (properEnergyRoot D e δ ^ 2 - properEnergyRoot d e δ ^ 2) := by
        rw [hz.2.2, hZ.2.2]
        ring
      _ = 4 * (D - d) * (D + d) := by rw [hy.2.2, hY.2.2]; ring
  have hgain : D - d ≤ properDecayRoot D e δ - properDecayRoot d e δ := by
    apply (mul_le_mul_right hdenpos).mp
    rw [hid]
    convert mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hdD) using 1 <;> ring
  unfold properExcessEnd properFirstZeroTime properDecayLength
  linarith only [hpay, hgain]

theorem properExcessEnd_mono_height {d e E δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 3 / 10 ≤ e) (heE : e ≤ E) (hE1 : E ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ ≤ properExcessEnd d E δ := by
  obtain ⟨hx, hy, hz⟩ := properExcess_roots_bounds hd0 hd1
    (by linarith only [he0]) (heE.trans hE1) hδ0 hδ1
  obtain ⟨hX, hY, hZ⟩ := properExcess_roots_bounds hd0 hd1
    (by linarith only [he0, heE]) hE1 hδ0 hδ1
  have hsum : 0 < properCrossingRoot d e + properCrossingRoot d E := by
    linarith only [hx.1, hX.1]
  have hgain : (E - e) / 3 ≤ properCrossingRoot d e - properCrossingRoot d E := by
    apply (mul_le_mul_right hsum).mp
    have hp := mul_nonneg (sub_nonneg.mpr heE)
      (show 0 ≤ 6 - (properCrossingRoot d e + properCrossingRoot d E) by
        linarith only [hx.2.1, hX.2.1, hd1])
    nlinarith only [hp, hx.2.2, hX.2.2]
  have hdenpos : 0 < (properDecayRoot d E δ + properDecayRoot d e δ) *
      (properEnergyRoot d E δ + properEnergyRoot d e δ) := by
    apply mul_pos <;> linarith only [hz.1, hZ.1, hy.1, hY.1]
  have hden : 57 / 10 ≤ (properDecayRoot d E δ + properDecayRoot d e δ) *
      (properEnergyRoot d E δ + properEnergyRoot d e δ) := by
    have hmul := mul_le_mul
      (show (3 / 2 : ℝ) ≤ properDecayRoot d E δ + properDecayRoot d e δ by
        linarith only [hz.1, hZ.1])
      (show (19 / 5 : ℝ) ≤ properEnergyRoot d E δ + properEnergyRoot d e δ by
        linarith only [hy.1, hY.1]) (by norm_num : (0 : ℝ) ≤ 19 / 5)
      (show 0 ≤ properDecayRoot d E δ + properDecayRoot d e δ by
        linarith only [hz.1, hZ.1])
    norm_num at hmul ⊢
    exact hmul
  have hid : (properDecayRoot d E δ - properDecayRoot d e δ) *
      ((properDecayRoot d E δ + properDecayRoot d e δ) *
        (properEnergyRoot d E δ + properEnergyRoot d e δ)) = 4 * (E - e) * (E + e - 1) := by
    calc
      _ = (properDecayRoot d E δ ^ 2 - properDecayRoot d e δ ^ 2) *
          (properEnergyRoot d E δ + properEnergyRoot d e δ) := by ring
      _ = 4 * (properEnergyRoot d E δ ^ 2 - properEnergyRoot d e δ ^ 2) := by
        rw [hz.2.2, hZ.2.2]
        ring
      _ = 4 * (E - e) * (E + e - 1) := by rw [hy.2.2, hY.2.2]; ring
  have hloss : -(E - e) / 3 ≤ properDecayRoot d E δ - properDecayRoot d e δ := by
    apply (mul_le_mul_right hdenpos).mp
    rw [hid]
    have hp := mul_nonneg (sub_nonneg.mpr heE)
      (show 0 ≤ 4 * (E + e - 1) +
        ((properDecayRoot d E δ + properDecayRoot d e δ) *
          (properEnergyRoot d E δ + properEnergyRoot d e δ)) / 3 by
        linarith only [hden, he0, heE])
    nlinarith only [hp]
  unfold properExcessEnd properFirstZeroTime properDecayLength
  linarith only [hgain, hloss]

theorem properFirstZeroTime_quadratic {d e : ℝ}
    (hrad : 0 ≤ d ^ 2 - 2 * e) :
    e - d * properFirstZeroTime d e + properFirstZeroTime d e ^ 2 / 2 = 0 := by
  have hx : properCrossingRoot d e ^ 2 = d ^ 2 - 2 * e := Real.sq_sqrt hrad
  unfold properFirstZeroTime
  nlinarith only [hx]

theorem properFirstZeroTime_lt_of_quadratic {d e T : ℝ}
    (hrad : 0 ≤ d ^ 2 - 2 * e) (hTd : T ≤ d)
    (hnegative : e - d * T + T ^ 2 / 2 < 0) : properFirstZeroTime d e < T := by
  apply first_zero_lt_of_quadratic (show properFirstZeroTime d e ≤ d from
    sub_le_self _ (Real.sqrt_nonneg _)) hTd
    (properFirstZeroTime_quadratic hrad).le hnegative

theorem properDecayLength_lt_of_energy {d e δ ell : ℝ}
    (henergy : 0 ≤ d ^ 2 - e * (1 - e) + δ)
    (hdecay : 0 ≤ 4 * properEnergyRoot d e δ - 7)
    (hell : 0 ≤ ell)
    (hbound : d ^ 2 - e * (1 - e) + δ < (2 + ell / 2 + ell ^ 2 / 4) ^ 2) :
    properDecayLength d e δ < ell := by
  have hy2 : properEnergyRoot d e δ ^ 2 = d ^ 2 - e * (1 - e) + δ := Real.sq_sqrt henergy
  have hy0 : 0 ≤ properEnergyRoot d e δ := Real.sqrt_nonneg _
  have hy : properEnergyRoot d e δ < 2 + ell / 2 + ell ^ 2 / 4 := by
    by_contra hnot
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ properEnergyRoot d e δ + (2 + ell / 2 + ell ^ 2 / 4) by positivity)
    nlinarith only [hp, hy2, hbound]
  have hz2 : properDecayRoot d e δ ^ 2 = 4 * properEnergyRoot d e δ - 7 := Real.sq_sqrt hdecay
  have hz0 : 0 ≤ properDecayRoot d e δ := Real.sqrt_nonneg _
  unfold properDecayLength
  by_contra hnot
  have hp := mul_nonneg
    (show 0 ≤ properDecayRoot d e δ - (ell + 1) by linarith only [le_of_not_gt hnot])
    (show 0 ≤ properDecayRoot d e δ + (ell + 1) by linarith only [hz0, hell])
  nlinarith only [hp, hz2, hy]

theorem properDecayLength_lt_fifty_two_hundredths {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properDecayLength d e δ < 13 / 25 := by
  obtain ⟨_, hy, _⟩ := properExcess_roots_bounds hd0 hd1 he0 he1 hδ0 hδ1
  apply properDecayLength_lt_of_energy
    (by rw [← hy.2.2]; exact sq_nonneg _) (by linarith only [hy.1]) (by norm_num)
  have hdsq := mul_nonneg (sub_nonneg.mpr hd1)
    (show 0 ≤ 2311 / 1000 + d by linarith only [hd0])
  nlinarith only [hdsq, mul_nonneg he0 (sub_nonneg.mpr he1), hδ1]

theorem properDecayLength_lt_near_full {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 563 / 250)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 480) :
    properDecayLength d e δ < 43 / 100 := by
  obtain ⟨_, hy, _⟩ := properExcess_roots_bounds hd0 (by linarith only [hd1]) he0 he1
    hδ0 (by linarith only [hδ1])
  apply properDecayLength_lt_of_energy
    (by rw [← hy.2.2]; exact sq_nonneg _) (by linarith only [hy.1]) (by norm_num)
  have hdsq := mul_nonneg (sub_nonneg.mpr hd1)
    (show 0 ≤ 563 / 250 + d by linarith only [hd0])
  nlinarith only [hdsq, mul_nonneg he0 (sub_nonneg.mpr he1), hδ1]

theorem properExcessEnd_lt_of_small_height {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 3 / 10) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ < 69 / 100 := by
  obtain ⟨hx, _, _⟩ := properExcess_roots_bounds hd0 hd1 he0
    (by linarith only [he1]) hδ0 hδ1
  have ht := properFirstZeroTime_lt_of_quadratic
    (by rw [← hx.2.2]; exact sq_nonneg _) (show (17 / 100 : ℝ) ≤ d by linarith only [hd0])
    (show e - d * (17 / 100) + (17 / 100) ^ 2 / 2 < 0 by linarith only [hd0, he1])
  have hell := properDecayLength_lt_fifty_two_hundredths hd0 hd1 he0
    (by linarith only [he1]) hδ0 hδ1
  unfold properExcessEnd
  linarith only [ht, hell]

theorem properExcessEnd_lt_near_full {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 563 / 250)
    (he0 : 0 ≤ e) (he1 : e ≤ 19 / 25) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 480) :
    properExcessEnd d e δ < 73 / 100 := by
  by_cases hsmall : e ≤ 3 / 10
  · exact (properExcessEnd_lt_of_small_height hd0 (by linarith only [hd1]) he0 hsmall
      hδ0 (by linarith only [hδ1])).trans (by norm_num)
  · have hwidth := properExcessEnd_mono_width hd0 hd1
      (by norm_num : (563 / 250 : ℝ) ≤ 2311 / 1000) he0
      (by linarith only [he1]) hδ0 (by linarith only [hδ1])
    have hheight := properExcessEnd_mono_height
      (by norm_num : (199 / 100 : ℝ) ≤ 563 / 250) (by norm_num)
      (le_of_not_ge hsmall) he1 (by norm_num) hδ0 (by linarith only [hδ1])
    have ht : properFirstZeroTime (563 / 250) (19 / 25) < 37 / 100 :=
      properFirstZeroTime_lt_of_quadratic (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨_, hy, _⟩ := properExcess_roots_bounds
      (d := (563 / 250 : ℝ)) (e := (19 / 25 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ0 (by linarith only [hδ1])
    have hell : properDecayLength (563 / 250) (19 / 25) δ < 9 / 25 := by
      apply properDecayLength_lt_of_energy
        (by rw [← hy.2.2]; exact sq_nonneg _) (by linarith only [hy.1]) (by norm_num)
      nlinarith only [hδ1]
    unfold properExcessEnd at *
    linarith only [hwidth, hheight, ht, hell]

theorem properExcessEnd_lt_nonnegative_middle {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 179 / 200) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ < 91 / 100 := by
  by_cases hsmall : e ≤ 3 / 10
  · exact (properExcessEnd_lt_of_small_height hd0 hd1 he0 hsmall hδ0 hδ1).trans (by norm_num)
  · have hwidth := properExcessEnd_mono_width hd0 hd1 le_rfl he0
      (by linarith only [he1]) hδ0 hδ1
    have hheight := properExcessEnd_mono_height
      (by norm_num : (199 / 100 : ℝ) ≤ 2311 / 1000) le_rfl
      (le_of_not_ge hsmall) he1 (by norm_num) hδ0 hδ1
    have ht : properFirstZeroTime (2311 / 1000) (179 / 200) < 107 / 250 :=
      properFirstZeroTime_lt_of_quadratic (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨_, hy, _⟩ := properExcess_roots_bounds
      (d := (2311 / 1000 : ℝ)) (e := (179 / 200 : ℝ))
      (by norm_num) le_rfl (by norm_num) (by norm_num) hδ0 hδ1
    have hell : properDecayLength (2311 / 1000) (179 / 200) δ < 241 / 500 := by
      apply properDecayLength_lt_of_energy
        (by rw [← hy.2.2]; exact sq_nonneg _) (by linarith only [hy.1]) (by norm_num)
      nlinarith only [hδ1]
    unfold properExcessEnd at *
    linarith only [hwidth, hheight, ht, hell]

theorem properExcessEnd_lt_negative_middle {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ < 9 / 10 := by
  by_cases hsmall : e ≤ 3 / 10
  · exact (properExcessEnd_lt_of_small_height hd0 (by linarith only [hd1]) he0 hsmall
      hδ0 hδ1).trans (by norm_num)
  · have hwidth := properExcessEnd_mono_width hd0 hd1
      (by norm_num : (111 / 50 : ℝ) ≤ 2311 / 1000) he0 he1 hδ0 hδ1
    have hheight := properExcessEnd_mono_height
      (by norm_num : (199 / 100 : ℝ) ≤ 111 / 50) (by norm_num)
      (le_of_not_ge hsmall) he1 le_rfl hδ0 hδ1
    have ht : properFirstZeroTime (111 / 50) 1 < 51 / 100 :=
      properFirstZeroTime_lt_of_quadratic (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨_, hy, _⟩ := properExcess_roots_bounds (d := (111 / 50 : ℝ)) (e := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) le_rfl hδ0 hδ1
    have hell : properDecayLength (111 / 50) 1 δ < 39 / 100 := by
      apply properDecayLength_lt_of_energy
        (by rw [← hy.2.2]; exact sq_nonneg _) (by linarith only [hy.1]) (by norm_num)
      nlinarith only [hδ1]
    unfold properExcessEnd at *
    linarith only [hwidth, hheight, ht, hell]

end AmbidextrousSofa.Analysis
