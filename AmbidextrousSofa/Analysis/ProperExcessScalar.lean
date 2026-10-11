module

public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

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
  have hd2 := pow_le_pow_left₀ (by norm_num) hd0 2
  have hd2' := pow_le_pow_left₀ (by linarith) hd1 2
  have he2 := mul_nonneg he0 (sub_nonneg.2 he1)
  have he2' : e * (1 - e) ≤ 1 / 4 := by linarith [sq_nonneg (e - 1 / 2)]
  have hy : 19 / 10 ≤ properEnergyRoot d e δ ∧ properEnergyRoot d e δ ≤ 7 / 3 :=
    ⟨Real.le_sqrt_of_sq_le (by linarith), (Real.sqrt_le_left (by norm_num)).2 (by linarith)⟩
  exact ⟨⟨Real.le_sqrt_of_sq_le (by linarith), (Real.sqrt_le_left (by linarith)).2 (by linarith),
      Real.sq_sqrt (by linarith)⟩, ⟨hy.1, hy.2, Real.sq_sqrt (by linarith)⟩,
    ⟨Real.le_sqrt_of_sq_le (by linarith), (Real.sqrt_le_left (by norm_num)).2 (by linarith),
      Real.sq_sqrt (by linarith)⟩⟩

theorem properExcessEnd_mono_width {d D e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hdD : d ≤ D) (hD1 : D ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ ≤ properExcessEnd D e δ := by
  obtain ⟨⟨hx0, -, hx2⟩, ⟨hy0, hy1, hy2⟩, ⟨hz0, hz1, hz2⟩⟩ :=
    properExcess_roots_bounds hd0 (hdD.trans hD1) he0 he1 hδ0 hδ1
  obtain ⟨⟨hX0, -, hX2⟩, ⟨hY0, hY1, hY2⟩, ⟨hZ0, hZ1, hZ2⟩⟩ :=
    properExcess_roots_bounds (hd0.trans hdD) hD1 he0 he1 hδ0 hδ1
  unfold properExcessEnd properFirstZeroTime properDecayLength
  generalize properCrossingRoot d e = x, properCrossingRoot D e = X, properEnergyRoot d e δ = y,
    properEnergyRoot D e δ = Y, properDecayRoot d e δ = z, properDecayRoot D e δ = Z at *
  -- Differences of squares: the first zero moves by at most `2 (D - d)`, the decay root by more.
  have hX : (X - x) * (X + x) ≤ 2 * (D - d) * (X + x) := by
    linarith only [hx2, hX2, mul_nonneg (sub_nonneg.2 hdD)
      (by linarith only [hx0, hX0, hdD, hD1] : 0 ≤ 2 * (X + x) - D - d)]
  have hY : 17 / 20 * (D - d) * (Y + y) ≤ (Y - y) * (Y + y) := by
    linarith only [hy2, hY2, mul_nonneg (sub_nonneg.2 hdD)
      (by linarith only [hy1, hY1, hd0, hdD] : 0 ≤ D + d - 17 / 20 * (Y + y))]
  replace hY := le_of_mul_le_mul_right hY (by linarith only [hy0, hY0])
  have hZ : 5 / 4 * (Y - y) * (Z + z) ≤ (Z - z) * (Z + z) := by
    linarith only [hz2, hZ2, mul_nonneg (by linarith only [hY, hdD] : 0 ≤ Y - y)
      (by linarith only [hz1, hZ1] : 0 ≤ 4 - 5 / 4 * (Z + z))]
  linarith only [hY, hdD, le_of_mul_le_mul_right hX (by linarith only [hx0, hX0]),
    le_of_mul_le_mul_right hZ (by linarith only [hz0, hZ0])]

theorem properExcessEnd_mono_height {d e E δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 3 / 10 ≤ e) (heE : e ≤ E) (hE1 : E ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ ≤ properExcessEnd d E δ := by
  obtain ⟨⟨hx0, hx1, hx2⟩, ⟨hy0, hy1, hy2⟩, ⟨hz0, hz1, hz2⟩⟩ :=
    properExcess_roots_bounds hd0 hd1 (by linarith) (heE.trans hE1) hδ0 hδ1
  obtain ⟨⟨hX0, hX1, hX2⟩, ⟨hY0, hY1, hY2⟩, ⟨hZ0, hZ1, hZ2⟩⟩ :=
    properExcess_roots_bounds hd0 hd1 (by linarith) hE1 hδ0 hδ1
  unfold properExcessEnd properFirstZeroTime properDecayLength
  generalize properCrossingRoot d e = x, properCrossingRoot d E = X, properEnergyRoot d e δ = y,
    properEnergyRoot d E δ = Y, properDecayRoot d e δ = z, properDecayRoot d E δ = Z at *
  -- Differences of squares: the first zero gains at least `(E - e) / 3`, the decay root loses less.
  have hX : (E - e) / 3 * (x + X) ≤ (x - X) * (x + X) := by
    linarith only [hx2, hX2, mul_nonneg (sub_nonneg.2 heE)
      (by linarith only [hx1, hX1, hd1] : 0 ≤ 6 - (x + X))]
  have hY : -(E - e) / 9 * (Y + y) ≤ (Y - y) * (Y + y) := by
    linarith only [hy2, hY2, mul_nonneg (sub_nonneg.2 heE)
      (by linarith only [hy0, hY0, he0, heE] : 0 ≤ E + e - 1 + (Y + y) / 9)]
  replace hY := le_of_mul_le_mul_right hY (by linarith only [hy0, hY0])
  have hZ : -(E - e) / 3 * (Z + z) ≤ (Z - z) * (Z + z) := by
    linarith only [hz2, hZ2, hY, heE, mul_nonneg (sub_nonneg.2 heE)
      (by linarith only [hz0, hZ0] : 0 ≤ Z + z - 3 / 2)]
  linarith only [le_of_mul_le_mul_right hX (by linarith only [hx0, hX0]),
    le_of_mul_le_mul_right hZ (by linarith only [hz0, hZ0])]

theorem properFirstZeroTime_quadratic {d e : ℝ}
    (hrad : 0 ≤ d ^ 2 - 2 * e) :
    e - d * properFirstZeroTime d e + properFirstZeroTime d e ^ 2 / 2 = 0 := by
  unfold properFirstZeroTime properCrossingRoot
  linear_combination Real.sq_sqrt hrad / 2

theorem properFirstZeroTime_lt_of_quadratic {d e T : ℝ}
    (hrad : 0 ≤ d ^ 2 - 2 * e) (hTd : T ≤ d)
    (hnegative : e - d * T + T ^ 2 / 2 < 0) : properFirstZeroTime d e < T :=
  first_zero_lt_of_quadratic (sub_le_self _ (Real.sqrt_nonneg _)) hTd
    (properFirstZeroTime_quadratic hrad).ge hnegative

theorem properDecayLength_lt_of_energy {d e δ ell : ℝ} (hell : 0 ≤ ell)
    (hbound : d ^ 2 - e * (1 - e) + δ < (2 + ell / 2 + ell ^ 2 / 4) ^ 2) :
    properDecayLength d e δ < ell := by
  have hy : properEnergyRoot d e δ < 2 + ell / 2 + ell ^ 2 / 4 :=
    (Real.sqrt_lt' (by positivity)).2 hbound
  have hz : properDecayRoot d e δ < ell + 1 := (Real.sqrt_lt' (by linarith)).2 (by linarith)
  unfold properDecayLength
  linarith

-- `hδ0` is not needed for this upper bound; it stays in the statement for the callers.
set_option linter.unusedVariables false in
theorem properDecayLength_lt_fifty_two_hundredths {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properDecayLength d e δ < 13 / 25 := by
  refine properDecayLength_lt_of_energy (by norm_num) ?_
  linarith [mul_nonneg he0 (sub_nonneg.2 he1), pow_le_pow_left₀ (by linarith) hd1 2]

-- `hδ0` is not needed for this upper bound; it stays in the statement for the callers.
set_option linter.unusedVariables false in
theorem properDecayLength_lt_near_full {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 563 / 250)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 480) :
    properDecayLength d e δ < 43 / 100 := by
  refine properDecayLength_lt_of_energy (by norm_num) ?_
  linarith [mul_nonneg he0 (sub_nonneg.2 he1), pow_le_pow_left₀ (by linarith) hd1 2]

/-- Over a parameter box `[199/100, D] × [0, E]`, small heights stop early directly, and the
remaining heights reduce to the far corner `(D, E)`, bounded by a first zero `T` and a decay
length `L`. -/
theorem properExcessEnd_lt_of_corner {d e δ D E T L B : ℝ}
    (hd0 : 199 / 100 ≤ d) (hdD : d ≤ D) (hD : D ≤ 2311 / 1000) (he0 : 0 ≤ e) (heE : e ≤ E)
    (hE : E ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) (hTD : T ≤ D) (hT : E - D * T + T ^ 2 / 2 < 0)
    (hL : 0 ≤ L) (henergy : D ^ 2 - E * (1 - E) + δ < (2 + L / 2 + L ^ 2 / 4) ^ 2)
    (hB : 69 / 100 ≤ B) (hTL : T + L ≤ B) : properExcessEnd d e δ < B := by
  have hd2 := pow_le_pow_left₀ (by norm_num) hd0 2
  have hD2 := pow_le_pow_left₀ (by norm_num) (hd0.trans hdD) 2
  rcases le_or_gt e (3 / 10) with hsmall | hlarge
  · have ht := properFirstZeroTime_lt_of_quadratic (d := d) (e := e) (T := 17 / 100)
      (by linarith) (by linarith) (by linarith)
    have hl := properDecayLength_lt_fifty_two_hundredths hd0 (hdD.trans hD) he0 (by linarith)
      hδ0 hδ1
    unfold properExcessEnd
    linarith
  · have ht := properFirstZeroTime_lt_of_quadratic (by linarith) hTD hT
    have hl := properDecayLength_lt_of_energy hL henergy
    have := (properExcessEnd_mono_width hd0 hdD hD he0 (heE.trans hE) hδ0 hδ1).trans
      (properExcessEnd_mono_height (hd0.trans hdD) hD hlarge.le heE hE hδ0 hδ1)
    unfold properExcessEnd at *
    linarith

theorem properExcessEnd_lt_near_full {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 563 / 250)
    (he0 : 0 ≤ e) (he1 : e ≤ 19 / 25) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 480) :
    properExcessEnd d e δ < 73 / 100 :=
  properExcessEnd_lt_of_corner (T := 37 / 100) (L := 9 / 25) hd0 hd1 (by norm_num) he0 he1
    (by norm_num) hδ0 (by linarith) (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

theorem properExcessEnd_lt_nonnegative_middle {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 179 / 200) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ < 91 / 100 :=
  properExcessEnd_lt_of_corner (T := 107 / 250) (L := 241 / 500) hd0 hd1 le_rfl he0 he1
    (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

theorem properExcessEnd_lt_negative_middle {d e δ : ℝ}
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30) :
    properExcessEnd d e δ < 9 / 10 :=
  properExcessEnd_lt_of_corner (T := 51 / 100) (L := 39 / 100) hd0 hd1 (by norm_num) he0 he1
    le_rfl hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

end AmbidextrousSofa.Analysis
