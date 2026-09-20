import Bugeaud105.Escape
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace Bugeaud105

lemma rounded_mul_near (θ e : ℝ) (he : e ≠ 0) :
    |(round (θ / e) : ℝ) * e - θ| ≤ |e| / 2 := by
  have h := mul_le_mul_of_nonneg_right (abs_sub_round (θ / e)) (abs_nonneg e)
  have hident : (θ / e - (round (θ / e) : ℝ)) * e =
      -((round (θ / e) : ℝ) * e - θ) := by field_simp; ring
  rw [← abs_mul, hident, abs_neg] at h
  linarith

/-- Away from the factorial grid, a fixed window of consecutive multipliers meets
every interval of the requested length.  All intervals and fractional parts in
this statement are real, so no circle-to-interval endpoint conversion is hidden. -/
theorem factorial_window_hit (Q : ℕ) (hQ : 0 < Q) (y a ε : ℝ)
    (hε : 1 / ((Q : ℝ) + 1) < ε)
    (ha : 0 ≤ a) (haε : a + ε ≤ 1)
    (hescape : 1 / 4 ≤ |(Q.factorial : ℝ) * y - round ((Q.factorial : ℝ) * y)|) :
    ∃ j : ℕ, 10 * Q.factorial ≤ j ∧ j < 2 * (10 * Q.factorial) ∧
      Int.fract ((j : ℝ) * y) ∈ Set.Icc a (a + ε) := by
  let M := Q.factorial
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.factorial_pos Q
  have hQM : Q ≤ M := Nat.self_le_factorial Q
  obtain ⟨q, hqpos, hqQ, happrox⟩ := Real.exists_nat_abs_mul_sub_round_le y hQ
  have hqM : (q : ℝ) ≤ M := by exact_mod_cast hqQ.trans hQM
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  obtain ⟨d, hd⟩ := Nat.dvd_factorial hqpos hqQ
  have hMd : (M : ℝ) = (q : ℝ) * d := by exact_mod_cast hd
  let p : ℤ := round ((q : ℝ) * y)
  let e : ℝ := (q : ℝ) * y - p
  let β : ℝ := |e|
  have hβnonneg : 0 ≤ β := abs_nonneg e
  have hβsmall : β < ε := lt_of_le_of_lt happrox hε
  have hdβ : (1 : ℝ) / 4 ≤ (d : ℝ) * β := by
    have hround := round_le ((M : ℝ) * y) ((d : ℤ) * p)
    have hid : (M : ℝ) * y - (((d : ℤ) * p : ℤ) : ℝ) = (d : ℝ) * e := by
      push_cast
      dsimp [e]
      rw [hMd]
      ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] at hround
    exact hescape.trans hround
  have hβpos : 0 < β := by
    by_contra! hn
    have hz : β = 0 := le_antisymm hn hβnonneg
    rw [hz, mul_zero] at hdβ
    norm_num at hdβ
  have he : e ≠ 0 := by
    intro he
    have : β = 0 := by simp [β, he]
    linarith
  have hqβ : (q : ℝ) ≤ 4 * M * β := by
    have h := mul_le_mul_of_nonneg_left hdβ hqR.le
    rw [hMd]
    nlinarith
  let C : ℕ := 15 * M
  let target : ℝ := a + ε / 2
  let θ : ℝ := Int.fract (target - (C : ℝ) * y)
  let z : ℤ := round (θ / e)
  have hθ0 : 0 ≤ θ := Int.fract_nonneg _
  have hθ1 : θ < 1 := Int.fract_lt_one _
  have hnear : |(z : ℝ) * e - θ| ≤ β / 2 := rounded_mul_near θ e he
  have hzβ : |(z : ℝ)| * β ≤ θ + β / 2 := by
    have hnear' := abs_le.mp hnear
    have habs : |(z : ℝ) * e| ≤ θ + β / 2 := by
      rw [abs_le]
      constructor <;> linarith
    simpa only [abs_mul] using habs
  have hqz : (q : ℝ) * |(z : ℝ)| < 5 * M := by
    apply (mul_lt_mul_iff_left₀ hβpos).mp
    have h1 := mul_le_mul_of_nonneg_left hzβ hqR.le
    have h2 := mul_lt_mul_of_pos_left hθ1 hqR
    have h3 := mul_le_mul_of_nonneg_right hqM hβnonneg
    nlinarith
  let w : ℤ := (C : ℤ) + (q : ℤ) * z
  have hwR : (w : ℝ) = 15 * M + (q : ℝ) * z := by
    dsimp [w, C]
    push_cast
    ring
  have hwlo : (10 * M : ℝ) < w := by
    rw [hwR]
    have h := mul_le_mul_of_nonneg_left (neg_abs_le (z : ℝ)) hqR.le
    linarith
  have hwhi : (w : ℝ) < 20 * M := by
    rw [hwR]
    have h := mul_le_mul_of_nonneg_left (le_abs_self (z : ℝ)) hqR.le
    linarith
  have hwnonneg : 0 ≤ w := by
    have : (0 : ℝ) ≤ w := le_of_lt (lt_trans (by positivity) hwlo)
    exact_mod_cast this
  let b : ℝ := target + ((z : ℝ) * e - θ)
  have hab : a < b := by
    have := (abs_le.mp hnear).1
    dsimp [b, target]
    linarith
  have hbaε : b < a + ε := by
    have := (abs_le.mp hnear).2
    dsimp [b, target]
    linarith
  have hfract : Int.fract ((w : ℝ) * y) = b := by
    apply Int.fract_eq_iff.mpr
    refine ⟨ha.trans hab.le, hbaε.trans_le haε, z * p - ⌊target - (C : ℝ) * y⌋, ?_⟩
    dsimp [b, θ, e, w]
    rw [Int.fract]
    push_cast
    ring
  refine ⟨w.toNat, ?_, ?_, ?_⟩
  · have : (10 * M : ℤ) ≤ w := by exact_mod_cast hwlo.le
    exact_mod_cast (show (10 * M : ℤ) ≤ (w.toNat : ℤ) by simpa [Int.toNat_of_nonneg hwnonneg] using this)
  · have : w < (20 * M : ℤ) := by exact_mod_cast hwhi
    have : w.toNat < 20 * M := by
      exact_mod_cast (show (w.toNat : ℤ) < (20 * M : ℤ) by simpa [Int.toNat_of_nonneg hwnonneg] using this)
    convert this using 1
    dsimp [M]
    omega
  · have hwcast : (w.toNat : ℝ) = w := by exact_mod_cast Int.toNat_of_nonneg hwnonneg
    rw [hwcast, hfract]
    exact ⟨hab.le, hbaε.le⟩

end Bugeaud105
