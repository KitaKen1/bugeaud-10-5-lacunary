import Mathlib

#eval Lean.versionString

/-!
# Bugeaud Problem 10.5: standalone Lean4Web proof

This file reproduces the two statement types registered in Formal Conjectures
and proves both of them using mathlib only.  The Formal Conjectures package is
not imported here; see `../lean/` for the exact-type compatibility check.
-/

open Filter

/-- The real-valued lacunarity definition used by Formal Conjectures. -/
def IsLacunaryReal (a : ℕ → ℝ) : Prop :=
  ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * a k < a (k + 1)

namespace Bugeaud105Lean4Web


open Filter

lemma round_double_eq {x : ℝ}
    (hx : |x - round x| < 1 / 4)
    (h2x : |2 * x - round (2 * x)| < 1 / 4) :
    round (2 * x) = 2 * round x := by
  have hx' := abs_lt.mp hx
  have h2x' := abs_lt.mp h2x
  have h : |((round (2 * x) - 2 * round x : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith
  have hz : |round (2 * x) - 2 * round x| < (1 : ℤ) := by exact_mod_cast h
  have he : round (2 * x) - 2 * round x = 0 := by
    have := abs_lt.mp hz
    omega
  omega

lemma irrational_exists_round_escape {x : ℝ} (hx : Irrational x) :
    ∃ n : ℕ, 1 / 4 ≤ |x * 2 ^ n - round (x * 2 ^ n)| := by
  by_contra! h
  let e : ℕ → ℝ := fun n => x * 2 ^ n - round (x * 2 ^ n)
  have hstep (n : ℕ) : e (n + 1) = 2 * e n := by
    have heq : x * (2 : ℝ) ^ (n + 1) = 2 * (x * 2 ^ n) := by ring
    have hr := round_double_eq (h n) (by simpa only [heq] using h (n + 1))
    dsimp [e]
    rw [heq, hr]
    push_cast
    ring
  have hpow (n : ℕ) : e n = (2 : ℝ) ^ n * e 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih, pow_succ]; ring
  have hne : e 0 ≠ 0 := by
    simpa [e, sub_eq_zero] using hx.ne_int (round x)
  have hpos : 0 < |e 0| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (4 * |e 0|)) (by norm_num : (1 : ℝ) < 2)
  have hlarge : 1 / 4 < (2 : ℝ) ^ n * |e 0| := by
    have := (div_lt_iff₀ (by positivity : 0 < 4 * |e 0|)).mp hn
    nlinarith
  have hsmall : |e n| < 1 / 4 := h n
  rw [hpow, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)] at hsmall
  linarith

theorem irrational_round_escape_frequently {x : ℝ} (hx : Irrational x) :
    ∃ᶠ n : ℕ in atTop, 1 / 4 ≤ |x * 2 ^ n - round (x * 2 ^ n)| := by
  rw [Filter.frequently_atTop]
  intro N
  have hxN : Irrational (x * (2 : ℝ) ^ N) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      hx.mul_natCast (pow_ne_zero N (by norm_num : (2 : ℕ) ≠ 0))
  obtain ⟨n, hn⟩ := irrational_exists_round_escape hxN
  refine ⟨N + n, Nat.le_add_right _ _, ?_⟩
  simpa only [pow_add, mul_assoc] using hn

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

/-- An explicit increasing enumeration in dyadic blocks. -/
def blockSeq (J n : ℕ) : ℕ := (J + n % J) * 2 ^ (n / J)

lemma blockSeq_at (J k r : ℕ) (hJ : 0 < J) (hr : r < J) :
    blockSeq J (J * k + r) = (J + r) * 2 ^ k := by
  simp [blockSeq, Nat.add_mod, Nat.mul_add_div hJ, Nat.mod_eq_of_lt hr,
    Nat.div_eq_of_lt hr]

lemma blockSeq_pos {J : ℕ} (hJ : 0 < J) (n : ℕ) : 0 < blockSeq J n := by
  unfold blockSeq
  positivity

lemma blockSeq_step {J : ℕ} (hJ : 0 < J) (n : ℕ) :
    blockSeq J (n + 1) = blockSeq J n + 2 ^ (n / J) := by
  have hr : n % J < J := Nat.mod_lt n hJ
  have hn : n = J * (n / J) + n % J := (Nat.div_add_mod n J).symm
  by_cases hnext : n % J + 1 < J
  · have hn1 : n + 1 = J * (n / J) + (n % J + 1) := by omega
    rw [hn1, blockSeq_at J (n / J) (n % J + 1) hJ hnext]
    unfold blockSeq
    ring
  · have hr1 : n % J + 1 = J := by omega
    have hn1 : n + 1 = J * (n / J + 1) + 0 := by nlinarith
    rw [hn1, blockSeq_at J (n / J + 1) 0 hJ hJ]
    unfold blockSeq
    rw [pow_succ]
    simp only [Nat.add_zero]
    have hm := congrArg (fun t : ℕ => t * 2 ^ (n / J)) hr1
    nlinarith only [hm]

theorem blockSeq_lacunary {J : ℕ} (hJ : 0 < J) :
    IsLacunaryReal (fun n => (blockSeq J n : ℝ)) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  refine ⟨1 + 1 / (2 * J), ?_, Filter.Eventually.of_forall ?_⟩
  · have : (0 : ℝ) < 1 / (2 * J) := by positivity
    linarith
  intro n
  have hr : ((n % J : ℕ) : ℝ) < J := by exact_mod_cast Nat.mod_lt n hJ
  have hcoeff : (1 + 1 / (2 * (J : ℝ))) * (J + ((n % J : ℕ) : ℝ)) <
      J + ((n % J : ℕ) : ℝ) + 1 := by
    have hdiv : ((J : ℝ) + ((n % J : ℕ) : ℝ)) / (2 * J) < 1 := by
      apply (div_lt_one (by positivity : (0 : ℝ) < 2 * J)).mpr
      linarith
    calc
      _ = (J : ℝ) + ((n % J : ℕ) : ℝ) + ((J : ℝ) + ((n % J : ℕ) : ℝ)) / (2 * J) := by ring
      _ < _ := by linarith
  have hmul := mul_lt_mul_of_pos_right hcoeff (by positivity : (0 : ℝ) < 2 ^ (n / J))
  change (1 + 1 / (2 * (J : ℝ))) * (blockSeq J n : ℝ) < (blockSeq J (n + 1) : ℝ)
  rw [blockSeq_step hJ n]
  simp only [blockSeq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

open Filter

/-- A single positive integer sequence works for all irrational real numbers.
The sequence depends only on the prescribed interval length. -/
theorem exists_integer_sequence {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → ℕ, (∀ n, 0 < t n) ∧
      IsLacunaryReal (fun n => (t n : ℝ)) ∧
      ∀ ξ : ℝ, Irrational ξ → ∀ a ∈ Set.Icc (0 : ℝ) (1 - ε),
        ∃ y ∈ Set.Icc a (a + ε),
          MapClusterPt y atTop (fun n => Int.fract (ξ * (t n : ℝ))) := by
  obtain ⟨Q, hQlarge⟩ := exists_nat_gt (1 / ε)
  have hQR : (0 : ℝ) < Q := lt_trans (by positivity) hQlarge
  have hQ : 0 < Q := by exact_mod_cast hQR
  have hεQ : 1 / ((Q : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) + 1)).mpr
    have := (div_lt_iff₀ hε).mp hQlarge
    nlinarith
  let J := 10 * Q.factorial
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨blockSeq J, blockSeq_pos hJ, blockSeq_lacunary hJ, ?_⟩
  intro ξ hξ a ha
  apply isCompact_Icc.exists_mapClusterPt_of_frequently
  rw [Filter.frequently_atTop]
  intro N
  have hirr : Irrational ((Q.factorial : ℝ) * ξ) :=
    hξ.natCast_mul (Nat.factorial_ne_zero Q)
  have hfreq := irrational_round_escape_frequently hirr
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨k, hk, hescape⟩ := hfreq N
  have hescape' : 1 / 4 ≤
      |(Q.factorial : ℝ) * (ξ * 2 ^ k) - round ((Q.factorial : ℝ) * (ξ * 2 ^ k))| := by
    simpa only [mul_assoc] using hescape
  obtain ⟨j, hjlo, hjhi, hjhit⟩ :=
    factorial_window_hit Q hQ (ξ * 2 ^ k) a ε hεQ ha.1 (by linarith [ha.2]) hescape'
  have hr : j - J < J := by dsimp [J]; omega
  have hsum : J + (j - J) = j := Nat.add_sub_of_le hjlo
  refine ⟨J * k + (j - J), ?_, ?_⟩
  · have hJ1 : 1 ≤ J := hJ
    nlinarith
  · rw [blockSeq_at J k (j - J) hJ hr, hsum]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm, mul_left_comm,
      mul_assoc] using hjhit

/-- The strong form of Bugeaud 10.5, proved for every intermediate field of ℝ/ℚ.
Finite-dimensionality is not required by this construction. -/
theorem moreover (K : IntermediateField ℚ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K → ∀ a, a ∈ Set.Icc (0 : ℝ) (1 - ε) →
        ∃ y ∈ Set.Icc a (a + ε),
          MapClusterPt y atTop (fun n => Int.fract (ξ * (t n : ℝ))) := by
  obtain ⟨t, ht, hlac, hξ⟩ := exists_integer_sequence hε
  have hcast (n : ℕ) : ((n : K) : ℝ) = (n : ℝ) := map_natCast K.subtype n
  refine ⟨fun n => (t n : K), ?_, ?_, ?_⟩
  · intro n
    simpa only [hcast, Nat.cast_pos] using ht n
  · simpa only [hcast] using hlac
  · intro ξ hξK a ha
    have hirr : Irrational ξ := by
      rintro ⟨q, hq⟩
      apply hξK
      rw [← hq]
      exact K.algebraMap_mem q
    simpa only [hcast] using hξ ξ hirr a ha



/-! ## Local copies of the two Formal Conjectures statement types -/

/-- The stronger “moreover” target, with the same mathematical type as the
registered Formal Conjectures declaration. -/
theorem problem_10_5_moreover (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K → ∀ a, a ∈ Set.Icc (0 : ℝ) (1 - ε) →
        ∃ y ∈ Set.Icc a (a + ε),
          MapClusterPt y atTop (fun n => Int.fract (ξ * (t n : ℝ))) := by
  exact moreover K hε

/-- The checked implication from the “moreover” statement to the limsup
statement, reproduced from the Formal Conjectures target file. -/
theorem problem_10_5_of_moreover
    (h : ∀ (K : IntermediateField ℚ ℝ), [FiniteDimensional ℚ K] →
      ∀ {ε : ℝ}, 0 < ε →
      ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
        IsLacunaryReal (fun k => (t k : ℝ)) ∧
        ∀ ξ : ℝ, ξ ∉ K → ∀ a, a ∈ Set.Icc (0 : ℝ) (1 - ε) →
          ∃ y ∈ Set.Icc a (a + ε),
            MapClusterPt y atTop (fun n => Int.fract (ξ * (t n : ℝ)))) :
    ∀ (K : IntermediateField ℚ ℝ), [FiniteDimensional ℚ K] →
      ∀ {ε : ℝ}, 0 < ε →
      ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
        IsLacunaryReal (fun k => (t k : ℝ)) ∧
        ∀ ξ : ℝ, ξ ∉ K →
          (1 - ε) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
  intro K _ ε hε
  obtain ⟨t, hpos, hlac, hξ⟩ := h K hε
  refine ⟨t, hpos, hlac, fun ξ hξK => ?_⟩
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => Int.fract (ξ * (t n : ℝ))) :=
    isBoundedUnder_of ⟨1, fun n => (Int.fract_lt_one (ξ * (t n : ℝ))).le⟩
  by_cases hε1 : ε ≤ 1
  · obtain ⟨y, hy, hcluster⟩ := hξ ξ hξK (1 - ε) ⟨by linarith, le_refl _⟩
    have hb_ge : IsBoundedUnder (· ≥ ·) atTop (fun n => Int.fract (ξ * (t n : ℝ))) :=
      isBoundedUnder_of ⟨0, fun n => Int.fract_nonneg (ξ * (t n : ℝ))⟩
    have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n => Int.fract (ξ * (t n : ℝ))) :=
      hb_ge.isCoboundedUnder_le
    have hle : y ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
      rw [Filter.le_limsup_iff hcob hb]
      exact fun a ha => MapClusterPt.frequently hcluster (eventually_gt_nhds ha)
    linarith [hy.1]
  · push Not at hε1
    have h0 : (0 : ℝ) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop :=
      le_limsup_of_frequently_le
        ((Filter.Eventually.of_forall
          fun n => Int.fract_nonneg (ξ * (t n : ℝ))).frequently) hb
    linarith

/-- The first Problem 10.5 target, with the same mathematical type as the
registered Formal Conjectures declaration. -/
theorem problem_10_5 (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K →
        (1 - ε) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop :=
  problem_10_5_of_moreover problem_10_5_moreover K hε

#print axioms problem_10_5_moreover
#print axioms problem_10_5

end Bugeaud105Lean4Web
