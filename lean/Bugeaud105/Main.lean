import Bugeaud105.Coverage
import Bugeaud105.Sequence
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.FieldTheory.IntermediateField.Basic

namespace Bugeaud105

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

end Bugeaud105
