import Bugeaud105.Escape
import Mathlib.Data.Nat.ModEq
import FormalConjecturesForMathlib.NumberTheory.Lacunary

namespace Bugeaud105

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

end Bugeaud105
