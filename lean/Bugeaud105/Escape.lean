import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Escape of an irrational doubling orbit from small neighbourhoods of the integers

The proof is independent of the conjecture declarations.  It uses only rounding,
integer separation, and the unboundedness of powers of two.
-/

namespace Bugeaud105

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

end Bugeaud105
