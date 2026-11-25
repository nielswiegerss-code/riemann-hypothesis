module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  suffices h : ∀ n : ℕ,
      (x ^ n + 1) * Real.log (x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2)) / x ^ (n + 1)
        ≤ 2 * ((n : ℝ) + 3) by
    have hbound : 2 * ((398 : ℝ) + 3) = 802 := by norm_num
    simpa only [Nat.reduceAdd, Nat.cast_ofNat, hbound] using h 398
  intro n
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ n := by positivity
  have hp1 : 1 ≤ x ^ n := one_le_pow₀ hx1
  have hA : x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2) = x ^ n * (x ^ 2 + 1) := by
    rw [pow_add]
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hsq_pos : 0 < x ^ 2 + 1 := by positivity
  have hlog_sq : Real.log (x ^ 2 + 1) ≤ 3 * Real.log x := by
    calc Real.log (x ^ 2 + 1) ≤ Real.log (x ^ 3) := Real.log_le_log hsq_pos hsq
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlog_x : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hL1 : Real.log (x ^ n * (x ^ 2 + 1)) ≤ ((n : ℝ) + 3) * x := by
    rw [Real.log_mul hp.ne' hsq_pos.ne', Real.log_pow]
    calc (n : ℝ) * Real.log x + Real.log (x ^ 2 + 1)
        ≤ (n : ℝ) * Real.log x + 3 * Real.log x := add_le_add le_rfl hlog_sq
      _ = ((n : ℝ) + 3) * Real.log x := by ring
      _ ≤ ((n : ℝ) + 3) * x := mul_le_mul_of_nonneg_left hlog_x (by positivity)
  have hxn : x ≤ x ^ (n + 1) := by
    simpa only [pow_succ, one_mul] using mul_le_mul_of_nonneg_right hp1 hx0.le
  rw [hA, div_le_iff₀ (by positivity : (0 : ℝ) < x ^ (n + 1))]
  calc (x ^ n + 1) * Real.log (x ^ n * (x ^ 2 + 1))
      ≤ (x ^ n + 1) * (((n : ℝ) + 3) * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = ((n : ℝ) + 3) * (x ^ (n + 1) + x) := by rw [pow_succ]; ring
    _ ≤ ((n : ℝ) + 3) * (x ^ (n + 1) + x ^ (n + 1)) := by gcongr
    _ = 2 * ((n : ℝ) + 3) * x ^ (n + 1) := by ring

end Formalism.HermitianLattices.Ext.BoxTail
