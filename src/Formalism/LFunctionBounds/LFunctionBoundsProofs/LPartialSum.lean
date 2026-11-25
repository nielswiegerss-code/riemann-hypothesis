module

public import Formalism.LFunctionBounds.PositivityBound
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt

@[expose] public section

open Complex Filter Topology

namespace Formalism.FX


open LFunctionPartialSum in
lemma LFunctionPartialSum.norm_tail_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  let weight (i : ℕ) := ((i + (N + 1) : ℕ) : ℝ) ^ (-s.re)
  have hterm (i : ℕ) : ‖dterm χ s (i + (N + 1))‖ ≤
      B * (‖s‖ / s.re) * (weight i - weight (i + 1)) := by
    simpa only [weight, Nat.cast_add, Nat.cast_one, mul_assoc, add_assoc, add_comm, add_left_comm] using
      norm_dterm_le' χ hB hs (n := i + (N + 1)) (by omega)
  have hsum := (summable_nat_add_iff (N + 1)).mpr (summable_dterm χ hB hs)
  refine le_of_tendsto' hsum.hasSum.tendsto_sum_nat.norm fun n => ?_
  refine (norm_sum_le_of_le _ fun i _ => hterm i).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hB0 := (norm_nonneg _).trans (hB 0)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB0 (div_nonneg (norm_nonneg _) hs.le))
  have hn : 0 ≤ weight n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simpa [weight] using sub_le_self (weight 0) hn

open LFunctionPartialSum in
theorem l_function_partial_sum : LPartialSum := by
  intro q _ χ hχ B hB s hs N hN
  have hB' : ∀ M, ‖Ap χ M‖ ≤ B := hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  rw [LFunction_eq_G χ hχ hB' hs, ← partial_identity χ s N]
  have hsum := summable_dterm χ hB' hs
  have hG : LFunctionPartialSum.G χ s = ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm χ s n + Ap χ N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le χ hB' hs N
  have h2 : ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB' N) (Real.rpow_nonneg (by positivity) _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by linarith) (by linarith)
  have hq : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  have h5 : 0 ≤ ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  calc ‖∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm χ s (i + (N + 1))‖ + ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring
    _ ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (by linarith))
    _ ≤ 2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
          mul_nonneg (mul_nonneg hB0 (by linarith)) h4
        linarith

end Formalism.FX
