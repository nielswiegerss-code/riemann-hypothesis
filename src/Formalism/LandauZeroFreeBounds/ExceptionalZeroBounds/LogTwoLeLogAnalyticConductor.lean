module

public import Formalism.LandauZeroFreeBounds.Statement
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Lemma

@[expose] public section

open Complex

namespace Formalism.ZeroFreeDirichlet

lemma one_le_modulus_real (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)

lemma log_two_le_log_analytic_conductor (q : ℕ) [NeZero q] (t : ℝ) : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := one_le_modulus_real q
  have h2 := abs_nonneg t
  exact Real.log_le_log (by norm_num) (by nlinarith)

lemma log_analytic_conductor_ge_const (q : ℕ) [NeZero q] (t : ℝ) : 69 / 100 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h := Real.log_two_gt_d9
  have h2 := log_two_le_log_analytic_conductor q t
  linarith

lemma zero_free_region_mono_half {c₁ : ℝ} (hc : 0 < c₁) (q : ℕ) [NeZero q] (s : ℂ)
    (h : InRegion (c₁ / 2) q s) : InRegion c₁ q s := by
  unfold InRegion at h ⊢
  have hL : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_analytic_conductor q s.im)
  have h2 : c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le hL (by linarith)
  linarith

lemma log_le_of_le_exp_log_conductor {A M L : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) (hL : Real.log 2 ≤ L) (hX : 0 < Real.exp L)
    (hML : M ≤ 2 * A * Real.exp L) :
    Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * L := by
  have hA2 : 0 < 2 * A := by linarith
  have h1 : Real.log M ≤ Real.log (2 * A) + L := by
    have h := Real.log_le_log (by linarith) hML
    rwa [Real.log_mul hA2.ne' (Real.exp_pos L).ne', Real.log_exp] at h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 * A) ≤ Real.log (2 * A) / Real.log 2 * L := by
    have hq : 0 ≤ Real.log (2 * A) / Real.log 2 := div_nonneg hlA hl2.le
    calc Real.log (2 * A) = Real.log (2 * A) / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ Real.log (2 * A) / Real.log 2 * L := mul_le_mul_of_nonneg_left hL hq
  rw [add_mul, one_mul]
  linarith

end Formalism.ZeroFreeDirichlet
