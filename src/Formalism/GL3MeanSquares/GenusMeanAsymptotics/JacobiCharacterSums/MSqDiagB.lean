module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.NumberTheory.Primorial

@[expose] public section

open Finset Classical

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      2 * Real.log 4 * Real.log (2 * y) / y := by
  have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
  have hL0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hy2pos : 0 < (y:ℝ) ^ 2 := by positivity
  have hterm : ∀ p ∈ (Ioc y (2 * y)).filter Nat.Prime,
      Real.log p ^ 2 / (p : ℝ) ^ 2 ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
    have hp1 : (y:ℝ) < p := by exact_mod_cast h1
    have hp2 : (p:ℝ) ≤ 2 * y := by exact_mod_cast h2
    have hppos : (0:ℝ) < p := by linarith
    have hp2pos : 0 < (p:ℝ) ^ 2 := by positivity
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hlle : Real.log p ≤ Real.log (2 * y) := Real.log_le_log hppos hp2
    have hyp : (y:ℝ) ^ 2 ≤ (p:ℝ) ^ 2 := by nlinarith
    have hnum : 0 ≤ Real.log (2 * y) * Real.log p := mul_nonneg hL0 hlp
    calc Real.log p ^ 2 / (p:ℝ) ^ 2 = Real.log p * Real.log p / (p:ℝ) ^ 2 := by ring
      _ ≤ Real.log (2 * y) * Real.log p / (p:ℝ) ^ 2 := by
          gcongr ?_ * _ / _
      _ ≤ Real.log (2 * y) * Real.log p / (y:ℝ) ^ 2 := by
          gcongr _ / ?_
      _ = Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by ring
  have hsum : ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ≤ 2 * y * Real.log 4 := by
    have hsub : (Ioc y (2 * y)).filter Nat.Prime ⊆ (Finset.range (2 * y + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.range (2 * y + 1)).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Real.log (primorial (2 * y)) := by
          rw [primorial, Nat.cast_prod, Real.log_prod]
          intro p hp
          rw [Finset.mem_filter] at hp
          exact_mod_cast hp.2.ne_zero
      _ ≤ Real.log (4 ^ (2 * y)) := by
          apply Real.log_le_log
          · exact_mod_cast primorial_pos (2 * y)
          · exact_mod_cast primorial_le_four_pow (2 * y)
      _ = 2 * y * Real.log 4 := by
          rw [Real.log_pow]
          push_cast
          ring
  calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p :=
        Finset.sum_le_sum hterm
    _ = Real.log (2 * y) / (y:ℝ) ^ 2 * ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * (2 * y * Real.log 4) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hL0 (sq_nonneg _))
    _ = 2 * Real.log 4 * Real.log (2 * y) / y := by
        field_simp

theorem sum_log_sq_div_sq_primes_tail_le (N : ℕ) : ∀ d y : ℕ, 1 ≤ y → N - y ≤ d →
    ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
  intro d
  induction d with
  | zero =>
    intro y hy hd
    have hN : N ≤ y := by omega
    rw [Finset.Ioc_eq_empty_of_le hN, Finset.filter_empty, Finset.sum_empty]
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4) (by linarith)) (by positivity)
  | succ d ih =>
    intro y hy hd
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hy0 : (0:ℝ) < y := by linarith
    have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) hy0'
    have hblock := sum_log_sq_div_sq_primes_dyadic_le y hy
    by_cases hN : N ≤ 2 * y
    · have hsub : (Ioc y N).filter Nat.Prime ⊆ (Ioc y (2 * y)).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hN)
      calc ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ 2 * Real.log 4 * Real.log (2 * y) / y := hblock
        _ ≤ 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            gcongr ?_ / _
            rw [hlog2y]
            nlinarith [mul_nonneg hl4 hly, mul_nonneg hl4 hl2]
    · push Not at hN
      have hsplit : (Ioc y N).filter Nat.Prime =
          (Ioc y (2 * y)).filter Nat.Prime ∪ (Ioc (2 * y) N).filter Nat.Prime := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) hN.le]
      have hdisj : Disjoint ((Ioc y (2 * y)).filter Nat.Prime) ((Ioc (2 * y) N).filter Nat.Prime) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_Ioc] at ha hb
        omega
      have ht := ih (2 * y) (by omega) (by omega)
      rw [hsplit, Finset.sum_union hdisj]
      calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 +
            ∑ p ∈ (Ioc (2 * y) N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ 2 * Real.log 4 * Real.log (2 * y) / y +
            4 * Real.log 4 * (Real.log ((2 * y : ℕ) : ℝ) + 2 * Real.log 2) / ((2 * y : ℕ) : ℝ) :=
            add_le_add hblock ht
        _ = 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            push_cast
            rw [hlog2y]
            field_simp <;> ring

theorem sP_cN_nonneg (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ sP (cN x) N p := by
  unfold sP cN
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

theorem sP_cN_le_log_div (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) (hp : p.Prime) :
    sP (cN x) N p ≤ 2 * x * Real.log p / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp2
  have hppos : (0:ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set r : ℝ := 1 / (p:ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hppos]; linarith
  have hrh : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hpR
  have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Icc 1 N).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpp, hmf⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p = q := by
      have h1 : p ∣ q ^ k := by rw [← hmf]; exact Nat.minFac_dvd _
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
    subst hpq
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    have hlt := Nat.lt_pow_self (by omega : 1 < p) (n := k)
    exact le_of_lt (lt_of_lt_of_le hlt hnN)
  have h1 : sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      Real.log p * (x / n) := by
    unfold sP
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_filter] at hn
    unfold cN
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left hn.2.1, hn.2.2]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
  calc sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
        Real.log p * (x / n) := h1
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * (x / n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => mul_nonneg hlog (div_nonneg hx (Nat.cast_nonneg n)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * x * r ^ k := by
        rw [Finset.sum_image (Nat.pow_right_injective hp2).injOn]
        apply Finset.sum_congr rfl
        intro k _
        show Real.log p * (x / ((p ^ k : ℕ) : ℝ)) = Real.log p * x * r ^ k
        rw [hr, Nat.cast_pow, one_div, inv_pow]
        ring
    _ ≤ ∑ k ∈ Ico 1 (N + 1), Real.log p * x * r ^ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_Ico]
          omega
        · intro k _ _
          exact mul_nonneg (mul_nonneg hlog hx) (pow_nonneg hr0 k)
    _ = Real.log p * x * ∑ k ∈ Ico 1 (N + 1), r ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.log p * x * (r ^ 1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (mul_nonneg hlog hx)
    _ ≤ Real.log p * x * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog hx)
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith
    _ = 2 * x * Real.log p / p := by rw [hr]; ring

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
