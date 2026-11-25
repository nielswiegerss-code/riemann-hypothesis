module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma

@[expose] public section

open Complex Finset

namespace Formalism.ZeroFreeDirichlet

lemma character_sum_range_modulus_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩
    have h1 := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1
  rw [Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

lemma character_sum_range_add_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by
  rw [Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]
  simp only [Nat.cast_add, ZMod.natCast_self, zero_add]

lemma norm_character_sum_range_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ q := by
  have hperiod : Function.Periodic (fun k => ∑ n ∈ range k, χ (n : ZMod q)) q :=
    fun k => by simpa [add_comm k q] using character_sum_range_add_modulus χ hχ k
  rw [← hperiod.map_mod_nat M]
  calc ‖∑ n ∈ range (M % q), χ (n : ZMod q)‖ ≤ ∑ n ∈ range (M % q), (1 : ℝ) :=
         norm_sum_le_of_le _ fun n _ => DirichletCharacter.norm_le_one χ _
    _ ≤ q := by simpa using (Nat.mod_lt M (NeZero.pos q)).le

lemma norm_character_sum_Icc_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Icc 1 M, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have h1 : ∑ n ∈ range (M + 1), χ (n : ZMod q) =
      χ ((0 : ℕ) : ZMod q) + ∑ n ∈ Icc 1 M, χ (n : ZMod q) := by
    have hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M), zero_add, hI]
  have h2 : ∑ n ∈ Icc 1 M, χ (n : ZMod q) =
      ∑ n ∈ range (M + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q) := by
    rw [h1]; ring
  rw [h2]
  calc _ ≤ ‖∑ n ∈ range (M + 1), χ (n : ZMod q)‖ + ‖χ ((0 : ℕ) : ZMod q)‖ := norm_sub_le _ _
    _ ≤ q + 1 := add_le_add (norm_character_sum_range_le χ hχ _) (DirichletCharacter.norm_le_one χ _)

theorem lfunction_polynomial_growth : LGrowth := by
  refine ⟨9, ?_⟩
  intro q _ χ hχ s hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hσ : 0 < s.re := by linarith
  have hB := norm_character_sum_Icc_le χ hχ
  have hP := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) hB s hσ 1 le_rfl
  simp only [Nat.cast_one, Real.one_rpow, mul_one, Finset.Icc_self, Finset.sum_singleton] at hP
  have h1 : ‖χ (1 : ZMod q) * (1 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [one_cpow, mul_one]; exact DirichletCharacter.norm_le_one χ _
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ hσ]; nlinarith
  have hL : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by
    have := norm_le_insert' (DirichletCharacter.LFunction χ s) (χ (1 : ZMod q) * (1 : ℂ) ^ (-s))
    linarith
  calc ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := hL
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + 2 * ‖s‖) := by gcongr
    _ ≤ 9 * q * (1 + ‖s‖) := by nlinarith

end Formalism.ZeroFreeDirichlet
