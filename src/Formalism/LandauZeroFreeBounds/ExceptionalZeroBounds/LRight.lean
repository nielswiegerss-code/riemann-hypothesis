module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormLogDerivLeLamF
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace Formalism.ZeroFreeDirichlet

lemma norm_term_twist_moebius_le {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  apply LSeries.norm_term_le
  simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_one₀ h1 (norm_nonneg _) h2

open Formalism.ZF.MoebiusInverseZetaBounds in
theorem inverseBound : LInvBound := by
  intro q _ χ s hs
  have hσ1 : 0 < s.re - 1 := by linarith
  have hshift : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) ≤ s.re / (s.re - 1) := by
    calc _ ≤ 1 + 1 / (s.re - 1) := tsum_rpow_le hσ1
      _ = s.re / (s.re - 1) := by field_simp; ring
  have hp : -(s.re - 1) - 1 < -1 := by linarith
  have hfun : (fun n : ℕ => ‖term (1 : ℕ → ℂ) s (n + 1)‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) :=
    funext (norm_term_one_succ s)
  have hS1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1, hfun]
    exact summable_shift hp
  have hT1 : ∑' n, ‖term (1 : ℕ → ℂ) s n‖ ≤ s.re / (s.re - 1) := by
    rw [hS1.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add, hfun]
    exact hshift
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hinv : ‖LSeries ↗χ s‖⁻¹ = ‖LSeries (↗χ * ↗μ) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
  rw [hinv]
  exact (tsum_of_norm_bounded hS1.hasSum (norm_term_twist_moebius_le χ s)).trans hT1

lemma negLD_eq_LSeries_mul_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries ↗χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [negLD, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div]

lemma norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  have hSΛ : Summable fun n => ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  have hle : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
    intro n
    calc ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ s n‖ := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ‖term ↗Λ (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
  exact tsum_of_norm_bounded hSΛ.hasSum hle

theorem l_log_deriv_right : LLogDerivRight := by
  obtain ⟨C, hC0, hC⟩ := Formalism.ZF.logDerivBoundRightHalfPlane
  refine ⟨C, hC0, ?_⟩
  intro q _ χ s hs
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs]
  refine le_trans (norm_LSeries_twist_vonMangoldt_le χ hs) ?_
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  rw [Formalism.ZF.lamF_eq_norm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, norm_neg]
  have h := hC (s.re : ℂ) hre
  simpa using h

end Formalism.ZeroFreeDirichlet
