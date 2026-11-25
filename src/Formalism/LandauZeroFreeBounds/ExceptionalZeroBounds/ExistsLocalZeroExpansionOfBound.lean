module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor

@[expose] public section

open Complex Filter Topology Metric

namespace Formalism.ZeroFreeDirichlet

/-- In the local Landau expansion, the coefficient at each zero is its analytic order. -/
theorem exists_localZeroExpansion_with_order (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, analyticOrderAt f ρ = (m ρ : ℕ∞)) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  have hr3 : 0 < r / 3 := by linarith
  obtain ⟨Z, m, h, hZ, hm, hhd, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f z₀ r (r / 3) hr3 (by linarith) hf hfz₀
  have horder : ∀ ρ ∈ Z, analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    intro ρ hρ
    have hρmem := ((hZ ρ).mp hρ).1
    have hρb := closedBall_subset_ball (by linarith : r / 3 < r) hρmem
    have hfa := (hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball ρ hρb
    have hha := (hhd.mono ball_subset_closedBall).analyticOnNhd isOpen_ball ρ hρb
    apply hfa.analyticOrderAt_eq_natCast.mpr
    refine ⟨fun w => (∏ ρ' ∈ Z.erase ρ, (w - ρ') ^ m ρ') * h w, by fun_prop, ?_, ?_⟩
    · exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
        pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) (hh0 ρ hρmem)
    · filter_upwards [isOpen_ball.mem_nhds hρb] with w hw
      rw [smul_eq_mul, hfac w (ball_subset_closedBall hw), ← mul_assoc, Finset.mul_prod_erase Z (fun ρ' => (w - ρ') ^ m ρ') hρ]
  exact ⟨Z, m, hZ, hm, horder,
    Formalism.ZF.localZeroExpansion_bounds Formalism.ZF.logDerivBoundOnBall hr hM hZ hhd hh0 hfac hbound⟩

theorem exists_localZeroExpansion_of_bound (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  obtain ⟨Z, m, hZ, hm, horder, hsum, hest⟩ :=
    exists_localZeroExpansion_with_order f z₀ r M hr hM hf hfz₀ hbound
  have ha (ρ : ℂ) (hρ : ρ ∈ Z) : AnalyticAt ℂ f ρ :=
    (hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball ρ
      (closedBall_subset_ball (by linarith : r / 3 < r) ((hZ ρ).mp hρ).1)
  refine ⟨Z, m, hZ, hm, ?_, ?_, hsum, hest⟩
  · intro ρ hρ hd
    have htwo : (2 : ℕ∞) ≤ analyticOrderAt f ρ := by
      apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) (ha ρ hρ)).mpr
      intro i hi
      interval_cases i <;> simp [((hZ ρ).mp hρ).2, hd]
    simpa [horder ρ hρ] using htwo
  · intro ρ hρ hd
    have hone := (ha ρ hρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((hZ ρ).mp hρ).2 hd
    simpa [horder ρ hρ] using hone

end Formalism.ZeroFreeDirichlet
