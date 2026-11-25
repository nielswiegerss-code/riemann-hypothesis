module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormLogDerivLeLamF
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

namespace Formalism.ZF

theorem logDerivBoundRightHalfPlane : LogDerivRight := by
  obtain ⟨B, hB⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hB)
  refine ⟨max (max B 0) (lamF (1 + ε / 2)), le_max_of_le_left (le_max_right _ _),
    fun s hs => (norm_logDeriv_le_lamF hs).trans ?_⟩
  have hσ1 : 0 < s.re - 1 := sub_pos.mpr hs
  have hpos : 0 < 1 / (s.re - 1) := by positivity
  rcases lt_or_ge s.re (1 + ε / 2) with hlt | hge
  · have hreal : ‖((s.re : ℂ) - 1)‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ1.le]
    have hb := hball (by rw [Complex.dist_eq, hreal]; linarith) (by simpa using hs.ne')
    simp only [norm_one, mul_one] at hb
    rw [lamF_eq_norm hs, LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs), neg_div, norm_neg]
    have htri := norm_sub_le (deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹)
      (((s.re : ℂ) - 1)⁻¹)
    simp only [add_sub_cancel_right, norm_inv, hreal] at htri
    have hBmax : B ≤ max (max B 0) (lamF (1 + ε / 2)) := le_max_of_le_left (le_max_left _ _)
    rw [one_div]
    linarith
  · linarith [lamF_anti (by linarith) hge, le_max_right (max B 0) (lamF (1 + ε / 2))]

end Formalism.ZF
