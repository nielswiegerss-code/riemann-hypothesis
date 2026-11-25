module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos
import Mathlib.Tactic.Linter.Style
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound

@[expose] public section

open Complex Filter Topology

namespace Formalism.ZF

open ComplexPowerDifferenceIntegral in
lemma norm_Dz_le {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re - 1)) := summable_shift (by linarith)
  calc ‖Dz s‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm (summable_norm_dz hs)
    _ ≤ ∑' n : ℕ, ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) :=
        (summable_norm_dz hs).tsum_le_tsum (norm_dz_le hs) (hsum.mul_left _)
    _ = ‖s - 1‖ * ‖s‖ * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s.re - 1) := tsum_mul_left
    _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) :=
        mul_le_mul_of_nonneg_left (MoebiusInverseZetaBounds.tsum_rpow_le hs) (by positivity)

theorem growthBound : ZetaGrowth := by
  intro s hs hs1
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    unfold riemannZeta₁ riemannZeta₀
    rw [ite_eq_right hs1, mul_sub, mul_inv_cancel₀ hne]; ring
  have hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1) := by
    rw [← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]; field_simp
  rw [hz, norm_div, div_le_iff₀ (norm_pos_iff.2 hne)]
  calc ‖s - ComplexPowerDifferenceIntegral.Dz s‖ ≤ ‖s‖ + ‖ComplexPowerDifferenceIntegral.Dz s‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) :=
        add_le_add (by simpa using norm_add_le (s - 1) 1) (norm_Dz_le hs)
    _ = (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) * ‖s - 1‖ := by field_simp

end Formalism.ZF
