module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkExist

theorem star_smul_vec {D : D7} {n : ℕ} (k : D.host.E) (v : Fin n → D.host.E) : star (k • v) = star k • star v := by
  funext i
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']

theorem norm_smul_vec {D : D7} (L' : HSp D) (k : D.host.E) (v : Fin L'.rank → D.host.E) :
    star (k • v) ⬝ᵥ L'.gram *ᵥ (k • v) = star k * k * (star v ⬝ᵥ L'.gram *ᵥ v) := by
  rw [star_smul_vec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem link_of_norm : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (c : D.host.E), IsLineVec L' ζ' → star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = c * star c * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ') → IsLineVec L' ((c / D.host.xi0) • ζ') ∧ Nonempty (Link B L' ((c / D.host.xi0) • ζ')) := by
  intro D ρ B L' ζ' c hl hn
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN := B.line.2
  rw [hn] at hN
  have hc : c ≠ 0 := fun h => hN (by simp [h])
  have hv : star ζ' ⬝ᵥ L'.gram *ᵥ ζ' ≠ 0 := fun h => hN (by simp [h])
  have hk : c / D.host.xi0 ≠ 0 := div_ne_zero hc hxi
  have hsk : star (c / D.host.xi0) ≠ 0 := star_ne_zero.2 hk
  set x := (c / D.host.xi0) • ζ' with hx
  have hnx : star x ⬝ᵥ L'.gram *ᵥ x = star (c / D.host.xi0) * (c / D.host.xi0) * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ') :=
    norm_smul_vec L' _ ζ'
  have hn0 : star x ⬝ᵥ L'.gram *ᵥ x ≠ 0 := by
    rw [hnx]; exact mul_ne_zero (mul_ne_zero hsk hk) hv
  refine ⟨⟨hl.1, hn0⟩, ⟨{ τ := (-(star x ⬝ᵥ L'.gram *ᵥ x)⁻¹) • vecMulVec B.ζ (star x ᵥ* L'.gram), map := ?_, norm := ?_ }⟩⟩
  · rw [Matrix.smul_mulVec, vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, op_smul_eq_smul, smul_smul, neg_mul, inv_mul_cancel₀ hn0, neg_one_smul]
  · rw [hn, hnx]
    have hsx : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
    rw [star_div₀]
    field_simp

end GlobalTheory.Unf.LinkExist
