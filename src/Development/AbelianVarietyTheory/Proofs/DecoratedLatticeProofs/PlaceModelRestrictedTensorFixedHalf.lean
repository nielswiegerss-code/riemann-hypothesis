module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunction
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotentsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl.PutIn.Factor

variable {D : D7}

theorem isSBHalf_of_half_eq {S T : HSp D} {b : AE D} {Λ Λ' : AddSubgroup (WO S T)} {Ψ : WO S T → ℂ}
    (hΛ : ∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) (hΨ : IsSBHalf b Λ' Ψ) : IsSBHalf b Λ Ψ := by
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := hΨ
  refine ⟨hsupp, k, hk, fun u hu hub t => hinv u ((hΛ u hub).2 hu) hub t, fun t ht => ?_⟩
  exact (hΛ _ (_root_.GlobalTheory.SplitScalar.isHalf_nsmul (hsupp t ht) k)).1 (hfin t ht)

theorem half_smul_self {m n : ℕ} {b : AE D} {x : Mx D m n} (hx : IsHalf b x) : b • x = x := by
  ext i j; exact hx i j

theorem half_of_idem {m n : ℕ} {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem isSBHalf_tens {S T : HSp D} {a b : AE D} {Λ : AddSubgroup (WO S T)} {Φ Ψ : WO S T → ℂ}
    (hab : a * b = 0) (hb : b * b = b) (hbΛ : ∀ u ∈ Λ, b • u ∈ Λ) (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) :
    IsSBHalf (a + b) Λ (tens b Φ Ψ) := by
  apply _root_.GlobalTheory.FinPl.PutIn.isSBHalf_tens <;> assumption


open GlobalTheory.LocMod.TensorModel in
theorem isPlaceModel_tensR : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  intro D ψ S T a b Λ Λ' Φ f₀ Tm hab hb hbΛ hΛ hΦ hP
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => Ψ (t + x)) = fun t => tens b Φ Ψ (t + x) := by
      funext t
      simp only [tens_apply]
      rw [smul_add, half_smul_self hx, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.trans _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') x (half_sum hab hx)
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
      funext t
      simp only [tens_apply]
      by_cases h0 : Φ (t - b • t) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
          rw [← GlobalTheory.LatVac.symplO_add_left, sub_add_cancel]
        rw [e1, symplO_half_zero hab (hΦ.1 _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.modul _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') y (half_sum_cA hab hy)
  · have hind : halfInd b Λ' = halfInd b Λ := by
      funext t
      unfold halfInd
      have hiff : (t ∈ Λ' ∧ IsHalf b t) ↔ (t ∈ Λ ∧ IsHalf b t) :=
        ⟨fun h => ⟨(hΛ t h.2).1 h.1, h.2⟩, fun h => ⟨(hΛ t h.2).2 h.1, h.2⟩⟩
      by_cases h : t ∈ Λ ∧ IsHalf b t
      · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
      · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h]
    rw [one_smul, hind]
    rfl

end GlobalTheory.FinPl.PutIn.Factor
