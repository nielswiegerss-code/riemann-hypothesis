module

public import Formalism.PeriodIntegrals.UpqRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.DiscreteSeriesTest

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - a := by
  have h1 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => a < b) (fun b => ε b = ε a)
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a) (fun b => ε b = ε a)
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  have e1 : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have e2 : (univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  rw [e1, Fin.card_Ioi] at h1
  rw [e2, Fin.card_Iio] at h2
  have ha := a.isLt
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - a := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  have h1' := congrArg (Nat.cast : ℕ → ℝ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  rw [h3] at h1'
  push_cast at h1' h2'
  simp only [rhoN, rhoC, ne_eq]
  linarith

theorem lowK_add {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (((n : ℝ) - 1) / 2 - a) := by
  rw [← rhoN_add_rhoC ε a]
  simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem torus_mem {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, by simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

theorem wt_int {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h1 : σ 1 = 1) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  have h2 := h (Pi.single a (2 * Real.pi)) (torus_mem ε _)
  have e : (Matrix.diagonal fun b => Complex.exp (((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℂ) * Complex.I)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  rw [e, h1] at h2
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h2
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    apply smul_left_injective ℂ hv
    simpa using h2.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨m, ?_⟩
  have h4 := congrArg Complex.im hm
  simp at h4
  exact h4

end GlobalTheory.DiscreteSeriesTest
