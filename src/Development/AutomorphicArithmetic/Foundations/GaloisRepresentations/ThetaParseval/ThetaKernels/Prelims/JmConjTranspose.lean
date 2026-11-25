module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
public import Mathlib.RingTheory.MvPolynomial
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.IsAdaptedFrame
/-! # JmConjTranspose: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge

namespace GlobalTheory.FockBottom

section Alg

variable {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]

theorem isExp_eig {L U : Module.End ℂ V} (hU : IsExp L U) (q : V →ₗ[ℂ] Z) (L0 : Module.End ℂ Z)
    (h : ∀ v, q (L v) = L0 (q v)) {T : V} {μ : ℂ} (hT : L0 (q T) = μ • q T) : q (U T) = Complex.exp μ • q T := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  rw [map_sub, sub_eq_zero, map_smul, smul_eq_mul]
  have hp : ∀ n : ℕ, q ((L ^ n) T) = μ ^ n • q T := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, hT, smul_smul, pow_succ]
  have a := hU T (l ∘ₗ q)
  simp only [LinearMap.comp_apply, hp, map_smul, smul_eq_mul] at a
  have b := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).mul_right (l (q T))
  rw [← Complex.exp_eq_exp_ℂ] at b
  simp only [smul_eq_mul, mul_assoc] at b
  exact a.unique b

end Alg

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d}

variable {B : Base F E} {om : Rep σ Y W} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
  {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)} {c : InfinitePlace F → ℂ}

theorem acts_unique {T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ} {f f₁ f₂ : SInf F (Fin n × Fin d)}
    (h₁ : Acts (evI F) T f f₁) (h₂ : Acts (evI F) T f f₂) : f₁ = f₂ :=
  (Main.i_actslaws F _ f f₁ f₂).2.2.2.1 T h₁ h₂

end Tens

end GlobalTheory.FockBottom
