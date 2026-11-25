module

import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivationFinsetSumApply
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GlOperatorPreservesMultidegree
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem monomial_shift_cancel {σ : Type} (m : σ →₀ ℕ) (v : σ) (c : K) :
    (monomial (m - Finsupp.single v 1 + Finsupp.single v 1) (c * (m v : K)) : MvPolynomial σ K) =
      monomial m (c * (m v : K)) := by
  by_cases h : m v = 0
  · simp [h]
  · rw [tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]
    omega

theorem diagonal_derivation_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : K) * c) := by
  rw [gl_derivation_monomial]
  simp only [monomial_shift_cancel]
  unfold wtS

  rw [Int.cast_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_comm]

theorem diagonal_derivation_coeff (LL : Letters ι) (S : Set ι) (a : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glDerivation K LL S a a F) m = ((wtS LL S m a : ℤ) : K) * AddMonoidAlgebra.coeff F m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [diagonal_derivation_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, mul_add]

theorem polynomial_mem_weightSpace_iff (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K) :
    F ∈ weightSp (glOps K n LL S) mu ↔ ∀ a, glDerivation K LL S a a F = ((mu a : ℤ) : K) • F := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero, gl_operator_apply_derivation]
  rfl

theorem weight_vector_monomial_weight [CharZero K] (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ weightSp (glOps K n LL S) mu) (m : ι × Fin n →₀ ℕ) (hm : m ∈ F.support) : wtS LL S m = mu := by
  funext a
  have h := congrArg (AddMonoidAlgebra.coeff · m) ((polynomial_mem_weightSpace_iff LL S mu F).1 hF a)
  rw [diagonal_derivation_coeff, MvPolynomial.coeff_smul, smul_eq_mul] at h
  have hc : AddMonoidAlgebra.coeff F m ≠ 0 := mem_support_iff.1 hm
  have h2 := mul_right_cancel₀ hc h
  exact_mod_cast h2

theorem polynomial_isGLRep (LL : Letters ι) (S : Set ι) : IsGLRep (glOps K n LL S) := by
  apply _root_.Formalism.MainNotions.G.Joints.isGLRep_glOps <;> assumption

end Formalism.MainNotions.G.GLWeightTheory
