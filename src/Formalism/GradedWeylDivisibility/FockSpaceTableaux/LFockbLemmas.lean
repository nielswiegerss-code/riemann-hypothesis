module

public import Formalism.RealPlaceAnalysis.FockPairGl
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

@[expose] public section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open Formalism.REAL (fockF)

lemma LFockb_fockF_self {σ : Type*} (f : MvPolynomial σ ℂ) :
    fockF f f = ((∑ m ∈ f.support, Complex.normSq (f.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, mul_comm (starRingEnd ℂ _)]
  push_cast
  rfl

end Formalism.GradedWeylDivisibility
