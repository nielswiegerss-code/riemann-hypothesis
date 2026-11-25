module

public import Formalism.GradedWeylDivisibility.StatementB
import Formalism.FockPairing

@[expose] public section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

lemma lfockq_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) :=
  FockPairing.pair_eq_sum f g s h

lemma lfockq_symm (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f :=
  FockPairing.pair_comm f g

lemma lfockq_self_pos (f : MvPolynomial σ ℚ) (hf : f ≠ 0) : 0 < fockQ f f := by
  unfold fockQ
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hf (MvPolynomial.support_eq_empty.mp he)
  refine Finset.sum_pos (fun m hm => ?_) hne
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hw : (0 : ℚ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Finset.prod_pos (fun k _ => Nat.factorial_pos _))
  exact mul_pos (mul_self_pos.mpr hc) hw

lemma lfockq_add_left (f f' g : MvPolynomial σ ℚ) :
    fockQ (f + f') g = fockQ f g + fockQ f' g :=
  FockPairing.pair_add_left f f' g

lemma lfockq_smul_left (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ (c • f) g = c * fockQ f g :=
  FockPairing.pair_smul_left c f g

end general

end Formalism.GradedWeylDivisibility
