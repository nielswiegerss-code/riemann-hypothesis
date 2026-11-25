module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitOA

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem valuation_eq_exp (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    v.valuation L (k : L) = WithZero.exp (-ordF v k) := by
  rw [ordF, neg_neg, WithZero.exp_log]
  exact (Valuation.ne_zero_iff _).mpr k.ne_zero

theorem toNNReal_exp {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  first
    | (simp [WithZero.exp]; done)
    | rfl

theorem prod_norm_emb (x : L) : ∏ φ : L →+* ℂ, ‖φ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.I2.so_prod_norm <;> assumption

theorem finprod_norm_embedding (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, v ∉ T → ordF v k = 0) :
    ∏ᶠ w : FinitePlace L, w (k : L) =
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  have hval : ∀ v : HeightOneSpectrum (𝓞 L),
      (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
    intro v
    have e1 : (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) =
        NumberField.HeightOneSpectrum.adicAbv L v (k : L) := by
      first
        | (show (FinitePlace.mk v) (k : L) = _
           rw [FinitePlace.mk_apply, FinitePlace.norm_embedding])
    rw [e1, NumberField.HeightOneSpectrum.adicAbv_def, valuation_eq_exp, toNNReal_exp]
    push_cast
    rw [zpow_neg]
  rw [finprod_congr hval]
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hT'
  exact hv (by simp [hT v hT'])

theorem prodNorm : ProdNorm L := by
  intro k T hT
  have h3 := FinitePlace.prod_eq_inv_abs_norm (K := L) k.ne_zero
  rw [finprod_norm_embedding k T hT, Finset.prod_inv_distrib, Rat.cast_inv, Rat.cast_abs, inv_inj] at h3
  rw [prod_norm_emb, h3]

end PI.AlgValsFin.W
