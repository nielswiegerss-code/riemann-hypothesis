module

import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
public import Formalism.EllipticTorsion.Statement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar

@[expose] public section

open PowerSeries

namespace Formalism.ELL.SubstitutionCoefficientCongruence

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_subst_congr_lemma {R : Type*} [CommRing R] {σ : Type*}
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (n : ℕ) :
    ∀ e : σ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (a ^ n) = 0 := by
  classical
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : x.2 = 0
    · have h0 : MvPowerSeries.coeff 0 a = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
      rw [h2, h0, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
      have hsum : x.1.degree + x.2.degree = e.degree := by rw [← map_add (f := _), hx]
      have h1 : x.1.degree < n := by omega
      rw [ih x.1 h1, zero_mul]

end Chain

section Integral

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

theorem mem_unitBall {x : K} : x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem integral_one : Formalism.G.IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_mul {F G : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F)
    (hG : Formalism.G.IntegralMv G) : Formalism.G.IntegralMv (F * G) := by
  classical
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ =>
    Subring.mul_mem _ (mem_unitBall.2 (hF _)) (mem_unitBall.2 (hG _))

theorem integral_pow {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (n : ℕ) :
    Formalism.G.IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hF

theorem integral_subst {c : PowerSeries K} (hc : ∀ n, ‖coeff n c‖ ≤ 1)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : Formalism.G.IntegralMv f) : Formalism.G.IntegralMv (c.subst f) := by
  classical
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf0
  intro e
  rw [← mem_unitBall, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1)) ?_]
  · exact Subring.sum_mem _ fun d _ => by
      rw [smul_eq_mul]
      exact Subring.mul_mem _ (mem_unitBall.2 (hc d)) (mem_unitBall.2 (integral_pow hf d e))
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [coeff_subst_congr_lemma hf0 d e (by omega), smul_zero])

end Integral

end Formalism.ELL.SubstitutionCoefficientCongruence

namespace Formalism.ELL

end Formalism.ELL
