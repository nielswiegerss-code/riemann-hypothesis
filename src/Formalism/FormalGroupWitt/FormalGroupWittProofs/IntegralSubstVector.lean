module

public import Formalism.FormalGroupWitt.SubstInjectiveV
import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv

@[expose] public section

universe u v w

namespace Formalism.FG.IntegralSubstitution

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem integral_finsuppProd {ι : Type v} (a : ι → MvPowerSeries τ K) (ha : ∀ i, IntegralMv (a i))
    (n : ι →₀ ℕ) : IntegralMv (n.prod fun s e => (a s) ^ e) := by
  classical
  unfold Finsupp.prod
  exact Finset.prod_induction _ (fun x => IntegralMv x)
    (fun _ _ hx hy => Formalism.ELL.SubstitutionCoefficientCongruence.integral_mul hx hy)
    Formalism.ELL.SubstitutionCoefficientCongruence.integral_one
    (fun i _ => Formalism.ELL.SubstitutionCoefficientCongruence.integral_pow (ha i) _)

theorem integralSubstV {ι : Type v} [Finite ι] (g : MvPowerSeries ι K)
    (a : ι → MvPowerSeries τ K) (hg : IntegralMv g)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntegralMv (a i)) :
    IntegralMv (MvPowerSeries.subst a g) := by
  intro d
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst hs g d]
  have hfin := MvPowerSeries.coeff_subst_finite hs g d
  rw [finsum_eq_sum _ hfin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hg n) (norm_nonneg _) (integral_finsuppProd a ha n d)

end Formalism.FG.IntegralSubstitution

theorem Formalism.FG.integral_subst_vector : Formalism.FG.IntegralSubstV.{u, v, w} :=
  fun _ _ _ _ _ _ g a hg ha0 ha => Formalism.FG.IntegralSubstitution.integralSubstV g a hg ha0 ha
