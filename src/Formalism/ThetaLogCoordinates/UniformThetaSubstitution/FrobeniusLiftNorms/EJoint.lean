module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Formalism.GaussJetBounds.Statement
import Formalism.GaussJetBounds.StatementH
public import Formalism.GaussJetBounds.StatementI

@[expose] public section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)

namespace MinorFormHomogeneity

theorem coeff_subst_scale {K ι : Type} [Field K] (ϖ : K) (Th : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      ϖ ^ n.degree * MvPowerSeries.coeff n Th := by
  have h : (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) =
      (fun _ : ι => ϖ) • (MvPowerSeries.X : ι → MvPowerSeries ι K) := by
    funext i
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

section Lin

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

end Lin

end MinorFormHomogeneity

end Formalism.InvariantFactorPaths.G7
