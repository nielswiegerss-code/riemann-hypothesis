module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion

open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_fd (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by
  apply ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable.fd_exists <;> assumption

lemma integral_swap_of_bdd {m n : Type} [Fintype m] [Fintype n] {D : Set (m → ℝ)} {K : Set (n → ℝ)}
    (hD : volume D < ⊤) (hK : volume K < ⊤) {f : (m → ℝ) → (n → ℝ) → ℂ}
    (hf : Continuous (Function.uncurry f)) {M : ℝ} (hM : ∀ s t, ‖f s t‖ ≤ M) :
    ∫ s in D, ∫ t in K, f s t = ∫ t in K, ∫ s in D, f s t := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hD.ne
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.ne
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)

end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
