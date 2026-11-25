module

public import Formalism.PeriodIntegrals.FglPtW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

variable {K : Type*} [CommRing K]

theorem serOver_iff (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    SerOver S f ↔ f ∈ SerS S σ := by
  constructor
  · intro h
    refine ⟨fun n => ⟨MvPowerSeries.coeff n f, h n⟩, ?_⟩
    ext n
    first
    | rfl
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

end PI.FglPtW.Wk
