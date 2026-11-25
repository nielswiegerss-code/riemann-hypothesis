module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

@[expose] public section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem countable_numberField : Countable F :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

theorem separableSpace_Fv : TopologicalSpace.SeparableSpace (Fv F v) := by
  have := countable_numberField F
  exact ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  have := separableSpace_Fv F v
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))

theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  have : {r : Fv F v | IsUnit r} = {r | r ≠ 0} := by
    ext r
    simp [isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne

end Local

end PI.VolStabSW
