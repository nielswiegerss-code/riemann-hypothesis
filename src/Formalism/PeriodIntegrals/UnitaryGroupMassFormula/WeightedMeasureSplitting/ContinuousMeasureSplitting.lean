module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

@[expose] public section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct

theorem continuous_haMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [CommRing R'] [Algebra F R']
    [TopologicalSpace R'] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (φ : R →ₐ[F] R')
    (hφ : Continuous (tensMap (E := E) φ)) : Continuous (haMap σ J φ) := by
  apply _root_.MassDataMassesW.SplitW.continuous_haMap <;> assumption

theorem continuous_measure_splitting : ContSplit := by
  intro F E _ _ _ _ _ σ n J _
  have : FiniteDimensional F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact (continuous_haMap σ J (fstA F)
      (continuous_tensMap (AF F) (fstA F) continuous_fstA)).prodMk
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) (sndA F) continuous_sndA))

end PI.UnitaryGroupMassFormula.MeasWCore
