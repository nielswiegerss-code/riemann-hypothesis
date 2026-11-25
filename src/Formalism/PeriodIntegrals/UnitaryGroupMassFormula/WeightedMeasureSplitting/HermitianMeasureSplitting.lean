module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousHAIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MapSplitEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ProductDecompositionHolds

@[expose] public section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField

theorem hermitian_measure_splitting : SplitH := by
  intro F E _ _ _ _ _ σ n J r P T _ _ _
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact splitEquiv _ _ _ (splitA_injective σ J splT_bijective.1)
    (continuous_haMap σ J (fstA F) (continuous_tensMap (AF F) _ continuous_fstA))
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) _ continuous_sndA))
    (mem_Hsub_iff σ J splT_bijective.1 P)

theorem nilpotent_measure_splitting : SplitN := by
  intro F E _ _ _ _ _ σ n J r P T _ _ _
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact splitEquiv _ _ _ (splitA_injective σ J splT_bijective.1)
    (continuous_haMap σ J (fstA F) (continuous_tensMap (AF F) _ continuous_fstA))
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) _ continuous_sndA))
    (mem_Nsub_iff σ J splT_bijective P)

theorem measWCore_main : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  mwCore_of hermitian_measure_splitting nilpotent_measure_splitting continuous_measure_splitting product_decomposition_holds

end PI.UnitaryGroupMassFormula.MeasWCore
