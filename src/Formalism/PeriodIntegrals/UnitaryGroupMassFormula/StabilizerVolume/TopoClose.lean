module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasOrbSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

@[expose] public section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem lcscPolish_holds : LCSCPolish := fun Y _ _ _ _ => TopoPolish.polish_of_lcsc Y

theorem secCtblW_holds : SecCtblW := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem scha_holds : SCHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem measGrp_holds : MeasGrp := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ⟨inferInstance, inferInstance⟩

end PI.VolStabS
