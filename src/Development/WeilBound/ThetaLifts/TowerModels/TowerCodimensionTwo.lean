module

public import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneSkew
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

end PositivityTheory.ThKG.Tow
