module

public import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import CompanionTheory.AutomorphicTheory.ThetaDilations.OrbitAdelic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  exact CompanionTheory.PlacePermOperatorBicommutantSpan.oh_nat N

end PositivityTheory.PlacePermOperatorBicommutantSpan
