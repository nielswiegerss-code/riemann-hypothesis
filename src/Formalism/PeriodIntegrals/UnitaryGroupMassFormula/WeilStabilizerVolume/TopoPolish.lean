module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

@[expose] public section

namespace PI.VolStabW.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  exact PI.VolStabS.TopoPolish.polish_of_lcsc Y

end PI.VolStabW.TopoPolish
