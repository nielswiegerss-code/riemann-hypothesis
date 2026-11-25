module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

namespace PI.VolStabS.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  apply PI.AprimeInfA.polish_of_lcsc

end PI.VolStabS.TopoPolish
