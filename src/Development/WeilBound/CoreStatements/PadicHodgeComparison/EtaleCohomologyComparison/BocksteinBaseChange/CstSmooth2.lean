module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfP
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SumCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

theorem cstSmooth_of_side (h : EtSideS) : CstSmooth := cstSmooth_of_p Pb.pSeam h

end CrystallineSemistableComparison
