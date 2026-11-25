module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.FinPl.SplitHalfSuppImp

theorem mxAt_of_isHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) {m n : ℕ} (x : Mx D m n), IsHalf (q.e + cA D q.e) x → MxAt (· = q.v) x := by
  intro D k _ _ _ _ q m n x hx
  exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D k q m n x hx

end GlobalTheory.FinPl.SplitHalfSuppImp
