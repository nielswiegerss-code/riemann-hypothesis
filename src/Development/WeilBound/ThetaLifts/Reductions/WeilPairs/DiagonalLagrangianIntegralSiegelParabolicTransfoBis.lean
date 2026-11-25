module

import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end PositivityTheory.ThKW.LagrangianIntegralFactorisation
