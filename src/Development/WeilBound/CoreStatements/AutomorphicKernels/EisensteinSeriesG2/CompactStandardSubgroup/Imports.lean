module

import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace SiegelEisensteinSeries.BRoad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

end SiegelEisensteinSeries.BRoad
