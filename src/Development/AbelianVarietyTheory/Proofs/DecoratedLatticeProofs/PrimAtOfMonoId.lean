module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.SeeSaw.PrimSplit

variable {D : D7}

theorem pX_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    (d.pX *ᵥ colMul d.jX i a) i = a := by
  apply _root_.GlobalTheory.FinPl.RootKeep.pX_colMul_jX <;> assumption

theorem idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {P : Pl D → Prop} {i : Fin ρ} {a : AE D}
    (h : colMul d.jX i a ∈ latV S L P) : a ∈ idAt D P := by
  rw [← pX_colMul d i a]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt _ (GlobalTheory.FinPl.FrameLat.latV_supp h) i

end GlobalTheory.SeeSaw.PrimSplit
