module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.Proof.LocalGlobalAssembly

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GlobalTheory.PtCore.GoodPtRow D := by
  intro D _ _ hZ a π hπ
  have hπ' : π ∈ ZgoodN D.nd D.naut a := (D.Zgood_tie a π).1 hπ
  obtain ⟨-, Sig, hX, hg⟩ := id hπ'
  have hHG : HG D.nd D.naut a := ⟨π, hπ'⟩
  have h1 := ((hZ a hHG).1 π hπ' Sig hX).2

  have hE : eigC D.nd D.naut a π ≠ ⊥ := by
    obtain ⟨P, hP, -⟩ := hX
    intro h
    apply D.naut.typeV_ne a P
    rw [eq_bot_iff, ← h]
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | D.naut.ptV a P = some π}) => D.naut.typeV a P) P hP le_rfl
  have hM : MjSig D.nd D.naut a Sig ≠ ⊥ := by
    intro h
    apply hE
    rw [← h1, h, Submodule.map_bot]
  obtain ⟨σ, hW, hσ⟩ : ∃ σ, HasParamW D.nd D.naut a σ Sig ∧ D.what₂.isot (D.nd.j a) σ ≠ ⊥ := by
    by_contra! hc
    apply hM
    unfold MjSig
    exact le_bot_iff.1 (iSup₂_le fun σ hW => (hc σ hW).le)
  have hgr : D.nd.goodRow σ := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW.2.2).2 hg
  exact ⟨σ, Sig, ⟨hgr, hσ⟩, hW, hX⟩

end GlobalTheory.Proof.LocalGlobalAssembly
