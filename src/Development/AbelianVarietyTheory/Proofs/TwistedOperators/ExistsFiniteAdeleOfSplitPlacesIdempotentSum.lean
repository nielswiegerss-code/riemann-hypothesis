module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical

namespace GlobalTheory.IdemSumFinAdele

theorem exists_finAdele_of_idemSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  intro D P e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, hz⟩ := he
  have hex : ∀ PP ∈ P, ∃ α : Af D.host.F,
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = es PP + cA D (es PP) ∧
      evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) α = 1 ∧
      ∀ v', v' ≠ HeightOneSpectrum.under (𝓞 D.host.F) PP → evalV D.host.F v' α = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v ε (hes PP hPP) hε a3
    obtain ⟨α, rfl, h1, h2⟩ := hε
    exact ⟨α, a3.symm, hv ▸ h1, hv ▸ h2⟩
  choose! α hα using hex
  have hsum : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (∑ PP ∈ P, α PP)) =
      ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) := by
    have hp : pairA D.host.F 0 (∑ PP ∈ P, α PP) = ∑ PP ∈ P, pairA D.host.F 0 (α PP) := by
      have hadd : ∀ a b : Af D.host.F, pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
        fun a b => Prod.ext (add_zero 0).symm rfl
      exact map_sum (AddMonoidHom.mk' (pairA D.host.F 0) hadd) α P

    rw [hp, map_sum, map_sum (cA D), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun PP hPP => (hα PP hPP).1
  refine ⟨∑ PP ∈ P, α PP, hsum, ?_, ?_⟩
  · intro w hw

    rw [map_sum]
    exact Finset.sum_eq_zero fun PP hPP => (hα PP hPP).2.2 w (hw PP hPP).symm
  · intro PP hPP
    have h1 := GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one P _ he' PP hPP
    rw [← hsum] at h1
    have h2 : (evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) (∑ PP ∈ P, α PP)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Fv D.host.F _ ⊗[D.host.F] D.host.E) := h1
    haveI : Module.Free D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Flat D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) := Module.Flat.of_free
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
      (A := Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply, h2]
    rfl

end GlobalTheory.IdemSumFinAdele
