module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting

namespace GlobalTheory.SplitTypeCompl

theorem exists_padic_equiv : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D →
    ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous i := by
  intro D s hs
  obtain ⟨w, hw, k, hk⟩ := hs
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by simpa [placesOver] using hk
  have hv : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
    rw [← hw, Ideal.mem_comap, map_natCast]; exact hwk
  have hsw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have := hv
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ hsw
  haveI : CharZero (s.w.adicCompletion D.host.E) :=
    charZero_of_injective_ringHom (algebraMap D.host.E _).injective
  obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic (s.w.adicCompletion D.host.E) (D.host.g k)
    ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans (by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1))
    (GlobalTheory.TypeIdent.irreducible_natCast_compl _ hsw h2)
  exact ⟨D.host.g k, inferInstance, φ, h⟩

end GlobalTheory.SplitTypeCompl
