module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatIso

theorem heckeFunI_eq_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)) (h : GU Dv.σw n → ℂ)
    (hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0}) :
    ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
  classical
  refine ⟨hfin.toFinset,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      Dv.hval h (Dv.loc hc.choose) else 0,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      hc.choose else 1, fun W _ _ φ => ?_⟩
  funext g
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · simp only [dite_eq_left hc]
      rfl
    · simp only [dite_eq_right hc, zero_smul]
      rfl
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · rw [dite_eq_left hc] at hc0
      rw [Set.Finite.coe_toFinset]
      refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
      rw [h0, zero_smul]
    · exact absurd (dite_eq_right hc) hc0

theorem satAt_of_iso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n)
    (hiso : π.Iso π') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0})
    (hs : NG.SatAt π Dv α) : NG.SatAt π' Dv α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  obtain ⟨T, hT⟩ := hiso.2
  refine ⟨(T ⟨f, hfS⟩ : π'.S), (T ⟨f, hfS⟩).2, ?_, U, ?_, hUv, ?_⟩
  · intro h0
    have h1 : T ⟨f, hfS⟩ = 0 := Subtype.ext h0
    have h2 : (⟨f, hfS⟩ : π.S) = 0 := T.map_eq_zero_iff.mp h1
    exact hf0 (congrArg Subtype.val h2)
  · intro κ hκ
    exact (hT κ ⟨f, hfS⟩ ⟨f, hfS⟩ (hU κ hκ).symm).symm
  · intro h hh
    obtain ⟨C, a, x, hC⟩ := heckeFunI_eq_sum Dv U h (hfin U hUv h hh)
    have e := hH h hh
    rw [hC] at e
    rw [hC]
    have e1 : (∑ c ∈ C, a c • (⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ : π.S)) =
        SatU Dv.ϖ (qV (maximalRealSubfield L) v) h α • (⟨f, hfS⟩ : π.S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact e
    have e2 := congrArg (fun y => ((T y : π'.S) : GAf L n → π'.W)) e1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hT (x c) ⟨f, hfS⟩ ⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ rfl]

end GlobalTheory.SatIso
