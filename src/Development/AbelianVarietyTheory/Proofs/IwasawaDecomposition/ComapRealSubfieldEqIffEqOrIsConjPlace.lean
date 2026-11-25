module

public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.PlacePair

theorem hostConj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem cO_cO (D : D7) (x : 𝓞 D.host.E) :
    IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
  exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)

theorem cO_algebraMap (D : D7) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    IsCMField.ringOfIntegersComplexConj D.host.E
        (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a) =
      algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩

theorem isConjPl_iff (D : D7) (P P' : PlE D.host) :
    IsConjPl D.host P P' ↔
      ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ IsCMField.ringOfIntegersComplexConj D.host.E x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, hostConj_eq])
  · intro h x y hxy
    have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      rw [hxy, hostConj_eq, IsCMField.coe_ringOfIntegersComplexConj]
    rw [this]; exact h x

theorem eq_or_eq_conj (D : D7) (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w.asIdeal = P.asIdeal ∨
      w.asIdeal = P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  set Q : Ideal (𝓞 D.host.E) :=
    P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  by_contra! hne
  obtain ⟨h1, h2⟩ := hne
  have nle : ∀ I : Ideal (𝓞 D.host.E), I.IsPrime → w.asIdeal ≠ I → ¬ w.asIdeal ≤ I := fun I hI h hle =>
    h (w.isMaximal.eq_of_le hI.ne_top hle)
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle P.asIdeal P.isPrime h1)
  obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q hQp h2)
  have key : ∃ x ∈ w.asIdeal, x ∉ P.asIdeal ∧ x ∉ Q := by
    by_cases haQ : a ∈ Q
    · by_cases hbP : b ∈ P.asIdeal
      · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
        · simpa using P.asIdeal.sub_mem h hbP
        · simpa using Q.sub_mem h haQ
      · exact ⟨b, hb, hbP, hbQ⟩
    · exact ⟨a, ha, haP, haQ⟩
  obtain ⟨x, hx, hxP, hxQ⟩ := key
  have hxQ' : IsCMField.ringOfIntegersComplexConj D.host.E x ∉ P.asIdeal := hxQ
  have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
      x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
    rw [map_mul, cO_cO, mul_comm]
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
  have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
  rw [hw, Ideal.mem_comap, hy] at hyw
  rcases P.isPrime.mem_or_mem hyw with h | h
  · exact hxP h
  · exact hxQ' h

theorem comap_eq_iff : ∀ (D : D7) (P P' : PlE D.host),
    P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ↔
        (P = P' ∨ IsConjPl D.host P P') := by
  intro D P P'
  constructor
  · intro h
    rcases eq_or_eq_conj D P P' h.symm with e | e
    · exact Or.inl (HeightOneSpectrum.ext e.symm)
    · refine Or.inr ((isConjPl_iff D P P').2 fun x => ?_)
      rw [e, Ideal.mem_comap, RingHom.coe_coe, cO_cO]
  · rintro (rfl | h)
    · rfl
    · rw [isConjPl_iff] at h
      ext a
      rw [Ideal.mem_comap, Ideal.mem_comap, h, cO_algebraMap]

end GlobalTheory.PlacePair
