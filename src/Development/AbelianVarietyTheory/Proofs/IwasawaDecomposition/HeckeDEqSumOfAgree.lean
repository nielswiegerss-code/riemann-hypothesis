module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

open scoped ValuativeRel

namespace GlobalTheory.HeckeEigConj

theorem proj_conjSplit {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    (GlobalTheory.HeckeFrob.conjSplit s).proj z = s.proj (conjAL L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    simp only [SplitPlace.proj, conjAL, GlobalTheory.HeckeFrob.conjSplit, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]; rfl

theorem map_loc_conjSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) {K' : Type}
    [Field K'] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* K') (x : GAf L n) :
    Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x) =
      GlobalTheory.LFun.ConjPlace.invT i n (s.loc n x) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]
  have h := congrFun₂ (GlobalTheory.FinTypCount.inv_val x) b a
  change i ((GlobalTheory.HeckeFrob.conjSplit s).proj _) = i (s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix _ _ _) b a))
  rw [h, proj_conjSplit]
  rfl

theorem KO_eq_KGL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := by
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff]
  have h : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (Valuation.mem_integer_iff _ _).trans (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w x)
  simp only [h]

theorem heckeD_eq_sum_of_agree {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have hmem : ∀ x ∈ D, ∀ y ∈ D, (x⁻¹ * y ∈ J ↔ x⁻¹ * y ∈ Umax L n) := fun x hx y hy =>
    hJ _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy))
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dite_eq_left hc]
    have hu : γ⁻¹ * hc.choose ∈ Umax L n :=
      (hmem γ (h1 γ hγ) _ hc.choose_spec.1).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD γ (h1 γ hγ)))
      (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hmem γ (h1 γ hγ) δ (h1 δ hδ)).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hmem γ (h1 γ hγ) x hx).2 e)⟩)
    · exact absurd (dite_eq_right h) hc

theorem norms_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    Formalism.UG.qV L (GlobalTheory.HeckeFrob.conjSplit s).w = normV (GlobalTheory.HeckeFrob.conjSplit s).w ∧
      s.q = normV (GlobalTheory.HeckeFrob.conjSplit s).w := by
  refine ⟨?_, ?_⟩
  · rw [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]
  · rw [normV, (GlobalTheory.HeckeFrob.conjSplit s).card_quot]
    rfl

end GlobalTheory.HeckeEigConj
