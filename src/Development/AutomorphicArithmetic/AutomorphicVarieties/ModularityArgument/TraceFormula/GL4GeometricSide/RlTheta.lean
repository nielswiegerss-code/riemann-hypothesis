module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ContOfRightInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EopWMemStabAlg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
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
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution

@[expose] public section

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TwY.ThInv
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem along_unitary (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (k : Un n) :
    Bridge.along w g φ k.1 = φ (g * kAt w k) := by
  apply _root_.UpperTheory.V.Z.GSp4Splitting.along_unit <;> assumption

private theorem eop_theta (w : InfinitePlace E) (a b : Fin n) {φ φ' : Sm E n}
    (h : ∀ x, φ'.1 x = φ.1 (thetaA E n x)) (x : GA E n) :
    (Bridge.eopW w true a b φ).1 (thetaA E n x) = -(Bridge.eopW w false b a φ').1 x := by
  open Matrix in
  let adjH : Lie E n →L[ℝ] Lie E n :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => toL (Matrix.of X)ᴴ
        map_add' := fun X Y => by
          rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
        map_smul' := fun t X => by
          rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

  have adjH_apply (X : Lie E n) (i j : Fin n) : adjH X i j = star (X j i) := rfl

  have toL_thetaR (y : GL (Fin n) (Cinf E)) :
      toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
    rw [thetaR_val]
    ext i j : 2
    change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
    rw [Matrix.coe_units_inv]
    rfl

  have chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
      chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

  have lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
      lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
    have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
        chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
      Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
    have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
      (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
    have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
      (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
      (adjH.hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
    unfold lieD
    rw [e.fderiv_eq, h2.fderiv]
    simp


  have atEmb_conjugate (w : InfinitePlace E) (z : ℂ) :
      atEmb (ComplexEmbedding.conjugate w.embedding) z = atEmb w.embedding (conj z) := by
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
      (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
    unfold atEmb
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, ite_eq_right hne, ite_eq_left rfl]


  have star_atEmb (w : InfinitePlace E) (z : ℂ) : star (atEmb w.embedding z) = atEmb w.embedding (conj z) := by
    funext v
    simp only [atEmb, InfinitePlace.mk_embedding, ite_true, Pi.star_apply]
    by_cases hv : v = w
    · subst hv; simp
    · classical
      rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, star_zero]

  let sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : Lie E n := toL (Matrix.single a b (atEmb w.embedding z))

  have adjH_sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : adjH (sg w a b z) = sg w b a (conj z) := by
    funext i j
    rw [adjH_apply]
    change star (Matrix.single a b (atEmb w.embedding z) j i) = Matrix.single b a (atEmb w.embedding (conj z)) i j
    rw [Matrix.single_apply, Matrix.single_apply]
    by_cases h : a = j ∧ b = i
    · rw [ite_eq_left h, ite_eq_left h.symm, star_atEmb]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm, star_zero]

  have Eop_apply (τ : E →+* ℂ) (a b : Fin n) (φ : Sm E n) (g : GA E n) :
      (Eop τ a b φ).1 g = (1 / 2 : ℂ) * (lieD (toL (Matrix.single a b (atEmb τ 1))) φ.1 g -
        Complex.I * lieD (toL (Matrix.single a b (atEmb τ Complex.I))) φ.1 g) := rfl
  have e : φ'.1 = fun x => φ.1 (thetaA E n x) := funext h
  have e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y) := fun f y => by
    simp only [Bridge.eopW, ite_true]
    exact Eop_apply _ a b f y
  have e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y) := fun f y => by
    simp only [Bridge.eopW, Bool.false_eq_true, ite_false]
    rw [Eop_apply, atEmb_conjugate, atEmb_conjugate]
    simp [sg]
  rw [e1, e2, e]
  simp only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]
  ring

end

theorem rlTheta : RlTheta := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D
  have thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
    classical
    have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
    rw [e, thetaA_infGL]
    congr 1
    refine Units.ext ?_
    ext i j v
    rw [thetaR_val, ← map_inv, ← map_inv]
    change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
    rw [locInf_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, ite_true]
      change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
      simp [Matrix.star_apply]
    · simp only [hv, ite_false]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y := fun x y h =>
    D.inj (Subtype.ext (Subtype.ext (funext h)))
  refine ⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w =>
    ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩
  · change (D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g
    rw [D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · rw [D.inner_eq, D.inner_eq]
    exact D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)
  · change (D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g
    rw [D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]
  · change (D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g
    rw [D.hΘ, D.hE1, D.hE2]
    exact eop_theta w a b (D.hΘ u) g

end UpperTheory.V.Z.GSp4Splitting
