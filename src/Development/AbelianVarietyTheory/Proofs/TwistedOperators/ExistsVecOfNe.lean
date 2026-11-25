module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.KapRedII

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem nP_pos' (F : Face D A) (b : Bool) : 0 < RealDat.nP F b := by
  exact Formalism.IndefR.Links.RealDat.nP_pos b

end Defs

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨hint, heq⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact hint.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, heq, ENNReal.toReal_ofReal ha, Complex.real_smul]
    ring

private theorem isMultIP_const_unique {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c c' : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0)
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have e := (h v v).2
  rw [(h' v v).2] at e
  exact (mul_right_cancel₀ hv e).symm

private theorem ipM_eq_of_isMultIP {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (h : IsMultIP M μ 𝓕 T T' c) :
    ipM M μ 𝓕 T T' = c := by
  have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
  unfold ipM
  rw [dite_eq_left hex]
  exact isMultIP_const_unique v hv hex.choose_spec h

theorem ipM_smul_of_vec (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {a : ℝ}
    (ha : 0 < a) (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  by_cases hex : ∃ c, IsMultIP M μ 𝓕 T T' c
  · obtain ⟨c, hc⟩ := hex
    rw [ipM_eq_of_isMultIP v hv hc, ipM_eq_of_isMultIP v hv (isMultiplicityInner_smul_measure ha.le hc)]
  ·
    have hex' : ¬ ∃ c, IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' c := by
      rintro ⟨c', hc'⟩
      have hb := isMultiplicityInner_smul_measure (inv_nonneg.mpr ha.le) hc'
      rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_smul] at hb
      exact hex ⟨_, hb⟩
    unfold ipM
    rw [dite_eq_right hex, dite_eq_right hex', mul_zero]

theorem exists_vec_of_ne {M : DSModel V S} {T : MMap M} (hT : T ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical

  obtain ⟨v, hv⟩ : ∃ v : M.Vec, T v ≠ 0 := by
    by_contra! hno
    exact hT (MultilinearMap.ext fun x => by simp [hno x])
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => ?_⟩
  have hvt : v τ ≠ 0 := fun h0 => hv (T.map_coord_zero τ h0)
  rw [inner_self_ne_zero, ne_eq, Submodule.coe_eq_zero]
  exact hvt

end Schur

end GlobalTheory.KapRedII
