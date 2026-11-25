module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop.Model

variable {D : D7}

theorem rec_iff (large₂ : SizeData₂ D) : Rec large₂ ↔ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ ∧ HostHyp D :=
  ⟨fun h => ⟨h.size, h.host⟩, fun h => ⟨h.1, h.2, rfl, h.1.2.1.2.2.2.2.2.2.1.2.2.2.2.2.1⟩⟩

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨c, h⟩ := h
  obtain ⟨c', h'⟩ := h'
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hL G,
      h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hL G⟩⟩

theorem tower_numbers (i j : Fin D.R.m) : e0 D i j + pp D j = eTop D i j + qq D j ∧
    halfRank D i j = h0 D i j + pp D j + qq D j ∧ pp D j + qq D j = D.R.m - 1 - j ∧ 1 ≤ e0 D i j ∧ e0 D i j < h0 D i j ∧
    botBig D i j = e0 D i j + h0 D i j ∧ botSmall D i j + e0 D i j = h0 D i j ∧ eTop D i j + qq D j ≤ halfRank D i j ∧
    halfRank D i j ≤ bigN D := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := odd_sLen D
  obtain ⟨a, ha⟩ := D.R.m_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have r2 := D.R.m_add_three_le_k
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have hj := j.2
  have b1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
  have b2 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
  have b3 : rankV D (i + 1) (j + 1) = D.R.r + (j.1 + 1) * D.R.t + (i.1 + 1) * sLen D := rfl
  have b4 : bigN D = D.R.k + (D.R.m * D.R.t + D.R.m * sLen D + D.R.m) := by simp only [bigN]; ring
  simp only [e0, h0, pp, qq, eTop]
  omega

variable {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}

theorem base_tuple (hL : Lc.Is μ₀) : twPl G μ₀ = ∅ ∧ Qn G μ₀ = 1 ∧ modT G μ₀ = SqNum.condE G.pl := by
  have h : twPl G μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    simp only [twPl, locPl, Finset.mem_filter, Finset.mem_union] at hw
    exact (hL.Q_ram μ₀ w).2 (Or.inl (hw.1.resolve_left hw.2)) (by rw [hL.xi_base]; intro x _; rfl)
  simp [Qn, modT, h]

theorem Qn_ne_zero (t : T) : Qn G t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot

end GlobalTheory.SqTop.Model
