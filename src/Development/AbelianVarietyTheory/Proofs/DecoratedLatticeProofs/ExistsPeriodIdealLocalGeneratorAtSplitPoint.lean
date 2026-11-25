module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField

namespace GlobalTheory.FinPl.LocGen

theorem half_diff_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 :=
  _root_.GlobalTheory.LatVacFull.AA_ne_zero D

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_incA_int (q : SplitPt D k) (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E))) := (x.2).map ((q.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem exists_gen : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧
      ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  intro D k _ _ _ _ q
  classical
  set π : D.host.E →+* k := q.pr.comp (incA D) with hπ
  have hinj : Function.Injective π := π.injective
  have hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG :=
    FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]; simp
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun x => valuation k (π x)) hsne
  have hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := hs ▸ Submodule.subset_span hj
  have hj0 : π j ≠ 0 := by
    intro h0
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]
    intro i hi
    have h1 := hmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (h1.trans π.map_zero.symm)
  refine ⟨j, hjmem, hj0, ?_⟩
  intro a ha
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := hs.symm ▸ ha
  change π a / π j ∈ 𝒪[k]
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le'
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), add_div]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_div_assoc]
    exact mul_mem (pr_incA_int q r) hx

end GlobalTheory.FinPl.LocGen
