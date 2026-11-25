module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMemLatVIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical



namespace GlobalTheory.SplitIntComp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

theorem eq_sec_add_csec (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := GlobalTheory.SplitLine.eq_sec_add_cA q ha

theorem mem_intAt_iff (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  apply _root_.GlobalTheory.SplitLine.mem_intAt_iff_pr <;> assumption

theorem val_xi (q : SplitPt D k) (h : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have he := e_mem_intAt q
  have hpe : q.pr q.e = 1 := by rw [← sec_one q, q.pr_sec]
  have h1 := ((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1
  have h2 := ((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1
  rw [map_mul, hpe, mul_one] at h1 h2
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 := congrArg (valuation k) hprod
  rw [map_mul, map_one] at v3
  refine le_antisymm v1 ?_
  by_contra! hlt
  have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one
  rw [v3, mul_one] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitIntComp
