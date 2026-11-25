module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

namespace GlobalTheory.LevProd.SamePlace

open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}

theorem half_mem (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    q.e • (Formalism.L2.Theta.mt V g *ᵥ y) ∈ latV V L (· = q.v) := by
  have he : finPart D q.e ∈ intAE D := by
    rw [← GlobalTheory.FinPl.LatIndHalf.sec_one]; exact (q.int_iff 1).1 (one_mem _)
  have h2 : (Formalism.L2.Theta.mt V g).map q.pr = F.β * (GlobalTheory.LevIdx.locHom q V F g).val * F.γ :=
    (GlobalTheory.LevIdx.eq_locHom_iff q V F g _).2 rfl
  have e : q.e • (Formalism.L2.Theta.mt V g *ᵥ y) =
      fun i => q.sec ((F.β *ᵥ ((GlobalTheory.LevIdx.locHom q V F g).val *ᵥ (F.γ *ᵥ fun j => q.pr (y j)))) i) := by
    funext i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h2, Pi.smul_apply, smul_eq_mul, ← q.sec_pr]
    exact congrArg q.sec (RingHom.map_mulVec q.pr _ y i)
  rw [e]
  refine (hL _).1 (GlobalTheory.LocGl.mulVec_int ((GlobalTheory.LocGl.mem_KO_iff _).1 hg).1 ((hL _).2 ?_))
  rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  simpa only [q.sec_pr] using GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he hy

theorem act_mem (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    Formalism.L2.Theta.mt V g *ᵥ y ∈ latV V L (· = q.v) := by
  obtain ⟨s1, -, s2⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L q.v hsd
  have hs := GlobalTheory.IwaPlace.mulVec_mem_idAt (Formalism.L2.Theta.mt V g) (s1 y hy)
  have e : Formalism.L2.Theta.mt V g *ᵥ y =
      q.e • (Formalism.L2.Theta.mt V g *ᵥ y) + cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y) := by
    rw [← add_smul, GlobalTheory.LocGl.idem_eq]
    exact funext fun i => ((GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hs i)).symm
  have hg' : GlobalTheory.LevIdx.locHom q V F g⁻¹ ∈ KO k Y := by rw [map_inv]; exact inv_mem hg
  rw [e]
  refine add_mem (half_mem q F hL hg hy) ((s2 _ fun i => Ideal.mul_mem_left _ _ (hs i)).2 fun x hx => ?_)
  have e2 : q.e • x = Formalism.L2.Theta.mt V g *ᵥ (q.e • (Formalism.L2.Theta.mt V g⁻¹ *ᵥ x)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, mul_inv_cancel,
      GlobalTheory.MixModel.mt_one, Matrix.one_mulVec]
  change hermAt V (cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y)) x ∈ _
  rw [GlobalTheory.LocGl.hermAt_smul, e2, GlobalTheory.LocGl.hermAt_unitary]
  exact (s2 y (s1 y hy)).1 hy _ (half_mem q F hL hg' hx)

theorem moves_of_mem_KO (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V}
    (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y) : Moves V g L L (· = q.v) := by
  refine fun y _ => ⟨act_mem q F hsd hL hg, fun hy => ?_⟩
  have := act_mem q F hsd hL (g := g⁻¹) (by rw [map_inv]; exact inv_mem hg) hy
  rwa [Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mulVec] at this


end GlobalTheory.LevProd.SamePlace
