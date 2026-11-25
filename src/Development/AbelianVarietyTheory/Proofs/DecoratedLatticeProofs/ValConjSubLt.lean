module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair

namespace GlobalTheory.SeeSaw.LevChi

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar colPos superSum)
open GlobalTheory.SymBridge

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP)
include h

theorem val_rat_lt {y : D.host.E} (hy : PP.valuation D.host.E y < 1) : valuation K (q.pr (incA D y)) < 1 := by
  obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy.le
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (LevelTest.val_le_one q _) (not_lt.1 fun h' => d.2 ((LevelTest.val_lt_one_iff q h _).1 h'))
  have hr : r ∈ PP.asIdeal := by
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).1 ?_
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1
    rw [← e, map_mul]
    exact (mul_le_of_le_one_right' (PP.valuation_le_one _)).trans_lt hy
  have := (LevelTest.val_lt_one_iff q h r).2 hr
  rwa [show (r : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this



theorem val_pr_lt {z : AE D} (hz : Valued.v (adAt D.host.F PP (toEAf D z)) < 1) : valuation K (q.pr z) < 1 := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : PP.valuation D.host.E y < 1 := by
    rw [← valued_algebraMap, ← adAt_inclE D.host.F, ← sub_eq_iff_eq_add.2 e, map_sub]
    exact Valuation.map_sub_lt _ hz (valued_nat_mul_lt hr hN')
  have hnat : ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → valuation K (M : K) < 1 := fun M hM => by
    simpa using (LevelTest.val_lt_one_iff q h _).2 hM
  let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  have hf : finPart D (z - incA D y) = (N : Af D.host.F ⊗[D.host.F] D.host.E) * sw.symm r := by
    apply sw.injective
    rw [map_mul, map_natCast, AlgEquiv.apply_symm_apply]
    show toEAf D (z - incA D y) = _
    rw [RingHom.map_sub, e]
    exact add_sub_cancel_left _ _
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q (Ideal.absNorm PP.asIdeal)
        (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)) _ 0 (zero_mem _) ?_).trans_lt
        (hnat _ (Ideal.absNorm_mem _))
      rw [hf, Nat.cast_zero, zero_mul, mul_zero]
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q N hpos _ _ ((GlobalTheory.IdemSupport.mem_intAE_iff _).2 ?_) hf).trans_lt (hnat _ ?_)
      · exact (show Lev.swapAE D (sw.symm r) = r from sw.apply_symm_apply r).symm ▸ hr
      · rw [LevRead.valued_natCast] at hN'
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 hN'
  have h3 := (valuation K).map_add_lt h2 (val_rat_lt q h h1)
  rwa [← map_add, sub_add_cancel] at h3

end Split

end GlobalTheory.SeeSaw.LevChi
