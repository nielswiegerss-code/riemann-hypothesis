module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem θ_σA_ev (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev r s hr.symm]
  apply Subtype.ext
  rw [GlobalTheory.RingIface.sigO_coe]
  change Per.σC (g : GQ l) (((r : ↥K.1) : Om l) : ℂ_[l]) = (((r : ↥K.1) : Om l) : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2]

theorem dvd_σA_ev_sub (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev bk.E ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, map_sub, θ_σA_ev, sub_self]

theorem exists_dvd_bound (u : OC l) (hu : u ≠ 0) : ∃ a : ℕ, ∀ (x y : OC l) (n : ℕ),
    x * u = (l : OC l) ^ n * y → a ≤ n → ∃ y' : OC l, x = (l : OC l) ^ (n - a) * y' := by
  have hu' : 0 < ‖(u : ℂ_[l])‖ := norm_pos_iff.2 (fun h => hu (Subtype.ext h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ‖(l : ℂ_[l])‖ ^ a < ‖(u : ℂ_[l])‖ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) GlobalTheory.RingBasics.norm_p_lt).eventually
      (gt_mem_nhds hu')).exists
  refine ⟨a, fun x y n h han => ?_⟩
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hy : ‖(y : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 y.2
  have h1 : ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ := by
    have := congrArg (fun t : OC l => ‖(t : ℂ_[l])‖) h
    simpa [norm_mul, norm_pow] using this
  have hn : ‖(l : ℂ_[l])‖ ^ n = ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel han]
  have hx : ‖(x : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := by
    have hpa : 0 < ‖(l : ℂ_[l])‖ ^ a := pow_pos hl0 a
    have hpn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := pow_nonneg hl0.le _
    by_contra! hc
    have : ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a < ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ :=
      mul_lt_mul'' hc ha hpn hpa.le
    have h2 : ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := mul_le_of_le_one_right (pow_nonneg hl0.le n) hy
    linarith
  have hm := (GlobalTheory.RingBasics.mem_span_pow_OC (n - a) x).2 hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, by rw [← hb, mul_comm]⟩

end GlobalTheory.BKLim.BetaBd
