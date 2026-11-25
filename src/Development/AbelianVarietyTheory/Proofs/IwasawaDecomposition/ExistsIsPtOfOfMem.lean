module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Formalism.LocalToGlobal.Columns.AdelicLemmas
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix



namespace GlobalTheory.Mem.Col2.ChiFinTop

open GlobalTheory.Mem.Col2.PtExist

theorem exists_isPtOf_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅)
    {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  obtain ⟨p, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (by simp [hQ])⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [ite_eq_left (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [ite_eq_left (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)

end GlobalTheory.Mem.Col2.ChiFinTop
