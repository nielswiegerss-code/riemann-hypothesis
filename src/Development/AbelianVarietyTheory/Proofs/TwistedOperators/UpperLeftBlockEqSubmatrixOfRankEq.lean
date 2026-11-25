module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeometricConstantEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LevelGroupLifts

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix

namespace GlobalTheory.GeoActRoad

section Lattice

variable {D : D7} {V : HSp D}

variable {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

theorem le_of_half {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {Pg : Finset (Pl D.host.E)}
    (h : l.Mb = ∏ w ∈ Pg, w.asIdeal) {w : Pl D.host.E} (hw : w ∈ Pg) : l.Mb ≤ w.asIdeal :=
  h.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hw))

end Lattice

section Group

variable {D : D7} {V : HSp D} (β : GL (Fin V.rank) (EAf D))

variable {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem liftsExist_of_half (hβ : IsSDFrame V β Λ 1) (l : Level H) (L : LevDat D.host.E ℂ V.rank) (hQ : L.Q = ∅)
    (h : l.Mb = ∏ w ∈ L.Pg, w.asIdeal) : LiftsExist V β L := by
  obtain ⟨c, hc⟩ := hβ
  refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h1 PP' h' => ?_) (hQ ▸ Finset.disjoint_empty_right _)
  rcases h' with h' | h'
  · exact GlobalTheory.LevelAction.not_isConjPl l (le_of_half h h1) (le_of_half h h')
  · exact absurd (hQ ▸ h') (Finset.notMem_empty _)

end Group

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Classical in
theorem exists_half_prod {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (hM : l.M = D.host.g 0 * D.host.g 1) :
    (∀ Pg : Finset (Pl D.host.E), (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb = ∏ w ∈ Pg, w.asIdeal) ∧
      ∃ Pg : Finset (Pl D.host.E), l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  have hprod := l.prod
  rw [hM] at hprod
  have hs : Squarefree l.Mb := (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (l.Mb * _)).of_mul_left
  refine ⟨fun Pg h => GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ h,
    (Ideal.finite_factors hs.ne_zero).toFinset, GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]

theorem mem_Pg_iff {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (w : Pl D.host.E) :
    w ∈ L.Pg ↔ (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb ≤ w.asIdeal := by
  rw [hL.Pg, GlobalTheory.HalfOnRecord.designLevel_Mb, GlobalTheory.CoverHalf.prod_map_le_iff]
  rfl

theorem designLevel_prod {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) :
    (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb = ∏ w ∈ L.Pg, w.asIdeal :=
  (exists_half_prod _ rfl).1 _ (mem_Pg_iff hL)

theorem levelLiftsExist_gridVertexSpaces {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) :
    LiftsExist (Wc D i) (L.βW i) (L.datWp i L.triv) :=
  liftsExist_of_half (hL.βW i) (GlobalTheory.HalfOnRecord.designLevel L.C.P) _ rfl (designLevel_prod hL)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end Record

end GlobalTheory.GeoActRoad
