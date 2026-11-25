module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical

open GlobalTheory.Tow

open scoped Topology

namespace GlobalTheory.VacTranslate

variable {D : D7}

theorem exists_finCong_mod (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (hV : IsSelfDualC V ΛV) (hW : IsSelfDualC W ΛW)
    (N : ℕ) (hN : 0 < N) :
    ∃ n : ℕ, ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V n.factorial k →
      ∀ x ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        ∃ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
          actO V W k 1 x = x + N • l := by
  by_contra! hne
  choose k hk hkc hkne using hne
  have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
  have ht2 : Filter.Tendsto (fun n => ((k n, (1 : GA D W)) : GA D V × GA D W)) Filter.atTop (𝓝 1) := by
    have := ht.prodMk_nhds (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : GA D W)) Filter.atTop (𝓝 1))
    rwa [Prod.mk_one_one] at this
  obtain ⟨n, hn⟩ := (ht2.eventually (GlobalTheory.Mem.CoefInv.eventually_mod ΛV ΛW hV hW N hN)).exists
  obtain ⟨x, hx, hxne⟩ := hkne n
  obtain ⟨l, hl, e⟩ := hn x hx
  exact hxne l hl e

theorem psi_four_eq_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hlat : ∀ u ∈ Λ, heisO ψ S T (2 • u) f = f) {w₀ : WO S T} (hw₀ : f w₀ ≠ 0) {a b : WO S T} (ha : a ∈ Λ)
    (hb : b ∈ Λ) : ψ (symplO S T ((2 * 2) • a) b) = 1 := by
  have h := GlobalTheory.SplitScalar.heisO_comm ψ S T (2 • a) (2 • b) f
  rw [hlat b hb, hlat a ha, hlat b hb] at h
  have h3 := congrFun h w₀
  rw [Pi.smul_apply, smul_eq_mul] at h3
  have h4 : ψ (symplO S T (2 • a) (2 • b)) = 1 :=
    mul_right_cancel₀ hw₀ (h3.symm.trans (one_mul _).symm)
  rwa [← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_smul] at h4

theorem lat_iff_of_mod {V W : HSp D} {L : AddSubgroup (WO V W)} {n : ℕ}
    (hn : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V n.factorial k → ∀ x ∈ L, ∃ l ∈ L, actO V W k 1 x = x + 1 • l)
    {k : GA D V} (hk : k ∈ GlobalTheory.Member.PrincLevel.levelGroup V n.factorial) :
    ∀ u : WO V W, u ∈ L ↔ ∃ u₀ ∈ L, u = actO V W k 1 u₀ := by
  have hki := inv_mem hk
  intro u
  constructor
  · intro hu
    obtain ⟨l, hl, e⟩ := hn k⁻¹ hki.1 hki.2 u hu
    refine ⟨actO V W k⁻¹ 1 u, by rw [e, one_nsmul]; exact L.add_mem hu hl, ?_⟩
    have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D W) u
    rw [inv_inv, inv_one] at this
    exact this.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    obtain ⟨l, hl, e⟩ := hn k hk.1 hk.2 u₀ hu₀
    rw [e, one_nsmul]
    exact L.add_mem hu₀ hl

end GlobalTheory.VacTranslate
