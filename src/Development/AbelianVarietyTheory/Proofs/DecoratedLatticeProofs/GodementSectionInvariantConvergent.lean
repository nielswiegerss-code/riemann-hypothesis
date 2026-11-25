module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemEntries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf

@[expose] public section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

namespace GlobalTheory.GodementSectionReduction

open Formalism.UG (bc)

theorem row_ne_zero {A : Type} [CommRing A] [Nontrivial A] {r n : ℕ} {M : Matrix (Fin r) (Fin n) A}
    {N : Matrix (Fin n) (Fin r) A} (h : M * N = 1) (i : Fin r) : ¬∀ x, M i x = 0 := fun h2 => by
  have h5 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun x _ => by rw [h2, zero_mul]] at h5
  exact zero_ne_one h5

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

variable (d : HypDec T T₀ r)

theorem nB_mem (b : Mx D r T₀.rank) : d.nB b ∈ stab d := ⟨1, by rw [d.nB_jX, Units.val_one, Matrix.mul_one]⟩

theorem nC_mem (c : skewA D r) : d.nC c ∈ stab d := ⟨1, by rw [d.nC_jX, Units.val_one, Matrix.mul_one]⟩

theorem wittCoreEmbedding_mem_isotropicStabilizer (g : GA D T₀) : d.emb0 g ∈ stab d := ⟨1, by rw [d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩

theorem exists_decomp (p : stab d) : ∃ b c g, (p : GA D T) = d.nB b * d.nC c * d.emb0 g * d.levi (onX d p) := by
  have h : (p : GA D T) * d.levi (onX d p)⁻¹ ∈ MixPer.stabX d := by
    show mt T (p * d.levi (onX d p)⁻¹) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (mul_jX d p), Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  obtain ⟨n, hn, g, e⟩ := (MixPer.Decomp.mem_stabX_iff d).1 h
  obtain ⟨b, c, rfl⟩ := (MixPer.Decomp.mem_radX_iff d).1 hn
  exact ⟨b, c, g, by rw [← e, map_inv, inv_mul_cancel_right]⟩

theorem reduction_GL_diagonalUnitPowers_compact {E A : Type} [Field E] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (j : E →+* A) {s : Aˣ} {ν : Aˣ →* ℝ≥0} (hν : Continuous ν) (hj : ∀ u : Eˣ, ν (Units.map j.toMonoidHom u) = 1)
    {b : ℝ} (hb : 0 < b) (hs : (ν s : ℝ) = b⁻¹) {r : ℕ}
    (hR : ∃ Ω : Set A, IsCompact Ω ∧ ∀ β : GL (Fin r) A, ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ) (c : GL (Fin r) A),
      (∀ i k, c.1 i k ∈ Ω ∧ c⁻¹.1 i k ∈ Ω) ∧ δ.1.map j * β.1 = diagonal (fun i => (s ^ l i).1) * c.1) :
    ∃ (L : Set (GL (Fin r) A)) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) A,
    ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ), ∃ c ∈ L, bc j δ * α = dg s l * c ∧
      (ν (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (b ^ l i)⁻¹ := by
  obtain ⟨Ω, hΩ, hR⟩ := hR
  choose δ l c hcΩ hred using hR
  replace hred : ∀ β, bc j (δ β) * β = dg s (l β) * c β := fun β => Units.ext (hred β)
  obtain ⟨L, hL, hcL⟩ : Bdd c :=
    bdd_units (bdd_matrix hΩ fun q i k => (hcΩ q i k).1) (bdd_matrix hΩ fun q i k => (hcΩ q i k).2)
  have hdet : Continuous (GeneralLinearGroup.det : GL (Fin r) A → Aˣ) := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  obtain ⟨B, hB⟩ := (hL.image (NNReal.continuous_coe.comp (hν.comp hdet))).bddAbove
  refine ⟨L, B, hL, fun α => ⟨δ α, l α, c α, hcL α, hred α, ?_⟩⟩
  have h1 : GeneralLinearGroup.det (bc j (δ α)) = Units.map j.toMonoidHom (GeneralLinearGroup.det (δ α)) :=
    Units.ext (j.map_det (δ α).1).symm
  have h3 := congrArg (fun x => (ν (GeneralLinearGroup.det x) : ℝ)) (hred α)
  beta_reduce at h3
  rw [map_mul, map_mul, map_mul, map_mul, h1, hj, one_mul, det_dg, map_prod, NNReal.coe_mul, NNReal.coe_prod] at h3
  have h4 : ∀ i, (ν (s ^ l α i) : ℝ) = (b ^ l α i)⁻¹ := fun i => by
    rw [map_zpow, NNReal.coe_zpow, hs, _root_.inv_zpow]
  rw [h3, mul_comm, Finset.prod_congr rfl fun i _ => h4 i]
  exact mul_le_mul_of_nonneg_right (hB ⟨_, hcL α, rfl⟩) (by positivity)

theorem bound_aux {E A : Type} [Field E] [CommRing A] (j : E →+* A) {s : Aˣ} {Ω : Set A} {m₀ r n : ℕ}
    (hm₀ : ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, j x = s.1 ^ m * ω → x = 0) {l : Fin r → ℤ} {y : Matrix (Fin r) (Fin n) E}
    {w : Matrix (Fin r) (Fin n) A} (hw : ∀ i x, w i x ∈ Ω) (e : y.map j = (dg s l)⁻¹.1 * w) (i : Fin r)
    (h : ¬∀ x, y.map j i x = 0) : -(m₀ : ℤ) ≤ l i := by
  by_contra! hlt
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := -l i) (by omega)
  refine h fun x => ?_
  have h3 : j (y i x) = s.1 ^ m * w i x := by
    refine (congrFun (congrFun e i) x).trans ?_
    rw [show (dg s l)⁻¹.1 = diagonal fun i => (s ^ l i)⁻¹.1 from rfl, diagonal_mul, ← _root_.zpow_neg, hm, zpow_natCast,
      Units.val_pow_eq_pow_val]
  rw [map_apply, hm₀ m (by omega) _ (hw i x) _ h3, map_zero]

end GlobalTheory.GodementSectionReduction
