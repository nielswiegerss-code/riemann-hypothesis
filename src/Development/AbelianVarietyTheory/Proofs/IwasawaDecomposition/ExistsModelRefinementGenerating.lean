module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CechPic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.InvertIdeal

section General

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_mul_pow {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (α : Γ(X, U))
    (hα : genericPoint X ∈ X.basicOpen α) {f : X.functionField} (hf : ∀ x ∈ X.basicOpen α, RegAt x f) :
    ∃ (n : ℕ) (γ : Γ(X, U)), fnOf U h γ = f * fnOf U h α ^ n := by
  obtain ⟨β, rfl⟩ := exists_fnOf_eq hα hf
  have := hU.isLocalization_basicOpen α
  obtain ⟨n, γ, e⟩ := IsLocalization.Away.surj α β
  refine ⟨n, γ, ?_⟩
  have e' := congrArg (fnOf _ hα) e
  rw [map_mul, map_pow] at e'
  have r (a : Γ(X, U)) : fnOf _ hα (algebraMap _ Γ(X, X.basicOpen α) a) = fnOf U h a :=
    fnOf_resG (X.basicOpen_le α) hα a
  rw [r, r] at e'
  exact e'.symm

theorem exists_denom {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) {x : X} (hx : x ∈ U)
    {f : X.functionField} (hf : RegAt x f) :
    ∃ β γ : Γ(X, U), x ∈ X.basicOpen β ∧ fnOf U h γ = f * fnOf U h β := by
  obtain ⟨W, hW, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨α, hle, hα⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hW⟩ hx
  obtain ⟨n, γ, e⟩ := exists_mul_pow hU h α (gen_mem hα) fun y hy => regAt_fnOf (hle hy) (gen_mem hW) a
  refine ⟨α ^ (n + 1), γ * α, by rwa [X.basicOpen_pow α n.succ_pos], ?_⟩
  rw [map_mul, e, map_pow, pow_succ, mul_assoc]


theorem exists_unitAt {x : X} {ι : Type} [Fintype ι] {c g : ι → X.functionField} (hc : ∀ i, RegAt x (c i))
    (hg : ∀ i, RegAt x (g i)) (e : ∑ i, c i * g i = 1) : ∃ i, UnitAt x (g i) := by
  by_contra! H
  have : ZeroAt x (∑ i, c i * g i) := Finset.sum_induction _ _ (fun _ _ => ZeroAt.add) (zeroAt_zero x) fun i _ =>
    mul_comm (g i) (c i) ▸ (zeroAt_iff.2 ⟨hg i, H i⟩).mul (hc i)
  exact (zeroAt_iff.1 (e ▸ this)).2 (unitAt_one x)

theorem exists_common_open {x : X} {ι : Type} [Finite ι] {g : ι → X.functionField} (hg : ∀ i, RegAt x (g i)) :
    ∃ (W : X.Opens) (hx : x ∈ W), ∀ i, ∃ a : Γ(X, W), fnOf W (gen_mem hx) a = g i := by
  choose U hU a ha using fun i => (hg i).exists_fnOf
  let W : X.Opens := ⟨⋂ i, U i, isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hle (i) : W ≤ U i := Set.iInter_subset (fun i => (U i : Set X)) i
  exact ⟨W, Set.mem_iInter.2 hU, fun i => ⟨resG X (hle i) (a i), (fnOf_resG _ _ _).trans (ha i)⟩⟩

end General

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.InvertIdeal
