module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
public import Formalism.LatticeSlopes.CovolAntiSameRank
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Module Submodule

namespace Formalism.F

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_span_range_and_covol {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E)
    (hu : LinearIndependent ℝ u) :
    DiscreteTopology (span ℤ (Set.range u)) ∧
      covol (span ℤ (Set.range u)) = Real.sqrt (Matrix.gram ℝ u).det := by
  have hd := discreteTopology_span_range_of_linearIndependent u hu
  refine ⟨hd, ?_⟩
  rw [covol_eq_gram E (span ℤ (Set.range u)) ι (Basis.span (hu.restrict_scalars' ℤ))]
  simp only [Basis.span_apply]

theorem discreteTopology_sup_and_covol_sup (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [DiscreteTopology L₂]
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0) :
    DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E) ∧ covol (L₁ ⊔ L₂) = covol L₁ * covol L₂ := by
  classical
  let b₁ := Module.finBasis ℤ L₁
  let b₂ := Module.finBasis ℤ L₂
  let v₁ : Fin (Module.finrank ℤ L₁) → E := fun i => (b₁ i : E)
  let v₂ : Fin (Module.finrank ℤ L₂) → E := fun i => (b₂ i : E)
  have horth : ∀ i j, inner ℝ (v₁ i) (v₂ j) = 0 := fun i j => h _ (b₁ i).2 _ (b₂ j).2
  have horth' : ∀ i j, inner ℝ (v₂ i) (v₁ j) = 0 := fun i j => (real_inner_comm _ _).trans (horth j i)
  have hdisj : Disjoint (span ℝ (Set.range v₁)) (span ℝ (Set.range v₂)) :=
    Submodule.IsOrtho.disjoint <| Submodule.isOrtho_span.mpr <| by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact horth i j
  have hli := (linearIndependent_coe_basis L₁ b₁).sum_type (linearIndependent_coe_basis L₂ b₂) hdisj
  have hspan : span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, span_range_coe_basis' L₁ b₁,
      span_range_coe_basis' L₂ b₂]
  obtain ⟨hd, hc⟩ := discreteTopology_span_range_and_covol _ hli
  rw [hspan] at hd hc
  have hg : Matrix.gram ℝ (Sum.elim v₁ v₂) =
      Matrix.fromBlocks (Matrix.gram ℝ v₁) 0 0 (Matrix.gram ℝ v₂) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply, horth, horth']
  refine ⟨hd, ?_⟩
  rw [hc, covol_eq_gram E L₁ _ b₁, covol_eq_gram E L₂ _ b₂, hg, Matrix.det_fromBlocks_zero₂₁,
    Real.sqrt_mul (det_gram_basis_pos L₁ b₁).le]

theorem degree_le_rank_mul_maxSlope_of_injective (Q M : Submodule ℤ E) (hQ : DiscreteTopology Q)
    (hM : DiscreteTopology M) (ψ : Q →ₗ[ℤ] M) (hinj : Function.Injective ψ)
    (hψ : ∀ x : Q, ‖((ψ x : M) : E)‖ ≤ ‖(x : E)‖) : deg Q ≤ rk Q * muMax M := by
  have := hQ
  by_cases hQ0 : Q = ⊥
  · subst hQ0; simp [deg, rk, (covol_basic_properties E).1]
  · have hs := slopeInequality_of (slopeLeMuMax_of (slopesBdd_of gram_det_le)) E E Q M hQ hM hQ0
      ψ 1 hinj (fun x => by simpa using hψ x)
    rw [Real.log_one, add_zero] at hs
    have hk' : (0 : ℝ) < (rk Q : ℝ) := by
      exact_mod_cast Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ0)
    exact ((div_le_iff₀ hk').mp hs).trans_eq (mul_comm _ _)

theorem degree_le_rank_mul_maxSlope (L N : Submodule ℤ E) (hL : DiscreteTopology L) (hNL : N ≤ L) :
    deg N ≤ rk N * muMax L :=
  degree_le_rank_mul_maxSlope_of_injective N L (discreteTopology_of_le hNL) hL
    (Submodule.inclusion hNL) (Submodule.inclusion_injective hNL) (fun _ => le_rfl)

theorem slope_le_max_maxSlope (L₁ L₂ : Submodule ℤ E) (h1 : DiscreteTopology L₁)
    (h2 : DiscreteTopology L₂) (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0)
    (hd : DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E))
    (N : Submodule ℤ E) (hN : N ≤ L₁ ⊔ L₂) (hN0 : N ≠ ⊥) :
    slope N ≤ max (muMax L₁) (muMax L₂) := by
  have := h1; have := h2; have := hd
  have hNd : DiscreteTopology N := discreteTopology_of_le hN
  obtain ⟨P, hPdef⟩ : ∃ P : E →L[ℝ] E, P = (span ℝ (L₂ : Set E)).starProjection := ⟨_, rfl⟩
  have hP0 : ∀ x ∈ span ℝ (L₁ : Set E), P x = 0 := fun x hx => by
    rw [hPdef, Submodule.starProjection_apply_eq_zero_iff]
    exact (Submodule.isOrtho_iff_le.mp (Submodule.isOrtho_span.mpr h)) hx
  have hP3 : ∀ x ∈ L₁ ⊔ L₂, P x ∈ L₂ ∧ x - P x ∈ L₁ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hPy : P y = 0 := hP0 y (subset_span hy)
    have hPz : P z = z := by rw [hPdef, Submodule.starProjection_eq_self_iff]; exact subset_span hz
    rw [P.map_add, hPy, hPz, zero_add, add_sub_cancel_right]
    exact ⟨hz, hy⟩
  set K : Submodule ℤ E := N ⊓ L₁
  have hKspan : span ℝ (K : Set E) ≤ span ℝ (L₁ : Set E) := Submodule.span_mono fun _ hx => hx.2
  have hsat : IsSaturated N K :=
    ⟨inf_le_left, fun x hx hxs => ⟨hx, by
      have h1 := (hP3 x (hN hx)).2
      rwa [hP0 x (hKspan hxs), sub_zero] at h1⟩⟩
  obtain ⟨hQd, hrk, hdeg⟩ := degree_quotient E N K hNd hsat
  set Q := quot N K
  have hPR : ∀ x ∈ N, P ((span ℝ (K : Set E))ᗮ.starProjection x) = P x := fun x _ => by
    rw [Submodule.starProjection_orthogonal_val, P.map_sub,
      hP0 _ (hKspan (Submodule.starProjection_apply_mem _ x)), sub_zero]
  have hQmem : ∀ y ∈ Q, P y ∈ L₂ := by
    rintro _ ⟨x, hx, rfl⟩
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) ∈ L₂
    rw [hPR x hx]; exact (hP3 x (hN hx)).1
  let ψ : Q →ₗ[ℤ] L₂ := LinearMap.codRestrict L₂
    ((P.toLinearMap.restrictScalars ℤ).comp Q.subtype) (fun y => hQmem y.1 y.2)
  have hψ : ∀ y : Q, ((ψ y : L₂) : E) = P y := fun _ => rfl
  have hinj : Function.Injective ψ := fun y₁ y₂ hEq => by
    have h0 : P ((y₁ : E) - (y₂ : E)) = 0 := by
      have : P y₁ = P y₂ := by rw [← hψ, ← hψ, hEq]
      rw [P.map_sub, this, sub_self]
    obtain ⟨x, hx, hxEq⟩ := Submodule.mem_map.mp (Q.sub_mem y₁.2 y₂.2)
    have hPx : P x = 0 := by
      have h1 : P ((span ℝ (K : Set E))ᗮ.starProjection x) = 0 := by
        change P ((((span ℝ (K : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ) x) = 0
        rw [hxEq]; exact h0
      rwa [hPR x hx] at h1
    have hxK : x ∈ span ℝ (K : Set E) := subset_span ⟨hx, by
      have h1 := (hP3 x (hN hx)).2
      rwa [hPx, sub_zero] at h1⟩
    have hzero : (y₁ : E) - (y₂ : E) = 0 := by
      rw [← hxEq]
      change (span ℝ (K : Set E))ᗮ.starProjection x = 0
      rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hxK, sub_self]
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have hdK := degree_le_rank_mul_maxSlope L₁ K h1 inf_le_right
  have hdQ := degree_le_rank_mul_maxSlope_of_injective Q L₂ hQd h2 ψ hinj
    (fun y => by rw [hψ, hPdef]; exact Submodule.norm_starProjection_apply_le (span ℝ (L₂ : Set E)) (y : E))
  have hk' : (0 : ℝ) < (rk N : ℝ) := by
    exact_mod_cast Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN0)
  have hrk' : (rk N : ℝ) = (rk K : ℝ) + (rk Q : ℝ) := by exact_mod_cast hrk
  unfold slope
  rw [div_le_iff₀ hk', hdeg, hrk']
  have e1 := mul_le_mul_of_nonneg_left (le_max_left (muMax L₁) (muMax L₂)) (Nat.cast_nonneg (α := ℝ) (rk K))
  have e2 := mul_le_mul_of_nonneg_left (le_max_right (muMax L₁) (muMax L₂)) (Nat.cast_nonneg (α := ℝ) (rk Q))
  linarith

end

theorem orthogonal_sum_slope : OrthSum := by
  intro E _ _ _ L₁ L₂ h1 h2 h
  have := h1; have := h2
  obtain ⟨hd, hc⟩ := discreteTopology_sup_and_covol_sup L₁ L₂ h
  refine ⟨hd, ?_, fun hL1 hL2 => le_antisymm ?_ ?_⟩
  · unfold deg
    rw [hc, Real.log_mul (covol_pos_of_discrete L₁).ne' (covol_pos_of_discrete L₂).ne']
    ring
  · exact csSup_le ⟨_, L₁, le_sup_left, hL1, rfl⟩ fun _ ⟨N, hN, hN0, hEq⟩ =>
      hEq ▸ slope_le_max_maxSlope L₁ L₂ h1 h2 h hd N hN hN0
  · have hmono := muMaxMono_of (slopesBdd_of gram_det_le)
    exact max_le (hmono E (L₁ ⊔ L₂) L₁ hd le_sup_left hL1)
      (hmono E (L₁ ⊔ L₂) L₂ hd le_sup_right hL2)

end Formalism.F
