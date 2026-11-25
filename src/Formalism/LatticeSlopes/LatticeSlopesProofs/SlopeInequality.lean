module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Module Submodule

namespace Formalism.F

universe u v

theorem det_gram_basis_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    0 < (Matrix.gram ℝ (fun i => (b i : E))).det :=
  (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L b)).det_pos

theorem covol_pos_of_discrete {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    0 < covol L :=
  covol_pos' E L ‹_›

theorem norm_sum_smul_le_of_int {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → F)
    (C : ℝ) (h : ∀ n : ι → ℤ, ‖∑ i, (n i : ℝ) • w i‖ ≤ C * ‖∑ i, (n i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by
  classical
  have hq : ∀ q : ι → ℚ, ‖∑ i, (q i : ℝ) • w i‖ ≤ C * ‖∑ i, (q i : ℝ) • v i‖ := fun q => by
    let m : ℕ := ∏ i, (q i).den
    have hm : (0 : ℝ) < m := by exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    let n : ι → ℤ := fun i => (q i).num * (m / (q i).den : ℕ)
    have hn : ∀ i, (n i : ℝ) = (m : ℝ) * (q i : ℝ) := fun i => by
      have hdvd : (q i).den ∣ m := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have h1 : ((q i).den : ℝ) * ((m / (q i).den : ℕ) : ℝ) = m := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      have h2 : ((q i).num : ℝ) = (q i : ℝ) * ((q i).den : ℝ) := by
        exact_mod_cast (Rat.mul_den_eq_num (q i)).symm
      dsimp only [n]
      rw [Int.cast_mul, Int.cast_natCast, h2]
      linear_combination (q i : ℝ) * h1
    have key := h n
    simp_rw [hn, mul_smul, ← Finset.smul_sum] at key
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hm.le, mul_left_comm] at key
    exact le_of_mul_le_mul_left key hm
  intro c
  exact (DenseRange.piMap (fun _ => Rat.denseRange_cast)).induction_on c
    (isClosed_le (by fun_prop) (by fun_prop)) hq

theorem slopeInequality_of (h : SlopeLeMuMax.{v}) : SlopeInequality.{u, v} := by
  intro E F _ _ _ _ _ _ L M hL hM hne φ C hφ hC
  classical
  let g : L →ₗ[ℤ] F := M.subtype.comp φ
  have ginj : Function.Injective g := M.injective_subtype.comp hφ
  let N : Submodule ℤ F := LinearMap.range g
  have hNM : N ≤ M := by rintro _ ⟨x, rfl⟩; exact (φ x).2
  have : DiscreteTopology L := hL
  have : DiscreteTopology M := hM
  have : DiscreteTopology N := discreteTopology_of_le hNM
  let e : L ≃ₗ[ℤ] N := LinearEquiv.ofInjective g ginj
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := fun h0 =>
    hx0 (congrArg Subtype.val (hφ (Subtype.ext h0 |>.trans (map_zero φ).symm)))
  have hNne : N ≠ ⊥ := fun h0 => by
    have hmem : g ⟨x, hxL⟩ ∈ N := LinearMap.mem_range_self g ⟨x, hxL⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hφx hmem
  have hCpos : 0 < C := pos_of_mul_pos_left
    ((norm_pos_iff.mpr hφx).trans_le (hC ⟨x, hxL⟩)) (norm_nonneg x)
  have h1 : slope N ≤ muMax M := h F M N hM hNM hNne
  set r := Module.finrank ℤ L
  have hrkN : rk N = r := e.finrank_eq.symm
  have : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hr : (0 : ℝ) < r := by exact_mod_cast Module.finrank_pos (R := ℤ) (M := L)
  let b := Module.finBasis ℤ L
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := fun n => by
    simpa [map_sum, map_zsmul, Int.cast_smul_eq_zsmul] using hC (∑ i, n i • b i)
  have hdet := gram_det_le E F (Fin r) (fun i => (b i : E)) (fun i => ((φ (b i) : M) : F)) C
    (norm_sum_smul_le_of_int _ _ C hint)
  have hle : covol N ≤ C ^ r * covol L := by
    rw [covol_eq_gram F N (Fin r) (b.map e), covol_eq_gram E L (Fin r) b]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) * (Matrix.gram ℝ (fun i => (b i : E))).det) :=
          Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
          rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hlog := Real.log_le_log (covol_pos_of_discrete N) hle
  rw [Real.log_mul (by positivity) (covol_pos_of_discrete L).ne', Real.log_pow] at hlog
  have hs : slope L ≤ slope N + Real.log C := by
    unfold slope deg
    rw [show rk L = r from rfl, hrkN, div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
    linarith
  linarith

end Formalism.F
