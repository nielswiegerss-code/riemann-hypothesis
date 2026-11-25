module

public import Formalism.LatticeSlopes.CovolAntiSameRank
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality

@[expose] public section

open Module Submodule

namespace Formalism.F

theorem rank_eq_finrank_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (N : Submodule ℤ E) [hN : DiscreteTopology N] :
    rk N = finrank ℝ (span ℝ (N : Set E)) := by
  have hd : DiscreteTopology (span ℤ (N : Set E)) := (Submodule.span_eq N).symm ▸ hN
  have h := (Real.finrank_eq_int_finrank_of_discrete hd).symm
  unfold Set.finrank at h
  rwa [Submodule.span_eq] at h

theorem saturation_properties : SaturProps := by
  intro E _ _ _ L N hL hNL
  have := hL
  have hSL : satur L N ≤ L := inf_le_left
  have hNS : N ≤ satur L N := fun x hx => ⟨hNL hx, Submodule.subset_span hx⟩
  have hspan : span ℝ (satur L N : Set E) = span ℝ (N : Set E) :=
    le_antisymm (Submodule.span_le.mpr fun _ hx => hx.2) (Submodule.span_mono hNS)
  have : DiscreteTopology (satur L N) := discreteTopology_of_le hSL
  have : DiscreteTopology N := discreteTopology_of_le hNL
  exact ⟨⟨hSL, fun x hx hxs => ⟨hx, hspan ▸ hxs⟩⟩, hNS, by
    rw [rank_eq_finrank_span, rank_eq_finrank_span, hspan]⟩

theorem covol_anti_same_rank : CovolAntiSameRank := by
  intro E _ _ _ N N' hN' hle hrk
  have := hN'
  have hN : DiscreteTopology N := discreteTopology_of_le hle
  let e := Module.finBasis ℤ N'
  let f : Basis (Fin (Module.finrank ℤ N')) ℤ N := (Module.finBasis ℤ N).reindex (finCongr hrk)
  let M : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℤ :=
    fun i j => e.repr ⟨(f j : E), hle (f j).2⟩ i
  have hfj : (fun j => (f j : E)) = fun j => ∑ i, (M.map (Int.cast : ℤ → ℝ)) i j • (e i : E) := by
    funext j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hle (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    show (f j : E) = ∑ i, ((M i j : ℤ) : ℝ) • (e i : E)
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  have hdet : (Matrix.gram ℝ (fun j => (f j : E))).det
      = ((M.det : ℤ) : ℝ) ^ 2 * (Matrix.gram ℝ (fun i => (e i : E))).det := by
    rw [hfj, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      ← Int.cast_det]
    ring
  have hfpos : 0 < (Matrix.gram ℝ (fun j => (f j : E))).det := det_gram_basis_pos N f
  have hepos : 0 < (Matrix.gram ℝ (fun i => (e i : E))).det := det_gram_basis_pos N' e
  have hM0 : M.det ≠ 0 := fun h0 => by simp [h0] at hdet; linarith
  have hM1 : (1 : ℝ) ≤ ((M.det : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ M.det ^ 2 := by rw [← sq_abs]; nlinarith [Int.one_le_abs hM0]
    exact_mod_cast this
  rw [covol_eq_gram E N' _ e, covol_eq_gram E N _ f, hdet]
  exact Real.sqrt_le_sqrt (by nlinarith)

end Formalism.F
