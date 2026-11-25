module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Dr

private theorem multilinear_apply_add_smul_of_vanishing {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ} (A : V [⋀^Fin q]→L[ℝ] F) (z : V)
    (hA : ∀ (u : Fin q → V) (i : Fin q), u i = z → A u = 0) (u : Fin q → V) (a : Fin q → ℝ) :
    A (fun i => u i + a i • z) = A u := by
  rw [show (fun i => u i + a i • z) = u + fun i => a i • z from rfl, A.map_add_univ,
    Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ]
  · intro s _ hs
    obtain ⟨j, hj⟩ := (Finset.compl_ne_univ_iff_nonempty sᶜ).1 (by simpa using hs)
    have hupd : Function.update (s.piecewise u fun i => a i • z) j (a j • z) =
        s.piecewise u fun i => a i • z :=
      Function.update_eq_self_iff.2 (by simp [Finset.mem_compl.1 hj])
    rw [← hupd, A.map_update_smul, hA _ j (by simp), smul_zero]
  · simp

theorem pullA : PullTranslates := by
  intro V F _ _ _ _ Y hY hC l hl q w
  obtain ⟨hlc, hlpos, hlh⟩ := hl
  have hld : ∀ p ∈ Y, DifferentiableAt ℝ l p := fun p hp =>
    (hlc.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have hDr : ∀ p ∈ Y, ∀ h, fderiv ℝ (fun x => l x • x) p h = fderiv ℝ l p h • p + l p • h := by
    intro p hp h
    have hd : HasFDerivAt (fun x => l x • x) _ p := (hld p hp).hasFDerivAt.smul (hasFDerivAt_id p)
    rw [hd.fderiv]
    simp [add_comm]
  have heul : ∀ p ∈ Y, fderiv ℝ l p p = -l p := by
    intro p hp
    have hc : HasDerivAt (fun t : ℝ => t • p) p 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
    have h' : HasFDerivAt l (fderiv ℝ l p) ((1 : ℝ) • p) := by
      simpa using (hld p hp).hasFDerivAt
    have h1 : HasDerivAt (fun t : ℝ => l (t • p)) (fderiv ℝ l p p) 1 := h'.comp_hasDerivAt 1 hc
    have h2 : HasDerivAt (fun t : ℝ => t⁻¹ * l p) (-l p) 1 := by
      simpa using (hasDerivAt_inv (one_ne_zero (α := ℝ))).mul_const (l p)
    have heq : (fun t : ℝ => l (t • p)) =ᶠ[𝓝 1] fun t => t⁻¹ * l p := by
      filter_upwards [lt_mem_nhds one_pos] with t ht using hlh t ht p hp
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hDrp : ∀ p ∈ Y, fderiv ℝ (fun x => l x • x) p p = 0 := by
    intro p hp
    rw [hDr p hp, heul p hp, neg_smul, neg_add_cancel]
  refine ⟨?_, ?_⟩
  · intro p hp v i hvi
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    apply ContinuousAlternatingMap.map_coord_zero _ i
    simp [hvi, hDrp p hp]
  · intro hR hH p hp
    ext v
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hc := hlpos p hp
    have hcp : l p • p ∈ Y := hC _ hc p hp
    have e1 : (fun i => fderiv ℝ (fun x => l x • x) p (v i)) =
        fun i => l p • v i + (fderiv ℝ l p (v i) / l p) • (l p • p) := by
      ext i
      rw [hDr p hp, smul_smul, div_mul_cancel₀ _ hc.ne', add_comm]
    change w (l p • p) (fun i => fderiv ℝ (fun x => l x • x) p (v i)) = w p v
    rw [e1, multilinear_apply_add_smul_of_vanishing (w (l p • p)) (l p • p) (fun u i hu => hR _ hcp u i hu)]
    exact hH _ hc p hp v

end UpperTheory.V.Lit.Dr
