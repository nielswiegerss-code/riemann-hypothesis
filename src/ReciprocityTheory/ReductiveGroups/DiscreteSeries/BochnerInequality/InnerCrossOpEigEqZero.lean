module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Weights

@[expose] public section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section One

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem Wm_le_ncV : Wm ε E V ≤ ncV ε V 1 := by
  unfold Wm
  exact iSup₂_le fun _ _ => inf_le_right

theorem inner_crossOp_eig_eq_zero (hU : IsInfUnitary ε E) {θ θ' : ℝ} (hθ : θ ≠ θ')
    {u v : Big n 1 M} (hu : crossOp ε E 1 0 u = (θ : ℂ) • u)
    (hv : crossOp ε E 1 0 v = (θ' : ℂ) • v) : inner ℂ u v = 0 := by
  have h := crossOp_symm hU 1 0 u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne : (θ : ℂ) ≠ (θ' : ℂ) := by exact_mod_cast hθ
  by_contra h0
  exact hne (mul_right_cancel₀ h0 h)

theorem Wm_perp_Wp (hU : IsInfUnitary ε E) {x y : Big n 1 M} (hx : x ∈ Wm ε E V)
    (hy : y ∈ Wp ε E V) : inner ℂ x y = 0 := by
  have h : (Wm ε E V).IsOrtho (Wp ε E V) := by
    unfold Wm Wp
    refine Submodule.isOrtho_iSup_left.mpr fun θ => Submodule.isOrtho_iSup_left.mpr fun hθ =>
      Submodule.isOrtho_iSup_right.mpr fun θ' => Submodule.isOrtho_iSup_right.mpr fun hθ' => ?_
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hu hv
    exact inner_crossOp_eig_eq_zero hU (ne_of_lt (hθ.trans hθ')) hu.1 hv.1
  exact Submodule.isOrtho_iff_inner_eq.mp h x hx y hy

private theorem casimirK_eq_casValK_smul_of_isKHWVec {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X}
    (hw : IsKHWVec ε A μ w) : casimirK ε A w = (casValK ε μ : ℂ) • w := by
  intros
  apply _root_.ReciprocityTheory.ChartRestriction.DS.casimirK_khwVec <;> assumption

theorem crossOp_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) (hx0 : x ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ r s : Fin n, ε r ≠ ε s ∧ ν = lowK ε lam + root r s ∧
      (2 : ℂ) • crossOp ε E 1 0 x =
        ((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x := by
  obtain ⟨γ, hγ, hνγ⟩ := khw_big_weight hE hV hx hx0 hν
  refine ⟨(γ 0).1, (γ 0).2, hγ 0, ?_, ?_⟩
  · rw [Fin.sum_univ_one] at hνγ
    rw [← hνγ]
    abel
  · have hm : casimirK ε (mAct E 1) x = (casValK ε (lowK ε lam) : ℂ) • x := by
      ext κ
      rw [casimirK_mAct_apply, casimirK_irr hE hV _ (ncV_mem hx κ)]
      rfl
    have hcas := LinearMap.congr_fun (casimirK_bAct (ε := ε) (E := E) 1) x
    rw [casimirK_eq_casValK_smul_of_isKHWVec (bAct_isGlRep hE 1) hν] at hcas
    simp only [LinearMap.add_apply, Fin.sum_univ_one, factorCasimir_ncV_one hx,
      hm, two_smul] at hcas
    rw [two_smul]
    push_cast
    rw [sub_smul, sub_smul, hcas]
    abel

theorem Wm_kStable (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) : IsKStableSub ε (bAct E 1) (Wm ε E V) := by
  intro a b hab v hv
  have hVs : IsKStableSub ε E V := hV.2.1
  have hle : Wm ε E V ≤ (Wm ε E V).comap (bAct E 1 a b) := by
    unfold Wm
    refine iSup₂_le fun θ hθ x hx => ?_
    rw [Submodule.mem_comap]
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hx
    have hc : crossOp ε E 1 0 (bAct E 1 a b x) = bAct E 1 a b (crossOp ε E 1 0 x) :=
      LinearMap.congr_fun (crossOp_comm hE 1 0 hab) x
    have hmem : bAct E 1 a b x ∈
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := by
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      refine ⟨?_, ncV_kStable hVs 1 a b hab x hx.2⟩
      rw [hc, hx.1, map_smul]
    exact Submodule.mem_iSup_of_mem θ (Submodule.mem_iSup_of_mem hθ hmem)
  exact hle hv

end One

end ReciprocityTheory.ChartRestriction.DS
