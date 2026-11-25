module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInvariantCellAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Tactic.TypeStar

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

section

variable {k r : ℕ}

theorem unipotent_fixes_anisotropic_vector (l : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) : Q.w1 k r l c *ᵥ v = v := by
  apply +allowSynthFailures _root_.Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3.unipotent_fixes_base_vector <;> assumption

theorem top_wlist_wb (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    (L.map fun a => Q.w1 k r a (c a)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_anisotropic_vector a _ v hv]

theorem inv_wCell_last_mul_mulVec_of_inWb {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ z = g⁻¹ *ᵥ z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hgu : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul hgu
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (g⁻¹ *ᵥ z) = z := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z g, Matrix.mul_nonsing_inv _ hgu, Matrix.one_mulVec]
    exact top_wlist_wb c _ z hz
  conv_lhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem top_qminor_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n t t' : ℕ}
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = t') (a b : Fin t' → Fin n) (u : ℂ) :
    qminorOp Eop (a ∘ Fin.cast h) (b ∘ Fin.cast h) u = qminorOp Eop a b u := by
  subst h
  rfl

theorem top_chatL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℕ} (h : t = k + 1)
    (pos : Fin t → Fin (2 * r + k + 1)) (hpos : ∀ j, (pos j).val = r + j.val) (u : ℂ)
    (a β : Q.Mx k r → Fin t → ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Q.chatL (Q.EH k r) pos u a β f g = ∑ s : Fin (k + 1), ∑ t' : Fin (k + 1),
      (((-1 : ℂ) ^ ((s : ℕ) + (t' : ℕ))) * β g (Fin.cast h.symm s) * a g (Fin.cast h.symm t')) •
        qminorOp (Q.EH k r) (rowsN k r (Fin.last r) s) (rowsN k r (Fin.last r) t') u f g := by
  subst h
  unfold Q.chatL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t' _ => ?_
  have hc : k + 1 - 1 = r - (Fin.last r).val + k := by simp
  have e : ∀ i : Fin (k + 1), pos ∘ Q.skip1 i = rowsN k r (Fin.last r) i ∘ Fin.cast hc := by
    intro i
    funext j
    apply Fin.ext
    simp only [Function.comp_apply, Q.skip1, rowsN, Fin.val_last, Fin.val_cast]
    split_ifs <;> simp_all <;> omega
  rw [e s, e t', top_qminor_cast]
  rfl

end

theorem residue_top_holds : JDRTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  simp only [FN, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, inv_wCell_last_mul_mulVec_of_inWb hc hg hz]
  congr 2
  · congr 1
    simp only [Q.xbv, fvec]
    congr 1
    · congr 1; apply Fin.ext; simp [Q.posL, wI]; omega
    · simp
  · simp only [Q.yv, fvec]
    congr 2
    · simp
    · apply Fin.ext; simp [Q.posL, wI]; omega

end Formalism.FourierDecayAlt.P.CutMP
