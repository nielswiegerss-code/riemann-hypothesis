module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.LocalBesselAndTopKernel Formalism.QuantumDeterminants NumberField IsDedekindDomain ValuativeRel
open scoped ENNReal

variable {D : D7}

theorem Dstar_pos (D : D7) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem section_exists : ∀ (k r : ℕ) (L : LocBessel k r), 1 ≤ k → ∃ μsec, IsSection k r L.z L.z' μsec
  | 0, _, _, h => absurd h (by norm_num)
  | _ + 1, _, L, _ => Formalism.MainNotions.S.Inh.big_cell_section_of_local_bessel L


theorem ptEntry_col {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ j, j < (bs.map Prod.snd).sum → ∃ i, i < (bs.map Prod.snd).sum ∧ ∃ t : K, t ≠ 0 ∧
      ∀ j', ptEntry bs i j' = if j' = j then t else 0 := by
  intro bs
  induction bs with
  | nil =>
    intro _ j hj
    exact absurd hj (by simp)
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    intro h j hj
    simp only [List.map_cons, List.sum_cons] at hj ⊢
    by_cases hjs : j < s
    · refine ⟨s - 1 - j, by omega, t, (h (t, s) (by simp)).1, fun j' => ?_⟩
      simp only [ptEntry]
      by_cases hj' : j' = j
      · subst hj'
        rw [ite_eq_left ⟨by omega, hjs⟩, ite_eq_left (by omega), ite_eq_left rfl]
      · rw [ite_eq_right hj']
        by_cases h2 : j' < s
        · rw [ite_eq_left ⟨by omega, h2⟩, ite_eq_right (by omega)]
        · rw [ite_eq_right (fun hh => h2 hh.2), ite_eq_right (fun hh => by omega)]
    · have hrest : ∀ b ∈ rest, b.1 ≠ 0 ∧ 1 ≤ b.2 :=
        fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hjrest : j - s < (rest.map Prod.snd).sum := by omega
      obtain ⟨i0, hi0, t0, ht0, h0⟩ := ih hrest (j - s) hjrest
      refine ⟨i0 + s, by omega, t0, ht0, fun j' => ?_⟩
      simp only [ptEntry]
      rw [ite_eq_right (fun hh => by omega)]
      by_cases h2 : s ≤ j'
      · rw [ite_eq_left ⟨by omega, h2⟩, Nat.add_sub_cancel, h0]
        by_cases hj' : j' = j
        · rw [ite_eq_left (by omega), ite_eq_left hj']
        · rw [ite_eq_right (by omega), ite_eq_right hj']
      · rw [ite_eq_right (fun hh => h2 hh.2), ite_eq_right (by omega)]

theorem ptMat_det_ne {K : Type} [Field K] {n : ℕ} (p : Point K n) : (ptMat p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  funext j
  obtain ⟨i, hi, t, ht, hcol⟩ := ptEntry_col p.1 p.2.1 j.val (by rw [p.2.2]; exact j.2)
  have h1 := congrFun h0 ⟨i, by rw [← p.2.2]; exact hi⟩
  simp only [Matrix.mulVec, dotProduct, ptMat, hcol, Pi.zero_apply] at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [ite_eq_right (fun hh => hb (Fin.ext hh)), zero_mul])
    (fun hh => absurd (Finset.mem_univ j) hh), ite_eq_left rfl] at h1
  exact (mul_eq_zero.1 h1).resolve_left ht

theorem Dmin_top_ne (w : Point D.host.E (D.R.rS + 1)) : LocalSplitGroups.Dmin w (D.R.rS + 1) ≠ 0 := by
  unfold LocalSplitGroups.Dmin
  rw [dite_eq_left le_rfl]
  have : (ptMat w).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))) = ptMat w := by
    ext a b; rfl
  rw [this]
  exact ptMat_det_ne w

end Formalism.MainNotions.BridgeLemma
