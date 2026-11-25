module

public import Formalism.PeriodIntegrals.GTDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.CardEraseIccMin
import Formalism.LocalRingCardinality.Params

@[expose] public section

namespace PI.GTNum

open Formalism.BasicNotions PI Finset

variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem lam_le_last (k : ℕ) (hk : k < N) : lam.w ⟨N - 1, by omega⟩ ≤ lam.w ⟨k, hk⟩ :=
  lam.anti (Fin.mk_le_mk.2 (by omega))

theorem term_nonneg (hI : Interlace h lam sg) (i : Fin n) : 0 ≤ sg.w i - lam.w ⟨i.1 + 1, by omega⟩ := by
  have := (hI i).2
  omega

theorem determinantWeight_nonneg (hI : Interlace h lam sg) : 0 ≤ D0 h lam sg :=
  Finset.sum_nonneg (fun i _ => term_nonneg h lam sg hI i)

theorem term_le_D0 (hI : Interlace h lam sg) (i : Fin n) :
    sg.w i - lam.w ⟨i.1 + 1, by omega⟩ ≤ D0 h lam sg :=
  Finset.single_le_sum (f := fun i : Fin n => sg.w i - lam.w ⟨i.1 + 1, by omega⟩)
    (fun j _ => term_nonneg h lam sg hI j) (Finset.mem_univ i)

theorem last_le_sg (hI : Interlace h lam sg) (j : Fin n) : lam.w ⟨N - 1, by omega⟩ ≤ sg.w j :=
  le_trans (lam_le_last h lam (j.1 + 1) (by omega)) (hI j).2

theorem sg_mem_R (hI : Interlace h lam sg) (i : Fin n) : sg.w i ∈ Rset h lam sg i := by
  unfold Rset
  have h1 := hI i
  have h2 := term_le_D0 h lam sg hI i
  rw [Finset.mem_Icc]
  refine ⟨h1.2, le_min h1.1 (by omega)⟩

theorem lam_succ_le (i : Fin n) : lam.w ⟨i.1 + 1, by omega⟩ ≤ lam.w ⟨i.1, by omega⟩ :=
  lam.anti (Fin.mk_le_mk.2 (by omega))

theorem card_R_erase (hI : Interlace h lam sg) (i : Fin n) :
    ((((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) =
      min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg) := by
  have hm := sg_mem_R h lam sg hI i
  unfold Rset at hm ⊢
  exact card_erase_Icc_min _ _ _ _ (lam_succ_le h lam i) (determinantWeight_nonneg h lam sg hI) hm

theorem interlacing_defect_eq_card (hI : Interlace h lam sg) :
    D1 h lam sg = ((∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) := by
  unfold D1
  push_cast
  exact Finset.sum_congr rfl (fun i _ => (card_R_erase h lam sg hI i).symm)

end PI.GTNum
