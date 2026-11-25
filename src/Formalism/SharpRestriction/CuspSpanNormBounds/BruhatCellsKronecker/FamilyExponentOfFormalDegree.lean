module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

theorem capelliPoly_ofReal {n : ℕ} (lam : Fin n → ℝ) (Y : ℝ) :
    Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (Y : ℂ) = ((∏ s, (Y + lam s) : ℝ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

theorem cfg_P (D : D7) (τ : D.what₂.Tau) (Y : ℝ) :
    (cfgOf D τ).P Y = ∏ s : Fin D.R.r, (Y + lamS D.R (D.hc τ) s) := by
  unfold Formalism.FourierDecayAlt.Sz.Cfg.P
  simp only [← Ico_add_one_right_eq_Icc, ← prod_Ico_add' _ 0 _ 1, Nat.Ico_zero_eq_range, prod_range]
  exact Finset.prod_congr rfl fun s _ => congrArg (Y + ·) (cfg_lam D τ s)

theorem deOf_ne (D : D7) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ∀ w : D.what₂.Word, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 2) (hne : uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1)) :
    deOf D u l ≠ deOf D u' l := by
  intro heq
  apply hne
  have hk : (cfgOf D τ).k = D.R.k := rfl
  rw [← cfg_u D u τ (h5 u) (l + 1) (by omega) (by omega), ← cfg_u D u' τ (h5 u') (l + 1) (by omega) (by omega)]
  have a1 : l + 1 ≠ 1 := by omega
  have a2 : l + 1 ≠ (cfgOf D τ).k := by rw [hk]; omega
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.u, a1, a2, ite_false, Nat.add_sub_cancel, heq]

theorem Tr_pos (D : D7) (u : D.what₂.Word) : 0 < Tr D u := by
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

end Formalism.MainNotions.BridgeLemma
