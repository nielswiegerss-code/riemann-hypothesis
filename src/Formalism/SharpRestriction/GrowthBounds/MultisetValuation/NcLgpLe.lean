module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_lgp_le (p : ℕ) (hp : 2 ≤ p) (x : ℤ) (A : ℝ) (c : ℕ) (hx : (x : ℝ) ≤ A ^ c)
    (hl : 1 ≤ Real.logb p A) : (lgp p x : ℝ) ≤ (c + 1) * Real.logb p A := by
  unfold lgp
  split_ifs with h
  · push_cast
    have : 0 ≤ Real.logb p A := by linarith
    nlinarith
  · push_cast
    have hx0 : 0 < x := by omega
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
    have h1 : (Nat.log p x.toNat : ℝ) ≤ Real.logb p (x.toNat : ℝ) := Real.natLog_le_logb _ _
    have h2 : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0.le
      exact_mod_cast this
    rw [h2] at h1
    have h3 : Real.logb p (x : ℝ) ≤ Real.logb p (A ^ c) :=
      Real.logb_le_logb_of_le hp1 (by exact_mod_cast hx0) hx
    rw [Real.logb_pow] at h3
    nlinarith

variable {n' k1 : ℕ}

end Formalism.MainNotions.FormalGroupSystem.Pf
