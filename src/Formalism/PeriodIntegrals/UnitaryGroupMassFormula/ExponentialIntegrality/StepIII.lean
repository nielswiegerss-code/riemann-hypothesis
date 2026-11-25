module
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Development
public import Mathlib.Analysis.Normed.Field.Instances
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatCastMemWittIntegers
@[expose] public section
namespace PI.ExpIntWProof
open PI
theorem div_pow_mem (h : KeyW) (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ y : ℂ_[p], y ∈ Wp p → ‖y‖ ≤ ((p : ℝ)⁻¹) ^ k → y / (p : ℂ_[p]) ^ k ∈ Wp p := by
  intro k
  induction k with
  | zero => intro y hy _; simpa using hy
  | succ k ih =>
    intro y hy hnorm
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
    simpa only [div_div, ← pow_succ'] using ih (y / (p : ℂ_[p]))
      (h p y hy (hnorm.trans_lt (pow_lt_one₀ hpos.le
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) (Nat.succ_ne_zero k))))
      (by rwa [norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ])

theorem stepIII_of_key (h : KeyW) : StepIII := by
  intro p hp x ⟨k, hk⟩ hnorm
  rw [← mul_div_cancel_left₀ x (pow_ne_zero k
    (show (p : ℂ_[p]) ≠ 0 from by exact_mod_cast hp.out.ne_zero))]
  apply div_pow_mem h p k _ hk
  rw [norm_mul, norm_pow, norm_p]
  exact mul_le_of_le_one_right (by positivity) hnorm

theorem expIntW_of_key (h1 : StepI) (h : KeyW) : ExpIntW :=
  expIntW_of_steps h1 (stepIII_of_key h)
end PI.ExpIntWProof
