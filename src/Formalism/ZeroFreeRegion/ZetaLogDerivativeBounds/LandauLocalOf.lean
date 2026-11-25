module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Mathlib.Analysis.Complex.AbsMax

@[expose] public section

open Complex Filter Topology Metric

namespace Formalism.ZF

lemma landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_fun_prod (f := fun ρ w : ℂ => (w - ρ) ^ m ρ) (fun ρ hρ => pow_ne_zero _ (hz ρ hρ))
    (fun ρ _ => (differentiableAt_id.sub_const ρ).pow (m ρ))]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (by fun_prop) (m ρ)]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- Bounds for the zero multiplicities and the logarithmic derivative of a function
factored on a closed ball. -/
theorem localZeroExpansion_bounds (hlog : LogDerivBound) {f h : ℂ → ℂ} {z₀ : ℂ}
    {r M : ℝ} (hr : 0 < r) (hM : 1 ≤ M) {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ ρ ∈ closedBall z₀ (r / 3) ∧ f ρ = 0)
    (hh : DifferentiableOn ℂ h (closedBall z₀ r)) (hh0 : ∀ z ∈ closedBall z₀ (r / 3), h z ≠ 0)
    (hfeq : ∀ z ∈ closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hbound : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  have hr3 : 0 < r / 3 := by positivity
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    simpa [mem_closedBall, dist_eq_norm] using ((hZ ρ).1 hρ).1
  have hfz₀ := hfeq z₀ (mem_closedBall_self hr.le)
  have hhz₀ : h z₀ ≠ 0 := hh0 z₀ (mem_closedBall_self hr3.le)
  have hPz₀le : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ => by
      rw [norm_pow, norm_sub_rev]; exact pow_le_pow_left₀ (norm_nonneg _) (hZball ρ hρ) _
  have hPw : ∀ w : ℂ, ‖w - z₀‖ = r → (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := fun w hw => by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ => ?_
    rw [norm_pow]
    have htri : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by simpa using norm_add_le (w - ρ) (ρ - z₀)
    exact pow_le_pow_left₀ (by linarith) (by linarith [hZball ρ hρ]) _
  have hmax : ∀ z ∈ closedBall z₀ r, ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := fun z hz => by
    have hdc : DiffContOnCl ℂ h (ball z₀ r) := DifferentiableOn.diffContOnCl (by rwa [closure_ball z₀ hr.ne'])
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (fun w hw => ?_)
      (by rwa [closure_ball z₀ hr.ne'])
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm ‖h w‖]
    have hwmem : w ∈ closedBall z₀ r := mem_closedBall.mpr (by rw [dist_eq_norm]; exact hw.le)
    have e1 := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at e1
    have e4 : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
        ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := calc
      _ = (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ := by rw [mul_div_assoc, mul_pow]; ring
      _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right (hPw w hw) (norm_nonneg _)
      _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := e1
      _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPz₀le (norm_nonneg _)) (by linarith)
      _ = _ := by ring
    exact le_of_mul_le_mul_left e4 (by positivity)
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have h0 := hmax z₀ (mem_closedBall_self hr.le)
    rw [le_div_iff₀ (by positivity), mul_comm M] at h0
    exact le_of_mul_le_mul_left h0 (norm_pos_iff.mpr hhz₀)
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have hhb : ∀ z ∈ closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := fun z hz =>
    (hmax z (closedBall_subset_closedBall (by linarith) hz)).trans
      (div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) (one_le_pow₀ one_le_two))
  have hlogb := hlog h z₀ (r / 3) M hr3 hM (hh.mono (closedBall_subset_closedBall (by linarith))) hh0 hhb
  refine ⟨hsum, fun z hz hfz => ?_⟩
  have hzr : z ∈ ball z₀ r := by rw [mem_ball]; linarith [mem_closedBall.mp hz]
  have hnhds : closedBall z₀ r ∈ 𝓝 z := Filter.mem_of_superset (isOpen_ball.mem_nhds hzr) ball_subset_closedBall
  have hfeqz := hfeq z (ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := fun h0 => hfz (by rw [hfeqz, h0, zero_mul])
  have hhz : h z ≠ 0 := fun h0 => hfz (by rw [hfeqz, h0, mul_zero])
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := fun ρ hρ h0 => hfz (by rw [sub_eq_zero.mp h0]; exact ((hZ ρ).1 hρ).2)
  have heq := (logDeriv_congr_nhds (Filter.mem_of_superset hnhds hfeq)).self_of_nhds
  rw [show deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z by
    change logDeriv f z - _ = logDeriv h z
    rw [heq, logDeriv_fun_mul z hPz hhz (by fun_prop) (hh.differentiableAt hnhds),
      landauLocal_logDeriv_prod Z m z hzρ, add_sub_cancel_left]]
  exact (hlogb z (by rw [mem_closedBall] at hz ⊢; linarith)).trans_eq (by rw [div_div_eq_mul_div]; ring)

theorem localZeroExpansionOfFactorization : LandauLocalOf := by
  intro hfac hlog f z₀ r M hr hM hf hf0 hbound
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  exact ⟨Z, m, hZ, hm, localZeroExpansion_bounds hlog hr hM hZ hh hh0 hfeq hbound⟩

end Formalism.ZF
