module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NeNeedPrice
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcCGNonneg
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdLszLe

@[expose] public section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nd_x_ge : (1 : ℝ) ≤ L.sc.x := le_of_lt L.sc.one_lt_alt

theorem nd_b'_nonneg : 0 ≤ L.sc.b' := by
  have hx : (1 : ℝ) < L.sc.x := L.sc.one_lt_alt
  unfold Scale.b' Scale.a Scale.X' Scale.b
  exact div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.exp_pos _).le

theorem nd_b'_le : L.sc.b' ≤ L.sc.a := by
  have hx : (1 : ℝ) < L.sc.x := L.sc.one_lt_alt
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  unfold Scale.b'
  apply div_le_self ha
  unfold Scale.X'
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem nd_n_ge : (1 : ℝ) ≤ (D.R.n : ℝ) := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h3 : 1 ≤ D.R.n := by unfold Ranks.n; omega
  exact_mod_cast h3

theorem nd_w''_le : L.sc.w'' D.R.n ≤ L.sc.b' := by
  unfold Scale.w''
  exact div_le_self nd_b'_nonneg (one_le_mul_of_one_le_of_one_le nd_x_ge nd_n_ge)

theorem nd_m_ge : (2 : ℝ) ≤ (D.R.m : ℝ) := by
  exact_mod_cast D.R.two_le_m

theorem nd_k_ge : (5 : ℝ) ≤ (D.R.k : ℝ) := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 : 5 ≤ D.R.k := by omega
  exact_mod_cast h3

theorem nd_Sc_le (hS : Formalism.MainNotions.SizesAt L) : 4 * L.Sc ≤ L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS'
  unfold Formalism.MainNotions.SizeEta at hE
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hE
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := nd_n_ge
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := nd_m_ge
  have hb' : 0 ≤ L.sc.b' := nd_b'_nonneg
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    exact div_nonneg hb' (mul_nonneg hx0.le (by positivity))
  have heta : 0 ≤ L.etaSz := le_trans (by positivity) h1
  have hSc : 0 < L.Sc := L.Sc_pos
  have hL : L.sc.L ≤ L.sc.x := by
    unfold Scale.L
    calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith [L.sc.eps_lt])
      _ = L.sc.x := Real.rpow_one _
  have hwx : L.sc.w'' D.R.n * L.sc.x ≤ L.sc.b' := by
    unfold Scale.w''
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hx0 (by linarith))]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx0.le hn) hb'
  have hX : 2 ≤ L.sc.X' := by
    unfold Scale.X'
    have h1' : (1 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) := Real.one_le_rpow hx (by linarith [L.sc.eps_pos])
    linarith [Real.add_one_le_exp (L.sc.x ^ (L.sc.eps / 3))]
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg hx0.le (Real.exp_pos _).le
  have hb'a : 2 * L.sc.b' ≤ L.sc.a := by
    unfold Scale.b'
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith [mul_le_mul_of_nonneg_left hX ha]
  linarith [mul_le_mul_of_nonneg_left hL hw0, mul_le_mul_of_nonneg_right hm (add_nonneg hSc.le heta)]

theorem nd_N_le (hS : Formalism.MainNotions.SizesAt L) : (D.R.N D.R.m : ℝ) ≤ L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS'
  unfold Formalism.MainNotions.SizeEta at hE
  obtain ⟨h1, h2, -⟩ := hE
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hmf := D.R.m_le_f
  have htr := D.R.rank_add_five_le
  have hf : 2 ≤ D.R.f := by unfold Ranks.f Ranks.n; omega
  have ht : 1 ≤ D.R.t := by omega
  have hk : 5 ≤ D.R.k := by omega
  have hNn : D.R.N D.R.m ≤ D.R.t ^ 3 * D.R.f * D.R.k ^ 3 := by
    have e1 : D.R.m * (D.R.t + 1) ≤ D.R.k * (D.R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    have e2 : D.R.k * (D.R.t + 2) ≤ D.R.k * (3 * D.R.t) := Nat.mul_le_mul_left _ (by omega)
    have e3 : 3 ≤ D.R.f * D.R.k ^ 2 :=
      calc 3 ≤ 2 * 5 ^ 2 := by norm_num
        _ ≤ D.R.f * D.R.k ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hk 2)
    have e4 : D.R.t * 3 ≤ D.R.t ^ 3 * (D.R.f * D.R.k ^ 2) :=
      Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) e3
    unfold Ranks.N
    calc D.R.k + D.R.m * (D.R.t + 1) ≤ D.R.k + D.R.k * (D.R.t + 1) := Nat.add_le_add_left e1 _
      _ = D.R.k * (D.R.t + 2) := by ring
      _ ≤ D.R.k * (3 * D.R.t) := e2
      _ = D.R.k * (D.R.t * 3) := by ring
      _ ≤ D.R.k * (D.R.t ^ 3 * (D.R.f * D.R.k ^ 2)) := Nat.mul_le_mul_left _ e4
      _ = D.R.t ^ 3 * D.R.f * D.R.k ^ 3 := by ring
  have hNr : (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by exact_mod_cast hNn
  have ht0 : (0 : ℝ) < D.R.t := by exact_mod_cast (show 0 < D.R.t by omega)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (show 0 < D.R.k by omega)
  have hdpos : 0 < (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    mul_pos (mul_pos (pow_pos ht0 3) hf0) (pow_pos hk0 3)
  have ht1 : (1 : ℝ) ≤ L.etaSz := le_trans (by exact_mod_cast ht) h1
  have hde : (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 * L.etaSz ≤ L.sc.b := by
    rw [le_div_iff₀ hdpos] at h2
    linarith
  calc (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := hNr
    _ ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 * L.etaSz := le_mul_of_one_le_right hdpos.le ht1
    _ ≤ L.sc.b := hde
    _ ≤ L.sc.a := by unfold Scale.a; exact le_mul_of_one_le_left hb hx

end Formalism.MainNotions.FormalGroupSystem.Pf
