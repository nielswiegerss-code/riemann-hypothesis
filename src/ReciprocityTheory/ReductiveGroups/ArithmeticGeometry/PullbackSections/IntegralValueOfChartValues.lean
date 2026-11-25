module

import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem coprime_of_mod_one {g p : ℕ} (h : g % p = 1) : Nat.Coprime g p := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]

theorem g_coprime_ram (D : D7) (k : Fin 2) (p : ℕ) (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  apply coprime_of_mod_one
  rcases hp with rfl | rfl | rfl
  · have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ D.host.QS * D.host.q * D.host.d from
      (h2.mul_right _).mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.q, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 f i ≤ ∑ i, f i := by
  apply GlobalTheory.WtSizes.sum_extendByZero_le_sum <;> assumption


open Classical in
theorem DF_wtA_le {D : D7} (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ Formalism.MainNotions.WeightAlgebra.DF w := by
  show ∑ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) ≤
    ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i)
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = conjEmb (DV.tauEmb D t) then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact add_le_add (sum_extendByZero_le_sum _ _) (sum_extendByZero_le_sum _ _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
