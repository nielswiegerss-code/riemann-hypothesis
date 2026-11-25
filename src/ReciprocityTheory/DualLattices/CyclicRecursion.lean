module

public import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

@[expose] public section

open WittVector MvPolynomial

namespace ReciprocityTheory.PGsh

section TeichSum

variable {p : ℕ} [hp : Fact p.Prime]

private lemma ghost_one {R : Type*} [CommRing R] (x : WittVector p R) :
    ghostComponent 1 x = x.coeff 0 ^ p + (p : R) * x.coeff 1 := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  simp [Finset.sum_range_succ]

private lemma univ_coeff {ι : Type} (s : Finset ι) :
    (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i ∧
    (p : MvPolynomial ι ℤ) * (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 1 =
      ∑ i ∈ s, X i ^ p - (∑ i ∈ s, X i) ^ p := by
  have h0 : (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i := by
    rw [← WittVector.constantCoeff_apply, map_sum]
    simp
  refine ⟨h0, ?_⟩
  have hg : ghostComponent 1 (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)) =
      ∑ i ∈ s, (X i : MvPolynomial ι ℤ) ^ p := by

    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ghost_one]
    simp [WittVector.teichmuller_coeff_pos]
  rw [ghost_one, h0] at hg
  linear_combination hg

private lemma exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (x : WittVector p K) :
    ∃ w : WittVector p K, x = teichmuller p (x.coeff 0) +
      (p : WittVector p K) * teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
      (p : WittVector p K) ^ 2 * w := by
  have hV (y : WittVector p K) :
      WittVector.verschiebung y = WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y * p := by
    have hF : WittVector.frobenius ((WittVector.frobeniusEquiv p K).symm y) = y :=
      (WittVector.frobeniusEquiv p K).apply_symm_apply y
    conv_lhs => rw [← hF]
    exact WittVector.verschiebung_frobenius _
  have h1 : ∀ z : WittVector p K, ∃ u : WittVector p K,
      z = teichmuller p (z.coeff 0) + WittVector.verschiebung u ∧ u.coeff 0 = z.coeff 1 := by
    intro z
    refine ⟨WittVector.mk p (fun n => z.coeff (n + 1)), ?_, rfl⟩
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · rcases n with _ | n
      · simp [WittVector.teichmuller_coeff_zero, WittVector.verschiebung_coeff_zero]
      · simp [WittVector.teichmuller_coeff_pos, WittVector.verschiebung_coeff_succ]
    · intro m
      rcases m with _ | m
      · right
        simp [WittVector.verschiebung_coeff_zero]
      · left
        simp [WittVector.teichmuller_coeff_pos]
  obtain ⟨u, hu, hu0⟩ := h1 x
  rw [hV] at hu
  obtain ⟨v, hv, -⟩ := h1 (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u)
  rw [hV] at hv
  have hc : (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u).coeff 0 =
      (frobeniusEquiv K p).symm (x.coeff 1) := by
    rw [WittVector.map_coeff, hu0]
    try rfl
  rw [hc] at hv
  refine ⟨WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v, ?_⟩
  calc x = teichmuller p (x.coeff 0) +
        WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u * p := hu
    _ = teichmuller p (x.coeff 0) + (teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
          WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v * p) * p := by rw [hv]
    _ = _ := by ring

theorem teichSum (p : ℕ) [Fact p.Prime] : TeichSumStatement p := by
  intro ι s
  refine ⟨⟨_, (univ_coeff (p := p) s).2⟩, ?_⟩
  intro K _ _ _ X S hS
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (∑ i ∈ s, teichmuller p (X i))
    have h0 : (∑ i ∈ s, teichmuller p (X i)).coeff 0 = ∑ i ∈ s, X i := by
      rw [← WittVector.constantCoeff_apply, map_sum]
      simp
    have hmap : WittVector.map (MvPolynomial.aeval X).toRingHom
        (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)) =
          ∑ i ∈ s, teichmuller p (X i) := by

      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [WittVector.map_teichmuller]
      simp
    have hSeq : (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)).coeff 1 = S := by
      have hp0 : (p : MvPolynomial ι ℤ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      exact mul_left_cancel₀ hp0 ((univ_coeff (p := p) s).2.trans hS.symm)
    have h1 : (∑ i ∈ s, teichmuller p (X i)).coeff 1 = MvPolynomial.aeval X S := by
      rw [← hmap, WittVector.map_coeff, hSeq]
      try rfl
    have hfr : (frobeniusEquiv K p).symm (MvPolynomial.aeval X S) =
        MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S :=
      MvPolynomial.comp_aeval_apply X (((frobeniusEquiv K p).symm : K →+* K).toIntAlgHom) S
    refine ⟨w, ?_⟩
    rw [h0, h1, hfr] at hw
    exact hw
  · intro y t
    have hd : ((p : ℕ) : WittVector p K) ∣ (teichmuller p y + (p : WittVector p K) * t) -
        teichmuller p y := ⟨t, by ring⟩
    obtain ⟨w, hw⟩ := dvd_sub_pow_of_dvd_sub hd 1
    refine ⟨w, ?_⟩
    simp only [pow_one] at hw
    rw [show teichmuller p (y ^ p) = teichmuller p y ^ p from map_pow _ _ _]
    linear_combination hw

end TeichSum

end ReciprocityTheory.PGsh
