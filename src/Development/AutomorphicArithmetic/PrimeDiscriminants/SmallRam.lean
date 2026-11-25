module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

@[expose] public section

open NumberField IsDedekindDomain Ideal

namespace Formalism.HC.HostAx

variable {φ : Frame} (H : HostAx φ)

theorem mem_sq_of_dvd_QS (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) (P : Ideal (𝓞 H.E)) [hP : P.IsPrime]
    (hm : (l : 𝓞 H.E) ∈ P) : (l : 𝓞 H.E) ∈ P ^ 2 := by
  have hEgal := H.galois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have : Fact l.Prime := ⟨hl⟩
  have hlz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have hsp : (span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlz.ne_zero).2 hlz
  have hne : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hlz.ne_zero
  have hlo : P.LiesOver (span {(l : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hlz).2 (by simpa using hm)
  obtain ⟨u, hu, hu1⟩ := hE l hl hd
  have hN : l ∣ H.condN := hd.trans H.QS_dvd_condN
  have hdiv : ordCompl[l] H.condN ∣ H.condN / l := by
    have h1 : 1 ≤ H.condN.factorization l := (hl.dvd_iff_one_le_factorization H.condN_ne_zero).1 hN
    exact Nat.div_dvd_div_left (Nat.ordProj_dvd _ _) (by simpa using pow_dvd_pow l h1)
  have hin : ∀ x : 𝓞 H.E, H.gal.symm (H.art u) • x - x ∈ P :=
    (H.der.inertia l P _).2 ⟨u, hu.of_dvd hdiv, H.gal.apply_symm_apply _⟩
  have hnt : 1 < Nat.card (P.inertia Gal(H.E/ℚ)) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨⟨⟨_, AddSubgroup.mem_inertia.2 hin⟩, 1, fun h1 => hu1 ?_⟩⟩
    have h2 : H.gal.symm (H.art u) = 1 := congrArg Subtype.val h1
    simpa using congrArg H.gal h2
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ),
    ← ramificationIdx'_eq_ramificationIdx (span {(l : ℤ)}) P hne] at hnt
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (span {(l : ℤ)}) ≤ P ^ 2 := le_pow_of_le_ramificationIdx' hnt
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at hle
  simpa using hle

end Formalism.HC.HostAx
