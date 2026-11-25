module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ReadEmbEx

theorem exists_read {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)
    (ι : FractionRing O →+* ℂ) :
    ∃ φ : ↥B.LL.1 →+* ℂ, ∀ a : O, φ (B.toLL a) = ι (algebraMap O (FractionRing O) a) := by
  have hinj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)
  let f : FractionRing O →+* ↥B.LL.1 := IsFractionRing.lift (g := B.toLL) hinj
  have hf : ∀ a : O, f (algebraMap O (FractionRing O) a) = B.toLL a := fun a =>
    IsFractionRing.lift_algebraMap _ a
  have hb : Function.Bijective f := by
    refine ⟨f.injective, fun y => ?_⟩
    have hint (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
      have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
      rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
      constructor
      · intro h n
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
        exact ((minpoly ℤ_[l] x).coeff n).2
      · intro h
        have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
          rw [Polynomial.lifts_iff_coeff_lifts]
          exact fun n => ⟨⟨_, h n⟩, rfl⟩
        obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
        refine ⟨q, hqm, ?_⟩
        rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
    have hmem (x : ↥B.LL.1) : x ∈ OL B.LL ↔ ‖(x : Om l)‖ ≤ 1 := by
      rw [← hint, OL, mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (B.LL.1.val.restrictScalars ℤ_[l]) B.LL.1.val.toRingHom.injective).symm
    have hnorm (x : ↥B.LL.1) : ‖(x : Om l)‖ ≤ 1 → ∃ n : O, x = B.toLL n := by
      intro hx
      refine ⟨B.eO.symm ⟨x, (hmem x).2 hx⟩, ?_⟩
      simp [LocBridge.toLL]
    have hfrac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
      by_cases h : ‖(y : Om l)‖ ≤ 1
      · obtain ⟨n, hn⟩ := hnorm y h
        refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
        have := congrArg B.toLL h1
        simp at this
      · have hy : y ≠ 0 := by
          rintro rfl
          simp at h
        have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
          rw [IntermediateField.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ (not_le.1 h).le
        obtain ⟨d, hd⟩ := hnorm _ h'
        refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
        rw [h1, map_zero] at hd
        exact hy (inv_eq_zero.1 hd)
    obtain ⟨n, d, hd, e⟩ := hfrac y
    have hd' : B.toLL d ≠ 0 := fun h0 => hd (hinj (h0.trans (map_zero _).symm))
    refine ⟨algebraMap O _ n / algebraMap O _ d, ?_⟩
    rw [map_div₀, hf, hf, ← e, mul_div_cancel_left₀ _ hd']
  let e := RingEquiv.ofBijective f hb
  refine ⟨ι.comp e.symm.toRingHom, fun a => ?_⟩
  rw [← hf]
  exact congrArg ι (e.symm_apply_apply _)

theorem exists_readEmb : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  intro D bkP i ι v hv τ
  obtain ⟨φ, hφ⟩ := exists_read (bkP.br i v hv) ι
  let c : D.host.E →+* ↥(bkP.br i v hv).Kw.1 :=
    ((bkP.br i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (bkP.br i v hv).Kw.1 (bkP.br i v hv).j_E
  have h : ReadEmb bkP i ι v hv τ ((φ.comp (AlgHom.toRingHom τ)).comp c) := by
    intro x n d hx
    have := congrArg φ hx.2
    rw [map_mul, hφ, hφ] at this
    exact this
  exact ⟨_, h, fun v' hv' τ' hc x n d hx => h _ n d ((hc x n d).1 hx)⟩

end GlobalTheory.ReadEmbEx
