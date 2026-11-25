module

public import Formalism.QuotientMetricDivisors.LatticeGlueUnique
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix

namespace Formalism.DivisionValues

namespace GluingInclusion

open Formalism.HermitianLatticesTheory

section General

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem lg (hR : ¬ IsField R) (A : Submodule R V) (x : V)
    (hx : ∀ w : HeightOneSpectrum R, x ∈ localization₂ w.asIdeal A) : x ∈ A := by
  let I : Ideal R :=
    { carrier := {r | r • x ∈ A}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_smul] at *
        exact A.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c r hr => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *
        exact A.smul_mem c hr }
  by_contra hxA
  have hI : I ≠ ⊤ := fun h => hxA (by
    have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using h1)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := fun h => hR (Ring.isField_iff_maximal_bot.2 (h ▸ hM))
  let w : HeightOneSpectrum R := ⟨M, hM.isPrime, hM0⟩
  obtain ⟨s, hs, hsx⟩ := hx w
  exact hs (hIM hsx)

theorem sep (w : HeightOneSpectrum R) (c : R) (hc : c ≠ 0) :
    ∃ s, s ∉ w.asIdeal ∧ ∀ w' : HeightOneSpectrum R, w' ≠ w → ∃ t, t ∉ w'.asIdeal ∧ c ∣ t * s := by
  have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {c}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJw : ¬ J ≤ w.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsw⟩ := SetLike.not_le_iff_exists.mp hJw
  refine ⟨s, hsw, fun w' hw' => ?_⟩
  have hpow : ¬ w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {c}) ≤ w'.asIdeal := by
    intro h
    have h1 : w.asIdeal ≤ w'.asIdeal := w'.isPrime.le_of_pow_le h
    exact hw' (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htw⟩ := SetLike.not_le_iff_exists.mp hpow
  refine ⟨t, htw, ?_⟩
  have : t * s ∈ Ideal.span {c} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht hsJ
  exact Ideal.mem_span_singleton.mp this

theorem denom (A B : Submodule R V) (hA : A.FG) (hB : Submodule.span K (B : Set V) = ⊤) :
    ∃ d : R, d ≠ 0 ∧ ∀ x ∈ A, d • x ∈ B := by
  obtain ⟨d, hd, h⟩ := indexBasic_denom (nonZeroDivisors R) A B hA
    (by rw [indexBasic_locS_top (K := K) B hB]; exact le_top)
  exact ⟨d, nonZeroDivisors.ne_zero hd, h⟩

theorem glue_spec (hR : ¬ IsField R) (L0 : Submodule R V) (L : HeightOneSpectrum R → Submodule R V)
    (h0 : Submodule.IsFullLattice K L0) (hL : ∀ w, Submodule.IsFullLattice K (L w))
    (hfin : {w : HeightOneSpectrum R | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsFullLattice K (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) ∧
      ∀ w : HeightOneSpectrum R,
        localization₂ w.asIdeal (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) =
          localization₂ w.asIdeal (L w) := by
  classical
  set G : Submodule R V := ⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w) with hG
  have hGmem : ∀ x, x ∈ G ↔ ∀ w : HeightOneSpectrum R, x ∈ localization₂ w.asIdeal (L w) := by
    intro x
    rw [hG, Submodule.mem_iInf]

  have hA : ∃ a : R, a ≠ 0 ∧ ∀ x ∈ L0, a • x ∈ G := by
    choose a ha0 ha using fun w => denom (K := K) L0 (L w) (Submodule.IsLattice.fg (self := h0.toIsLattice))
      (Submodule.IsFullLattice.span_eq_top (self := hL w))
    refine ⟨∏ w ∈ hfin.toFinset, a w, Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w), ?_⟩
    intro x hx
    rw [hGmem]
    intro w
    by_cases hw : w ∈ hfin.toFinset
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a hw
      rw [hr, mul_comm, mul_smul]
      exact locBasic_le_locS _ _ ((L w).smul_mem r (ha w x hx))
    · have hw' : localization₂ w.asIdeal (L w) = localization₂ w.asIdeal L0 := by
        by_contra h
        exact hw (hfin.mem_toFinset.mpr h)
      rw [hw']
      exact locBasic_le_locS _ _ (L0.smul_mem _ hx)

  have hB : ∃ b : R, b ≠ 0 ∧ ∀ x ∈ G, b • x ∈ L0 := by
    choose b hb0 hb using fun w => denom (K := K) (L w) L0 (Submodule.IsLattice.fg (self := (hL w).toIsLattice))
      (Submodule.IsFullLattice.span_eq_top (self := h0))
    refine ⟨∏ w ∈ hfin.toFinset, b w, Finset.prod_ne_zero_iff.mpr (fun w _ => hb0 w), ?_⟩
    intro x hx
    apply lg hR
    intro w
    have hxw := (hGmem x).mp hx w
    by_cases hw : w ∈ hfin.toFinset
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem b hw
      obtain ⟨s, hs, hsx⟩ := hxw
      refine ⟨s, hs, ?_⟩
      have e : s • (∏ w ∈ hfin.toFinset, b w) • x = r • (b w • (s • x)) := by
        rw [hr]
        module
      rw [e]
      exact L0.smul_mem r (hb w _ hsx)
    · have hw' : localization₂ w.asIdeal (L w) = localization₂ w.asIdeal L0 := by
        by_contra h
        exact hw (hfin.mem_toFinset.mpr h)
      rw [hw'] at hxw
      exact (localization₂ w.asIdeal L0).smul_mem _ hxw
  obtain ⟨a, ha0, ha⟩ := hA
  obtain ⟨b, hb0, hb⟩ := hB
  have hinvsmul : ∀ (r : R), r ≠ 0 → ∀ y : V, (algebraMap R K r)⁻¹ • (r • y) = y := by
    intro r hr y
    have : algebraMap R K r ≠ 0 := by
      simpa using (IsFractionRing.injective R K).ne hr
    rw [← algebraMap_smul K r y, smul_smul, inv_mul_cancel₀ this, one_smul]
  refine ⟨{ toIsLattice := ⟨?_, ?_⟩, span_eq_top := ?_ }, ?_⟩
  ·
    have hN : IsNoetherian R L0 :=
      isNoetherian_of_fg_of_noetherian L0 (Submodule.IsLattice.fg (self := h0.toIsLattice))
    have hle : G.map (LinearMap.lsmul R V b) ≤ L0 := by
      rintro _ ⟨x, hx, rfl⟩
      exact hb x hx
    have hfg : (G.map (LinearMap.lsmul R V b)).FG := isNoetherian_submodule.mp hN _ hle
    refine Submodule.fg_of_fg_map_injective (LinearMap.lsmul R V b) ?_ hfg
    intro x y hxy
    have hxy' : b • x = b • y := hxy
    rw [← hinvsmul b hb0 x, ← hinvsmul b hb0 y, hxy']
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · have haK : algebraMap R K a ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R K).ne ha0
    rw [eq_top_iff, ← h0.span_eq_top, Submodule.span_le]
    intro x hx
    apply (Submodule.smul_mem_iff _ haK).mp
    rw [algebraMap_smul K]
    exact Submodule.subset_span (ha x hx)
  · intro w
    apply le_antisymm
    · have h1 : G ≤ localization₂ w.asIdeal (L w) := iInf_le _ w
      calc localization₂ w.asIdeal G ≤ localization₂ w.asIdeal (localization₂ w.asIdeal (L w)) := locBasic_locS_mono _ h1
        _ = localization₂ w.asIdeal (L w) := locBasic_locS_idem _ _
    · have h1 : L w ≤ localization₂ w.asIdeal G := by
        intro x hx

        obtain ⟨c', hc', hc'x⟩ : ∃ c' ∈ nonZeroDivisors R, c' • x ∈ L0 := by
          have : x ∈ locS (nonZeroDivisors R) L0 := by
            rw [indexBasic_locS_top (K := K) L0 (Submodule.IsFullLattice.span_eq_top (self := h0))]
            exact Submodule.mem_top
          exact this
        have hc0 : a * c' ≠ 0 := mul_ne_zero ha0 (nonZeroDivisors.ne_zero hc')
        have hcx : (a * c') • x ∈ G := by
          rw [mul_smul]
          exact ha _ hc'x
        obtain ⟨s, hsw, hs⟩ := sep w (a * c') hc0
        refine ⟨s, hsw, ?_⟩
        rw [hGmem]
        intro w'
        by_cases hw' : w' = w
        · subst hw'
          exact locBasic_le_locS _ _ ((L w').smul_mem s hx)
        · obtain ⟨t, ht, u, hu⟩ := hs w' hw'
          have h2 : t • (s • x) ∈ localization₂ w'.asIdeal (L w') := by
            rw [smul_smul, hu, mul_comm, mul_smul]
            exact (localization₂ w'.asIdeal (L w')).smul_mem u ((hGmem _).mp hcx w')
          have h3 : s • x ∈ localization₂ w'.asIdeal (localization₂ w'.asIdeal (L w')) := ⟨t, ht, h2⟩
          rwa [show localization₂ w'.asIdeal (localization₂ w'.asIdeal (L w')) = localization₂ w'.asIdeal (L w') from
            locBasic_locS_idem _ _] at h3
      calc localization₂ w.asIdeal (L w) ≤ localization₂ w.asIdeal (localization₂ w.asIdeal G) := locBasic_locS_mono _ h1
        _ = localization₂ w.asIdeal G := locBasic_locS_idem _ _

end General

section NF

variable {K : Type} [Field K] [NumberField K]

theorem glueLat_spec {D : ℕ} (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (h0 : Submodule.IsFullLattice K L0) (hL : ∀ w, Submodule.IsFullLattice K (L w))
    (hfin : {w : HeightOneSpectrum (𝓞 K) | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsFullLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal (glueLat L) = localization₂ w.asIdeal (L w) :=
  glue_spec (NumberField.RingOfIntegers.not_isField K) L0 L h0 hL hfin

end NF

section Star

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjIdeal_eq (w : HeightOneSpectrum (𝓞 K)) :
    conjIdeal (K := K) w.asIdeal = (conjPl w).asIdeal := by
  show Ideal.span _ = Ideal.map (cO K) w.asIdeal
  unfold Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (RingOfIntegers.ext h).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

theorem matLat_lattice' {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (hP : Function.Surjective P.mulVec) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K (matLat P M) := by
  refine ⟨(Submodule.IsLattice.fg (self := hM)).map _, ?_⟩
  have : ((matLat P M : Submodule (𝓞 K) (Fin D → K)) : Set (Fin D → K)) =
      (Matrix.mulVecLin P) '' (M : Set (Fin n → K)) := by
    rw [matLat, Submodule.map_coe]
    rfl
  exact fun _ _ hli => (LinearIndependent.iff_fractionRing _ _).mp hli

end Star

end GluingInclusion

open GluingInclusion Formalism.HermitianLatticesTheory

theorem lattice_gluing (K : Type) [Field K] [NumberField K] (D : ℕ)
    (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (h0 : Submodule.IsFullLattice K L0) (hL : ∀ w, Submodule.IsFullLattice K (L w))
    (hfin : {w : HeightOneSpectrum (𝓞 K) |
      localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsFullLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        localization₂ w.asIdeal (glueLat L) = localization₂ w.asIdeal (L w) :=
  glueLat_spec L0 L h0 hL hfin

end Formalism.DivisionValues
