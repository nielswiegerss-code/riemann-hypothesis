module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitOfPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GenSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
import Mathlib.RingTheory.Valuation.LocalSubring
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight

@[expose] public section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem fixed_mem_F (hcm : IsCMExt F E σ) (e : E) (he : σ e = e) : ∃ f : F, algebraMap F E f = e := by
  apply GlobalTheory.SelfDualLatticeCompare.exists_of_conj_eq <;> assumption

theorem sc_eq (a : Fv F v) : sc (E := E) v a = algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  simp [sc, Algebra.TensorProduct.algebraMap_apply]

theorem add_sig_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : ∃ t : Fv F v, z + sigR (Fv F v) σ z = sc (E := E) v t := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [sc_eq]⟩
  | tmul r e =>
    obtain ⟨f, hf⟩ := fixed_mem_F σ hcm (e + σ e) (by rw [map_add (f := _), sigma_invol σ hcm, add_comm])
    refine ⟨f • r, ?_⟩
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    rw [hs, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨t1, h1⟩ := hx
    obtain ⟨t2, h2⟩ := hy
    refine ⟨t1 + t2, ?_⟩
    rw [map_add (f := _), sc_eq, map_add (f := _), ← sc_eq, ← sc_eq, ← h1, ← h2]
    abel

theorem two_ne_zero_v : (2 : Fv F v) ≠ 0 := by
  have h : (2 : F) ≠ 0 := two_ne_zero
  intro h2
  apply h
  apply (algebraMap F (Fv F v)).injective
  rw [map_ofNat, map_zero]
  exact h2

theorem fix_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) :
    ∃ a : Fv F v, z = sc (E := E) v a := by
  obtain ⟨t, ht⟩ := add_sig_sc σ v hcm z
  rw [hz] at ht
  refine ⟨t / 2, ?_⟩
  rw [div_eq_inv_mul, ← sc_mul, ← ht, ← smul_eq_sc, ← two_smul (Fv F v) z, smul_smul,
    inv_mul_cancel₀ (two_ne_zero_v v), one_smul]

theorem one_mem_oEv : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using gen_mem (E := E) v 1

theorem sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  simpa using sc_mul_mem_oEv (E := E) v hc (one_mem_oEv v)

theorem sc_mem_int {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  apply +allowSynthFailures _root_.PI.OmLocU.SdB.b_int_of_sc <;> assumption

theorem fix_int (hcm : IsCMExt F E σ) {z : Fv F v ⊗[F] E} (hz0 : z ∈ OEv (E := E) v) (hz : sigR (Fv F v) σ z = z) :
    ∃ a ∈ v.adicCompletionIntegers F, z = sc (E := E) v a := by
  obtain ⟨a, ha⟩ := fix_sc σ v hcm z hz
  exact ⟨a, sc_mem_int v (ha ▸ hz0), ha⟩

theorem isU_sc {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F)
    (hu : IsUnit (⟨a, ha⟩ : v.adicCompletionIntegers F)) : IsU v (sc (E := E) v a) := by
  obtain ⟨u, hu'⟩ := hu
  refine ⟨sc v ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F), sc_mem v (SetLike.coe_mem _), ?_⟩
  have h1 : a * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) = 1 := by
    have h2 := congrArg (fun r : v.adicCompletionIntegers F => (r : Fv F v)) u.mul_inv
    rw [hu'] at h2
    simpa using h2
  rw [sc_mul, h1, sc_one]

private theorem fixLoc_holds_lemma {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (h : IsU (E := E) v (sc v c)) : IsUnit (⟨c, hc⟩ : v.adicCompletionIntegers F) := by
  obtain ⟨w, hw, hcw⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [sc_eq, map_zero, zero_mul] at hcw
    exact zero_ne_one hcw
  have hweq : w = sc v c⁻¹ := by
    have h1 : sc (E := E) v c⁻¹ * (sc v c * w) = sc v c⁻¹ := by rw [hcw, mul_one]
    rw [← mul_assoc, sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at h1
    exact h1
  have hinv : c⁻¹ ∈ v.adicCompletionIntegers F := sc_mem_int v (hweq ▸ hw)
  have hprod : (⟨c, hc⟩ : v.adicCompletionIntegers F) * ⟨c⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    simp [mul_inv_cancel₀ hc0]
  exact IsUnit.of_mul_eq_one _ hprod

theorem fixLoc_holds : FixLoc σ v := by
  intro hcm x hx y hy hfx hfy hu
  obtain ⟨a, ha, rfl⟩ := fix_int σ v hcm hx hfx
  obtain ⟨b, hb, rfl⟩ := fix_int σ v hcm hy hfy
  have hab : a + b ∈ v.adicCompletionIntegers F := add_mem ha hb
  rw [sc_eq, sc_eq, ← map_add (f := _), ← sc_eq] at hu
  have hU : IsUnit ((⟨a, ha⟩ : v.adicCompletionIntegers F) + ⟨b, hb⟩) := fixLoc_holds_lemma v hab hu
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h | h
  · exact Or.inl (isU_sc v ha h)
  · exact Or.inr (isU_sc v hb h)

end PI.OmLocU.UnN
