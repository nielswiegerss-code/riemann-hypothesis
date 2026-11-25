module

import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
public import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

@[expose] public section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section

variable {F : Type} [Field F] [NumberField F]

theorem csGlobApprox_vD (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  first
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap r)

theorem csGlobApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  set Dv := algebraMap (𝓞 F) (v.adicCompletion F) D with hDvdef
  have hDv : Dv ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hDv0 : Valued.v Dv ≠ 0 := (Valuation.ne_zero_iff _).2 hDv
  have hDv1 : Valued.v Dv ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (levelaf_int_mem_v v D)
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 hx
  have ho : IsOpen ((fun y => (y - x) * Dv⁻¹) ⁻¹'
      ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F))) :=
    (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨f, hf⟩ := (HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open ho
    ⟨x, by simp⟩
  have hf' : Valued.v (algebraMap F (v.adicCompletion F) f - x) ≤ Valued.v Dv := by
    change (algebraMap F (v.adicCompletion F) f - x) * Dv⁻¹ ∈
      (Valued.v : Valuation (v.adicCompletion F) _).integer at hf
    have h := (Valuation.mem_integer_iff _ _).1 hf
    simp only [map_mul, map_inv₀] at h
    calc Valued.v (algebraMap F (v.adicCompletion F) f - x)
        = Valued.v (algebraMap F (v.adicCompletion F) f - x) * (Valued.v Dv)⁻¹ * Valued.v Dv := by
          rw [inv_mul_cancel_right₀ hDv0]
      _ ≤ 1 * Valued.v Dv := mul_le_mul_left h _
      _ = Valued.v Dv := one_mul _
  have hfv : v.valuation F f ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    rw [show algebraMap F (v.adicCompletion F) f = (algebraMap F (v.adicCompletion F) f - x) + x by
      ring]
    exact Valuation.map_add_le _ (hf'.trans hDv1) hx1
  have hD' : v.intValuation D ≠ 0 := by rw [← csGlobApprox_vD]; exact hDv0
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hfv (Units.mk0 _ hD')
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f)
      ≤ Valued.v Dv := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap, hDvdef, csGlobApprox_vD]
    exact ha.le
  rw [show x - algebraMap (𝓞 F) (v.adicCompletion F) a =
      -(algebraMap F (v.adicCompletion F) f - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f) by ring]
  exact Valuation.map_add_le _ (by rw [Valuation.map_neg]; exact hf')
    (by rw [Valuation.map_neg]; exact h2)

end

theorem csGlob_intAdApprox : Formalism.UG.CS.IntAdApprox := by
  apply Formalism.UG.P.integral_adele_approximation_holds

end Formalism.UG.P
