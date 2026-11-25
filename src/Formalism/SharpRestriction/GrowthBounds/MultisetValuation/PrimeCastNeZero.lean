module

import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm

@[expose] public section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem pKf_ne (Y : Pend X) : ((p : ℕ) : X.G.Kf) ≠ 0 := by
  apply _root_.Formalism.MainNotions.FormalGroupSystem.Pf.pK_ne <;> assumption

theorem algebraMap_inj (Y : Pend X) (he : 0 < X.eO) : Function.Injective (algebraMap X.G.O X.G.Kf) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 X.unif
  obtain ⟨u, hu⟩ := hn

  have h1 : algebraMap X.G.O X.G.Kf (X.vp ^ n) = 0 := by rw [← hu, map_mul, ha, zero_mul]
  have h2 : algebraMap X.G.O X.G.Kf X.vp = 0 := by
    rw [map_pow] at h1
    by_contra h
    exact pow_ne_zero n h h1
  obtain ⟨u', hu'⟩ := X.eO_spec
  have h3 : algebraMap X.G.O X.G.Kf ((p : X.G.O) * u') = 0 := by
    rw [hu', map_pow, h2, zero_pow (by omega)]
  rw [map_mul, map_natCast] at h3
  rcases mul_eq_zero.1 h3 with h | h
  · exact pKf_ne Y h
  · have : algebraMap X.G.O X.G.Kf ((u' : X.G.O) * ((u'⁻¹ : X.G.Oˣ) : X.G.O)) = 0 := by rw [map_mul, h, zero_mul]
    simp at this

theorem isFractionRing_of_pos_eO (Y : Pend X) (he : 0 < X.eO) : IsFractionRing X.G.O X.G.Kf := by
  have : FaithfulSMul X.G.O X.G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj Y he)
  apply IsFractionRing.of_field
  intro z
  rcases Y.Oc_val (algebraMap X.G.Kf Y.Kc z) with h | h
  · obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z).1 h)
    exact ⟨a, 1, by simp [ha]⟩
  · rw [← map_inv₀] at h
    obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z⁻¹).1 h)
    exact ⟨1, a, by simp [ha]⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
