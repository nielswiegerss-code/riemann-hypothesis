module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField Module

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  let ι := algebraMap (𝓞 F) (𝓞 K)
  have coe_ι (b : 𝓞 F) : ((ι b : 𝓞 K) : K) = algebraMap F K (b : F) :=
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K b).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K b)
  have ι_injective : Function.Injective ι := by
    intro b c h
    apply RingOfIntegers.ext
    have hcoe := congrArg (fun z : 𝓞 K => (z : K)) h
    exact (algebraMap F K).injective ((coe_ι b).symm.trans (hcoe.trans (coe_ι c)))
  have conj_ι (b : 𝓞 F) : conjO K (ι b) = ι b := by
    apply RingOfIntegers.ext
    change star ((ι b : 𝓞 K) : K) = ((ι b : 𝓞 K) : K)
    rw [coe_ι]
    exact (hF _).mpr ⟨b, rfl⟩
  have exists_trace (z : 𝓞 K) : ∃ b : 𝓞 F, ι b = z + conjO K z := by
    let w : 𝓞 K := z + conjO K z
    have hw : star (w : K) = (w : K) := by
      change star ((z : K) + star (z : K)) = (z : K) + star (z : K)
      rw [star_add, star_star, add_comm]
    obtain ⟨b, hb⟩ := (hF _).mp hw
    have hb_int : IsIntegral ℤ b := by
      apply (isIntegral_algHom_iff (algebraMap F K).toIntAlgHom (algebraMap F K).injective).mp
      change IsIntegral ℤ (algebraMap F K b)
      rw [hb]
      exact RingOfIntegers.isIntegral_coe w
    refine ⟨⟨b, hb_int⟩, RingOfIntegers.ext ?_⟩
    exact (coe_ι ⟨b, hb_int⟩).trans hb
  let trace (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_trace z)
  have trace_spec (z : 𝓞 K) : ι (trace z) = z + conjO K z :=
    Classical.choose_spec (exists_trace z)
  let tr : 𝓞 K →ₗ[𝓞 F] 𝓞 F :=
    { toFun := trace
      map_add' := by
        intro x y
        apply ι_injective
        rw [trace_spec, map_add, map_add, trace_spec, trace_spec]
        ring
      map_smul' := by
        intro b z
        apply ι_injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, trace_spec, trace_spec, Algebra.smul_def,
          map_mul, conj_ι]
        ring }
  have htop : LinearMap.range tr = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range tr) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← trace_spec]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have hdiff : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [pow_one] using hsq)
    have hone : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [mul_one] using hdiff)
    have hcomap : Ideal.comap ι (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    have hone_mem : (1 : 𝓞 F) ∈ 𝔭 := by
      rw [← hcomap, Ideal.mem_comap, map_one]
      simpa only [pow_one] using hone
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 hone_mem)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range tr := htop ▸ Submodule.mem_top
  exact ⟨z, (trace_spec z).symm.trans (congrArg ι hz)⟩

end Formalism.HermitianLattices.Ext.L3
