module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.MirTower

section Adelic

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem discrete_of_le_range {Γ : Subgroup (GA E a)} (hΓ : Γ ≤ (ratGL E a).range) : DiscreteTopology Γ := by
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hW : IsOpen (⋂ i : Fin a, ⋂ k : Fin a,
      {g : Γ | (g : GA E a).val i k - (1 : Matrix (Fin a) (Fin a) (Ad E)) i k ∈ V}) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hVo.preimage (((Units.continuous_val.comp continuous_subtype_val).matrix_elem i k).sub continuous_const)
  convert hW using 1
  ext ⟨g, hg⟩
  obtain ⟨γ, rfl⟩ := hΓ hg
  simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h i k
    have h1 : ratGL E a γ = 1 := congrArg Subtype.val h
    rw [h1, Units.val_one, sub_self]
    exact hV0
  · intro h
    have h1 : γ = 1 := by
      ext i k
      have h2 := h i k
      have e : (ratGL E a γ).val i k - (1 : Matrix (Fin a) (Fin a) (Ad E)) i k =
          algebraMap E (Ad E) (γ.val i k - (1 : Matrix (Fin a) (Fin a) E) i k) := by
        rw [map_sub, Matrix.one_apply, Matrix.one_apply]
        congr 1
        split_ifs <;> simp
      rw [e] at h2
      exact sub_eq_zero.1 (h0 _ (hVU h2))
    subst h1
    exact Subtype.ext (map_one _)

end Adelic

end GlobalTheory.MirTower
