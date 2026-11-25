module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable

@[expose] public section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}

variable {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem rreg_mem_Hlam (_hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ v₀, rreg ε g x ∈ Hlam ε Ψ v₀ :=
  DS.rreg_mem_Hlam_of hP hv₀

theorem sigLam_coe (_hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (x : Hlam ε Ψ v₀) :
    ((sigLam ε Ψ v₀ g x : Hlam ε Ψ v₀) : L2 ε) = rreg ε g x :=
  DS.sigLam_coe_of hP hv₀ hg x

theorem sigLam_isURepOn (_hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : IsURepOn (UJset ε) (sigLam ε Ψ v₀) :=
  DS.sigLam_isURepOn_of hP hv₀

theorem sigLam_irred (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ v₀) :=
  DS.sigLam_irred_of hP hv₀
    (ReciprocityTheory.ChartRestriction.DS.G2.rigid_irred hgap (rreg_isURepOn ε)
      (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
      (datumV_kStable hP v₀))

theorem Hlam_nontrivial (_hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Nontrivial (Hlam ε Ψ v₀) :=
  DS.Hlam_nontrivial_of hP hv₀

theorem subtype_sigLam (_hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, (Hlam ε Ψ v₀).subtype (sigLam ε Ψ v₀ g x) =
      rreg ε g ((Hlam ε Ψ v₀).subtype x) :=
  DS.subtype_sigLam_of hP hv₀

theorem sigLam_lowK (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) (lowKSubLam ε Ψ v₀) ∧
      ∀ S : Submodule ℂ (Hlam ε Ψ v₀), Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) S →
        S = lowKSubLam ε Ψ v₀ := by
  have hσ := ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hV := ReciprocityTheory.ChartRestriction.DS.datumV_isKIrrHW hP hv₀
  have hc := ReciprocityTheory.ChartRestriction.DS.datumV_casimir hP v₀
  have hVK := ReciprocityTheory.ChartRestriction.DS.datumV_kStable hP v₀
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.coe_injective
  have hint := ReciprocityTheory.ChartRestriction.DS.G2.subtype_sigLam hgap hP hv₀
  refine ⟨?_, ?_⟩
  · rw [ReciprocityTheory.ChartRestriction.DS.isKTypeOf_map_iff (Hlam ε Ψ v₀).subtype hinj hint,
      ReciprocityTheory.ChartRestriction.DS.map_lowKSubLam]
    exact ReciprocityTheory.ChartRestriction.DS.isKTypeOf_of_isKIrrHW hσ hD hV hVK
      (fun μ x hx hx0 hμ => ReciprocityTheory.ChartRestriction.DS.datumV_weight_le hP hv₀ hx hx0 hμ)
  · intro S hS
    rw [ReciprocityTheory.ChartRestriction.DS.isKTypeOf_map_iff (Hlam ε Ψ v₀).subtype hinj hint] at hS
    have h := ReciprocityTheory.ChartRestriction.DS.G2.data_lowK_eq hgap hσ hD hV hc hVK (S.map (Hlam ε Ψ v₀).subtype)
      (ReciprocityTheory.ChartRestriction.DS.map_subtype_le_closGen S) hS
    rw [← ReciprocityTheory.ChartRestriction.DS.map_lowKSubLam] at h
    exact Submodule.map_injective_of_injective hinj h

theorem sigLam_kType_bounds (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {μ : Fin n → ℝ} (S : Submodule ℂ (Hlam ε Ψ v₀))
    (hS : Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ ∧
      ∀ h : ℝ, GapAtLeast ε lam h → 2 * (n : ℝ) < h → μ ≠ lowK ε lam →
        casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  have hσ := ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hV := ReciprocityTheory.ChartRestriction.DS.datumV_isKIrrHW hP hv₀
  have hc := ReciprocityTheory.ChartRestriction.DS.datumV_casimir hP v₀
  have hVK := ReciprocityTheory.ChartRestriction.DS.datumV_kStable hP v₀
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.coe_injective
  have hint := ReciprocityTheory.ChartRestriction.DS.G2.subtype_sigLam hgap hP hv₀
  rw [ReciprocityTheory.ChartRestriction.DS.isKTypeOf_map_iff (Hlam ε Ψ v₀).subtype hinj hint] at hS
  have hle := ReciprocityTheory.ChartRestriction.DS.map_subtype_le_closGen S
  exact ⟨ReciprocityTheory.ChartRestriction.DS.G2.data_vogan hgap hσ hD hV hc hVK _ hle hS,
    fun h hh hbig hμ => ReciprocityTheory.ChartRestriction.DS.G2.data_casValK_gap hgap hσ hD hV hc hVK hh hbig _ hle hS hμ⟩

end ReciprocityTheory.ChartRestriction.DS.G2
