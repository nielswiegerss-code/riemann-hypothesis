module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin

@[expose] public section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_admissible_of (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (μ : Fin n → ℝ)
    (hkhw : ∃ k : ℕ, ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ layer ε E V k)
    (hkfin : ∀ S : Submodule ℂ H, S ≤ closGen E V → FiniteDimensional ℂ S →
      (∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S) → S ≤ (genSub E V).map D.subtype) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) := by
  have hE := hD.glRep
  obtain ⟨k, hk⟩ := hkhw
  have hLf : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hV.1 k
  have hLK := kStable_of_isKStableSub hσ hD (layer ε E V k) hLf (layer_kStable hE hV.2.1 k)
  have hMf : FiniteDimensional ℂ ((layer ε E V k).map D.subtype) := Module.Finite.map _ _
  have hle : (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) ≤
      (layer ε E V k).map D.subtype := by
    refine sSup_le fun S hSmem => ?_
    obtain ⟨hS, hST⟩ := hSmem
    obtain ⟨hSf, hSK, hirr, -, -⟩ := id hST
    have hSM := hkfin S hS hSf (fun g hg x hx => hSK g hg x hx)
    have hSD : S ≤ D := hSM.trans (Submodule.map_subtype_le _ _)
    obtain ⟨w, hwS, hw0, hwμ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
    have hwg : w ∈ genSub E V := by
      obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
      have : y = w := Subtype.ext hyw
      exact this ▸ hy
    have hwL := hk w hwg hwμ
    have hS'K : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ (layer ε E V k).map D.subtype) := by
      intro g hg v hv
      refine ⟨hSK g hg v hv.1, ?_⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
      obtain ⟨z, hz, hzeq⟩ := hLK g hg y hy
      exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
    rcases hirr _ inf_le_left hS'K with h0 | hEq
    · exfalso
      have hmem : (w : H) ∈ S ⊓ (layer ε E V k).map D.subtype :=
        ⟨hwS, Submodule.mem_map_of_mem hwL⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hw0 (Subtype.ext hmem)
    · rw [← hEq]
      exact inf_le_right
  exact Submodule.finiteDimensional_of_le hle

theorem data_admissible [CompleteSpace H] (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (μ : Fin n → ℝ) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) :=
  data_admissible_of hσ hD hV μ
    (khw_mem_layer hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap μ)
    (data_kfin_le hgap hσ hD hV hc hVK)

end ReciprocityTheory.ChartRestriction.DS
