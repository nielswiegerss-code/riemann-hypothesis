module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels

namespace GlobalTheory.SerRatRay

theorem isRat_const_mul {D : D7} (T : CoreJ D) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (C : Cover T ((i : ℕ) + 1) σ) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) (c : ℂ)
    (h : IsRat T i hV C κ φ) (hc : c ∈ C.σ₂.fieldRange) : IsRat T i hV C κ (fun g => c * φ g) := by
  obtain ⟨φ', ⟨f₂, hf₂, rfl⟩, rfl⟩ := h
  obtain ⟨c', rfl⟩ := RingHom.mem_fieldRange.1 hc
  refine ⟨C.rd (wtA κ) (c' • f₂), ⟨c' • f₂, ⟨(sec _ _ _ _).smul_mem c' hf₂.1, ?_⟩, rfl⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hf₂.2
  · funext g
    simp only [castDict, Cover.rd, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end GlobalTheory.SerRatRay
