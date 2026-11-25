module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.RingTheory.PicardGroup

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise TensorProduct
open IsDedekindDomain NumberField

namespace GlobalTheory.FinPl

theorem CMAdele_eq_zero_of_infinite_and_finite_components_zero (D : D7) (a : AE D) (h0 : infPart D a = 0) (hw : ∀ w : Pl D, compAt D w a = 0) :
    a = 0 := by
  first | exact _root_.GlobalTheory.FinPlLoc.eq_zero_of_comp | exact @_root_.GlobalTheory.FinPlLoc.eq_zero_of_comp | apply _root_.GlobalTheory.FinPlLoc.eq_zero_of_comp <;> assumption

theorem mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere (D : D7) (P : Pl D → Prop) (a : AE D) :
    a ∈ idAt D P ↔ infPart D a = 0 ∧ ∀ w : Pl D, ¬ P w → compAt D w a = 0 := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem placeIdempotent_infinite_and_finite_components (D : D7) (v : Pl D) (ε : AF D.host.F) (α : Af D.host.F)
    (hε : ε = pairA D.host.F 0 α) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, hε]
    exact TensorProduct.zero_tmul _ _
  · rw [ha]
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hε]
    rfl

theorem mem_supportedAtPlace_iff_placeIdempotent_mul (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0) (c1 : compAt D v e = 1)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) : a ∈ idAt D (· = v) ↔ e * a = a := by
  constructor
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
    obtain ⟨ha0, haw⟩ := ha
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul]
      by_cases h : w = v
      · subst h; rw [c1, one_mul, sub_self]
      · rw [haw w h, mul_zero, sub_zero]
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw' => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, c0 w hw', zero_mul]

theorem placeIdempotent_mul_supportedOffPlace_eq_zero (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) (ha : a ∈ idAt D (· ≠ v)) : e * a = 0 := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  obtain ⟨ha0, haw⟩ := ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · rw [haw w (fun h' => h' h), mul_zero]
    · rw [c0 w h, zero_mul]

theorem placeIdem_acts : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  intro D v ε ⟨α, hε, hv, hw⟩
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have c1 : compAt D v (algebraMap (AF D.host.F) (AE D) ε) = 1 := by
    rw [hc, hv]; rfl
  have c0 : ∀ w : Pl D, w ≠ v → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    intro w h; rw [hc, hw w h, TensorProduct.zero_tmul]
  exact ⟨mem_supportedAtPlace_iff_placeIdempotent_mul D v _ h0 c1 c0, placeIdempotent_mul_supportedOffPlace_eq_zero D v _ h0 c0⟩

end GlobalTheory.FinPl
