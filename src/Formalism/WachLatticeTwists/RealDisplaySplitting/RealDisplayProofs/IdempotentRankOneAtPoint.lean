module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingObjectsOfMatrixData
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement

@[expose] public section

open Finset Classical

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
  {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
  {D : RingData O X d G t bl}

theorem deltaO_eq (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    D.δO = ∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) := by
  obtain ⟨-, -, -, -, -, hrr, -⟩ := hD
  have h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
      ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π') := by
    show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _
    unfold RingData.δ
    rw [map_prod]; rfl
  rw [h2]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioo] at hi
  rw [hrr 0 (by omega), hrr i hi.2]
  simp

theorem idempotent_rank_one_at_point (hI : IdemHyp O T r₀ π bl eB e₁) (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    ((D.ρk 0 D.e₁).map (algebraMap O (FractionRing O))).rank = 1 := by
  obtain ⟨-, -, -, -, hpπ, -, -, -, -, -, -, -, -, he1, -, -, hρπ, hρk, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, -, hrk1, -, he1π⟩ := hI
  have h2 : (D.ρk 0 D.e₁).map (algebraMap O (FractionRing O)) =
      ((e₁ π).map (algebraMap O (FractionRing O))).toSquareBlock bl 0 := by
    rw [← hρk]
    ext i j
    have h := congrFun (congrFun (hρπ D.e₁) i.1) j.1
    rw [he1, hpπ] at h
    exact h
  rw [h2, rank_block bl 0 _ (fun a b hab => by
    show algebraMap O (FractionRing O) (e₁ π a b) = 0
    rw [he1π a b hab, map_zero])]
  exact hrk1 π

end Formalism.RepresentationBoundsCohomology.SF
