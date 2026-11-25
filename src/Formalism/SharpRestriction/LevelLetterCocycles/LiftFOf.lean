module

public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace

@[expose] public section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem lc_pow (I : BaseId W) (e : ℕ) :
    I.Bs.lc ^ e = PowerSeries.C (((PD.p : ℕ) : O) ^ e) := by
  unfold Formalism.ExponentWindows.E.Base.lc
  rw [I.ℓ_eq, map_pow]

theorem map_mem_Z1DΔ (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) ∈ W.wachCocyclesDelta T₂ := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  show (W.map F x, W.map F y) ∈ W.wachCocyclesDelta T₂
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Formalism.BasicNotions.herrCocycles, Submodule.mem_inf,
    LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply, LinearMap.prodMap_apply] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, fun d hd => ?_⟩
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, ← map_neg, ← map_add (f := _), h1, map_zero]
  · have h3 := h2 d hd
    rw [← W.map_γ, ← W.map_γ]
    simp only [Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at h3 ⊢
    exact ⟨by rw [h3.1], by rw [h3.2]⟩

end Formalism.MainNotions.WachCoordinates.Br
