module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

namespace Formalism.MainNotions.TwOe

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']

private theorem exists_ne_zero_addVal_algebraMap_eq_mul (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ y : R, IsDiscreteValuationRing.addVal R' (algebraMap R R' y) =
      (e : ℕ∞) * IsDiscreteValuationRing.addVal R y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have h0 : algebraMap R R' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap R R' ϖ) := by
    intro hu
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
      (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal R')
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hmem : ϖ ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := by
      rw [heq]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hu
  have he : e ≠ 0 := by
    rintro rfl
    apply hnu
    rw [hw, pow_zero, mul_one]
    exact w.isUnit
  refine ⟨e, he, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, AddValuation.map_zero, AddValuation.map_zero, ENat.mul_top (by exact_mod_cast he)]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    rw [IsDiscreteValuationRing.addVal_def y u hϖ n hu]
    have hy' : algebraMap R R' y =
        ↑(Units.map (algebraMap R R' : R →* R') u * w ^ n) * ϖ' ^ (e * n) := by
      rw [hu, map_mul, map_pow, hw]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass]
      ring
    rw [IsDiscreteValuationRing.addVal_def _ _ hϖ' _ hy']
    push_cast
    ring

theorem nval_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) (x : R) :
    nval R' l (algebraMap R R' x) = nval R l x := by
  obtain ⟨e, he, hE⟩ := exists_ne_zero_addVal_algebraMap_eq_mul hinj
  simp only [nval]
  rw [hE x, ← map_natCast (algebraMap R R') l, hE]
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

end Formalism.MainNotions.TwOe
