module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem algHom_coe_eq_aeval {O T : Type*} [CommRing O] [CommRing T] [Algebra O T]
    (ρ : PowerSeries O →ₐ[O] T) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.aeval_algHom_apply]
  rfl

theorem constantCoeff_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (x : PowerSeries S) (r : Polynomial O) :
    constantCoeff (Polynomial.aeval x r) = Polynomial.aeval (constantCoeff x) r := by
  exact Polynomial.hom_eval₂ _ _ _ _

theorem rhoCompl : RhoComplStatement := by
  intro O LL S _ _ _ _ _ _ _ _ _ _ _ P hP ρ hunit hann k a ha
  obtain ⟨w, hw⟩ := hunit
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have hne : PowerSeries.map (residue O) (P : PowerSeries O) ≠ 0 := by
      rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]
      exact (hP.monic.map _).ne_zero
    obtain ⟨q, r, _, rfl⟩ := exists_isWeierstrassDivision a hne
    obtain ⟨b, hb⟩ := (Polynomial.map_dvd_map _ (IsFractionRing.injective O LL) hP.monic).1
      (hann _ (by simpa [hw, algHom_coe_eq_aeval, constantCoeff_aeval] using
        X_pow_dvd_iff.1 ha 0 k.succ_pos))
    subst hb
    rw [Polynomial.coe_mul, ← mul_add, pow_succ'] at *
    exact mul_dvd_mul_left _ (ih _ (by
      simpa [hw, mul_assoc, IsLeftRegular.dvd_cancel_left (X_mul_injective (R := S))] using ha))

end LevelStatements.Lv
