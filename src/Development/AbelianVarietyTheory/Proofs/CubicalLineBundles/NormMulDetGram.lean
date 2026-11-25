module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIrreducibleGeneralizations
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TopDifferential

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {F : DualNumber R →+* DualNumber R'}
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_mul, h₁, h₁, h₂, ← e]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem det_gram {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 * Hm.det.re := by
  have e : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)) =
      (Real.pi : ℂ) • (W * (Hm * W.conjTranspose)).transpose := rfl
  rw [e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Fintype.card_fin, mul_left_comm W.det, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    mul_comm Hm.det, ← _root_.mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

end GlobalTheory.CM.TopDifferential
