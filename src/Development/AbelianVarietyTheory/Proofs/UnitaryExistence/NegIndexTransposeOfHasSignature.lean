module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.SumEmbeddingsEq
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict


open Matrix in
theorem negIndex_transpose_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : GlobalTheory.Inertia.negIndex Jᵀ = q ∧ J.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have hd : Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [← fromBlocks_diagonal, Formalism.UG.Jpq]
    congr 1
    rw [← diagonal_neg]
    rfl
  have hPd : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det ≠ 0 := P.det_ne_zero
  constructor
  · have ht := congrArg Matrix.transpose hP
    rw [hd, diagonal_transpose, transpose_mul, transpose_mul, Formalism.UG.cT, transpose_transpose,
      ← Matrix.mul_assoc] at ht
    have h1 := GlobalTheory.Inertia.negIndex_eq_card_of_congr_diagonal hPd ht
    have h2 : (J.reindex e e)ᵀ = Jᵀ.submatrix e.symm e.symm := rfl
    rw [h2, GlobalTheory.Inertia.negIndex_submatrix_equiv] at h1
    rw [h1, Finset.card_filter, Fintype.sum_sum_type]
    simp [not_lt.2 (zero_le_one' ℝ)]
  · intro h0
    have h1 := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_reindex_self, h0, hd, det_diagonal] at h1
    simp only [mul_zero, zero_mul] at h1
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h1.symm
    rcases k with k | k <;> simp

variable {D : D7}

theorem cc_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (a b : Fin r) :
    cc (gmW V hr a b) = gmW V hr b a := by
  subst hr
  show IsCMField.complexConj D.host.E (-(V.hT (V.frame b) (V.frame a))) = -(V.hT (V.frame a) (V.frame b))
  rw [map_neg]
  exact congrArg Neg.neg (LinearMap.isSymm_def.1 V.herm (V.frame b) (V.frame a))

theorem herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm) =
      -V.hT y x := by
  subst hr
  rw [Formalism.L2.Pj.DatLin.sesq_repr V.hT V.frame y x, Finset.sum_comm, herm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show V.frame.repr x a * (-(V.hT (V.frame b) (V.frame a))) * star (V.frame.repr y b) = _
  ring

theorem trace_herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    Algebra.trace ℚ D.host.E (D.host.xi0 *
      herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm)) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT x y) := by
  rw [herm_gmW, ← trace_cc D (D.host.xi0 * V.hT x y), map_mul (IsCMField.complexConj D.host.E), conj_xi0_alt]
  have h : IsCMField.complexConj D.host.E (V.hT x y) = V.hT y x := LinearMap.isSymm_def.1 V.herm x y
  rw [h, mul_neg, neg_mul]

theorem posIndex_gmW (V : HSp D) (hV : V.SigOK) {r : ℕ} (hr : V.rank = r) (τ : D.host.E →+* ℂ) :
    GlobalTheory.Inertia.posIndex ((gmW V hr).map τ) = (V.sig τ).2 ∧ (gmW V hr).det ≠ 0 := by
  subst hr
  obtain ⟨h1, h2⟩ := negIndex_transpose_of_hasSignature (hV τ)
  have e : gmW V rfl = -V.gram.transpose := rfl
  constructor
  · rw [← h1, ← GlobalTheory.Inertia.posIndex_neg, e]
    congr 1
    ext a b
    simp
  · rw [e, Matrix.det_neg, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ (by simp)) fun h0 => h2 ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.RecDict
