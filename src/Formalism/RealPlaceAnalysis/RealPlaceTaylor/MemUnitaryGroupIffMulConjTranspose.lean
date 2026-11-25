module

public import Formalism.RealPlaceAnalysis.Complexify
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Lemma

@[expose] public section

open Matrix

namespace Formalism.REAL

lemma f1alg_isUnit_J {n : ℕ} (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩

lemma f1alg_inv_J {n : ℕ} (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_left_inv (Jm_mul_self ε)

lemma f1alg_JJ_left {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma f1alg_comm_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = Jm ε * A ↔ Jm ε * A * Jm ε = A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = (Jm ε * A * Jm ε) * Jm ε := by rw [h]
      _ = Jm ε * A := by rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]

lemma f1alg_anti_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = -(Jm ε * A) ↔ Jm ε * A * Jm ε = -A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_neg, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = -(Jm ε * A * Jm ε) * Jm ε := by rw [h, neg_neg]
      _ = -(Jm ε * A) := by rw [Matrix.neg_mul, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]

lemma f1alg_inG_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ Xᴴ = -(Jm ε * X * Jm ε) := by
  unfold inG
  constructor
  · intro h
    have h' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h', Matrix.neg_mul]
  · intro h
    rw [h, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, neg_add_cancel]

lemma f1alg_inK_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  unfold inK
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩

lemma mem_cartanP_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inP ε X ↔ Xᴴ = X ∧ X * Jm ε = -(Jm ε * X) := by
  unfold inP
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩

lemma f1alg_exp_inUJ {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inUJ
  have hY' : Yᴴ = Jm ε * (-Y) * Jm ε := by
    rw [(f1alg_inG_iff ε Y).mp hY, Matrix.mul_neg, Matrix.neg_mul]
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩
  have hconj : NormedSpace.exp (Jm ε * (-Y) * Jm ε) = Jm ε * NormedSpace.exp (-Y) * Jm ε :=
    Matrix.exp_units_conj U (-Y)
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hY', hconj]
  simp only [Matrix.mul_assoc]
  rw [f1alg_JJ_left, hinv, Matrix.mul_one]

theorem indefinite_unitary_closed : UJClosed := by
  intro n ε
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exp_indefinite_unitary_holds : ExpUJ := by
  intro n ε X hX t
  apply f1alg_exp_inUJ
  unfold inG at hX ⊢
  have hs : ((t : ℂ) • X)ᴴ = (t : ℂ) • Xᴴ := by
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem indefinite_unitary_inv_closed : UJInv := by
  intro n ε g h
  have h2 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_self]
  exact ⟨mul_eq_one_comm.mp h2, h2⟩

theorem one_parameter_subgroup_holds : OneParam := by
  intro n X s t
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem parabolic_character_holds : PChar := by
  intro n ε X
  exact ⟨mem_cartanP_iff ε X, fun h => (f1alg_anti_iff ε X).mp h.2⟩

lemma f1alg_unit_iff {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ gᴴ * g = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

lemma mem_unitaryGroup_iff_mul_conjTranspose {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ g * gᴴ = 1 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]

theorem maximal_compact_facts : KFacts := by
  intro n ε

  have h1 : ∀ g ∈ Kset ε, inUJ ε g := by
    rintro g ⟨hu, hc⟩
    unfold inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, (f1alg_unit_iff g).mp hu, Matrix.one_mul]

  have h5 : ∀ g, g ∈ Kset ε ↔ (inUJ ε g ∧ g ∈ Matrix.unitaryGroup (Fin n) ℂ) := by
    intro g
    constructor
    · intro hg
      exact ⟨h1 g hg, hg.1⟩
    · rintro ⟨hJ, hu⟩
      refine ⟨hu, ?_⟩
      unfold inUJ at hJ
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [(mem_unitaryGroup_iff_mul_conjTranspose g).mp hu, Matrix.one_mul]
  refine ⟨h1, ?_, ?_, ?_, h5⟩
  ·
    have hcl : IsClosed (Kset ε) := by
      have : Kset ε = {g | gᴴ * g = 1} ∩ {g | g * Jm ε = Jm ε * g} := by
        ext g
        simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, f1alg_unit_iff]
      rw [this]
      exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id))
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      exact entry_norm_bound_of_unitary hg.1 i j
    exact IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _) hcl hsub
  · refine ⟨?_, rfl⟩
    rw [f1alg_unit_iff, Jm_conjTranspose, Jm_mul_self]
  · rintro X ⟨hG, hc⟩
    have hX : Xᴴ = -X := ((f1alg_inK_iff ε X).mp ⟨hG, hc⟩).1
    refine ⟨?_, ?_⟩
    · rw [f1alg_unit_iff, ← Matrix.exp_conjTranspose, hX,
        ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
        NormedSpace.exp_zero]
    · exact ((Commute.exp_right (show Commute (Jm ε) X from hc.symm)).symm).eq

end Formalism.REAL
