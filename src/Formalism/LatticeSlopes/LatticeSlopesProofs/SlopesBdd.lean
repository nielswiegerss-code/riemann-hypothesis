module

public import Formalism.LatticeSlopes.CovolAntiSameRank
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Module Submodule

namespace Formalism.F

universe u

theorem gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem slopesBdd_of (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  have := hL
  let e := Module.finBasis ℤ L
  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact PiLp.ext (Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis L e) _ hx)
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro _ ⟨N, hNL, hN0, rfl⟩
  have hN : DiscreteTopology N := discreteTopology_of_le hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := fun j => by
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simpa only [S, w, M, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
      Int.cast_smul_eq_zsmul] using h
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := fun c => by
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by simp [map_sum, hSw]
    simpa [h1, dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet
  have hwli : LinearIndependent ℝ w :=
    LinearIndependent.of_comp S (by
      have hcompSw : S ∘ w = fun j => (f j : E) := funext hSw
      rw [hcompSw]
      exact linearIndependent_coe_basis N f)
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    exact_mod_cast (show (0 : ℤ) < (M.transpose * M).det by exact_mod_cast hwpos)
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℤ) (M := N)
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det
  have hgpos : 0 < g := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis N f)).det_pos
  have hlog := Real.log_le_log one_pos (hd1.trans hdet)
  rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at hlog
  have hcov : covol N = Real.sqrt g := covol_eq_gram E N _ f
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  push_cast at hlog
  linarith

end Formalism.F
