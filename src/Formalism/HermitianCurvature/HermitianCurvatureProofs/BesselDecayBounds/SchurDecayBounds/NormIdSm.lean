module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.OpNormLeOneOfIso
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

theorem gN_lshift {x y : Mx k r} (hx : x ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) {a : ℝ} (ha : 0 ≤ a) :
    Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-a) ≤ Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by
  have hUnit : IsUnit y.det := by
    have h1 : yᴴ * Hpk k r * y = Hpk k r := hy
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH := Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r
    have h3 : (yᴴ).det * y.det = 1 := by
      apply hH.mul_left_cancel
      calc (Hpk k r).det * ((yᴴ).det * y.det) = (yᴴ).det * (Hpk k r).det * y.det := by ring
        _ = (Hpk k r).det := h2
        _ = (Hpk k r).det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((yᴴ).det) (by rw [mul_comm]; exact h3)
  have hNI := Formalism.MainNotions.InverseNormDecayBounds.normInvP k r
  have hgx : 1 ≤ Formalism.FourierDecayAlt.B.gN x := (hNI.1 x hx).2
  have hgy : 1 ≤ Formalism.FourierDecayAlt.B.gN y := (hNI.1 y hy).2
  have hsub : Formalism.FourierDecayAlt.B.gN x ≤ Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := by
    have := hNI.2 y (y⁻¹ * x)
    rwa [Matrix.mul_nonsing_inv_cancel_left _ _ hUnit] at this
  have hlow : Formalism.FourierDecayAlt.B.gN x / Formalism.FourierDecayAlt.B.gN y ≤ Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := by
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_comm (Formalism.FourierDecayAlt.B.gN y) (Formalism.FourierDecayAlt.B.gN (y⁻¹ * x))]
  have h0x : 0 < Formalism.FourierDecayAlt.B.gN x := by linarith
  have h0y : 0 < Formalism.FourierDecayAlt.B.gN y := by linarith
  calc Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-a) ≤ (Formalism.FourierDecayAlt.B.gN x / Formalism.FourierDecayAlt.B.gN y) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (div_pos h0x h0y) hlow (by linarith)
    _ = Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by
        rw [Real.div_rpow h0x.le h0y.le, Real.rpow_neg h0y.le a, div_inv_eq_mul, mul_comm]

theorem decBd_mono {σ : Mx k r → (H →L[ℂ] H)} {a b : ℝ} {u' u : H} (hab : b ≤ a) (h : DecBd σ a u' u) :
    DecBd σ b u' u := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun x hx => ?_⟩
  have hg : 1 ≤ Formalism.FourierDecayAlt.B.gN x := ((Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1 x hx).2
  calc ‖⟪u', σ x u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a) := hC x hx
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN x ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hg (by linarith)) (le_max_right _ _)

theorem decBd_left {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (hSg : Cv.SigU σ) {w0 u : H} {b : ℝ} (hb : 0 ≤ b) (h : DecBd σ b w0 u)
    {y : Mx k r} (hy : y ∈ UH (Hpk k r)) : DecBd σ b (σ y w0) u := by
  obtain ⟨C, hC⟩ := h
  have hNI := Formalism.MainNotions.InverseNormDecayBounds.normInvP k r
  have hUnit : ∀ g ∈ UH (Hpk k r), IsUnit g.det := by
    intro g hg
    have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH := Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r
    have h3 : (gᴴ).det * g.det = 1 := by
      apply hH.mul_left_cancel
      calc (Hpk k r).det * ((gᴴ).det * g.det) = (gᴴ).det * (Hpk k r).det * g.det := by ring
        _ = (Hpk k r).det := h2
        _ = (Hpk k r).det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((gᴴ).det) (by rw [mul_comm]; exact h3)
  have hmul : ∀ a ∈ UH (Hpk k r), ∀ c ∈ UH (Hpk k r), a * c ∈ UH (Hpk k r) := by
    intro a ha c hc
    have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
    have hc' : cᴴ * Hpk k r * c = Hpk k r := hc
    show (a * c)ᴴ * Hpk k r * (a * c) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc cᴴ * aᴴ * Hpk k r * (a * c) = cᴴ * (aᴴ * Hpk k r * a) * c := by simp only [mul_assoc]
      _ = Hpk k r := by rw [ha', hc']
  have hinv : y⁻¹ ∈ UH (Hpk k r) := by
    have hd := hUnit y hy
    have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
    show (y⁻¹)ᴴ * Hpk k r * y⁻¹ = Hpk k r
    calc (y⁻¹)ᴴ * Hpk k r * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) * y⁻¹ := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
      _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  refine ⟨max C 0 * Formalism.FourierDecayAlt.B.gN y ^ b, fun x hx => ?_⟩
  have hyx : y⁻¹ * x ∈ UH (Hpk k r) := hmul _ hinv _ hx
  have hsx : σ x = (σ y).comp (σ (y⁻¹ * x)) := by
    rw [← hSg.2.1 y hy _ hyx, Matrix.mul_nonsing_inv_cancel_left _ _ (hUnit y hy)]
  let li : H →ₗᵢ[ℂ] H := { toLinearMap := (σ y : H →ₗ[ℂ] H), norm_map' := hSg.2.2 y hy }
  have hin : ⟪σ y w0, σ x u⟫_ℂ = ⟪w0, σ (y⁻¹ * x) u⟫_ℂ := by
    rw [hsx, ContinuousLinearMap.comp_apply]
    exact li.inner_map_map w0 (σ (y⁻¹ * x) u)
  have hg1 : 1 ≤ Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := (hNI.1 _ hyx).2
  rw [hin]
  calc ‖⟪w0, σ (y⁻¹ * x) u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-b) := hC _ hyx
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-b) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * (Formalism.FourierDecayAlt.B.gN y ^ b * Formalism.FourierDecayAlt.B.gN x ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_lshift hx hy hb) (le_max_right _ _)
    _ = max C 0 * Formalism.FourierDecayAlt.B.gN y ^ b * Formalism.FourierDecayAlt.B.gN x ^ (-b) := by ring

theorem decBd_DD_left {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (hSg : Cv.SigU σ) {w0 u : H} {b : ℝ} (hb : 0 ≤ b) (h : DecBd σ b w0 u) :
    ∀ v ∈ DDsp σ w0, DecBd σ b v u := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact decBd_left hds hSg hb h hg
  | zero => exact Formalism.MainNotions.InverseNormDecayBounds.decBd_zero_left σ b u
  | add x y _ _ hx hy => exact Formalism.MainNotions.InverseNormDecayBounds.decBd_add_left hx hy
  | smul c x _ hx => exact Formalism.MainNotions.InverseNormDecayBounds.decBd_smul_left c hx

end PI.WBL.NIS
