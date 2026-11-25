module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.GrowthIntegrals.BeBessel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix
import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace PI.WBL.S5

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.Cv PI.WBL.Cv.BeC

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dsigW_eq (σ : Mx k r → (H →L[ℂ] H)) (W : List (Mx k r)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v) =
      PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ W v)
    rw [ih]
    rfl

theorem cwCont_conv {Wp : Type} [NormedAddCommGroup Wp] {σ : Mx k r → (H →L[ℂ] H)} {B : H → Wp}
    (h : Formalism.MainNotions.S.IsCWCont (k := k) (r := r) σ B) : PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  obtain ⟨C, Ws, hW, hB⟩ := h
  refine ⟨C, Ws, hW, fun v hv => ?_⟩
  have h1 := hB v hv
  simp only [dsigW_eq] at h1
  exact h1

theorem psiConst : Formalism.FourierDecayAlt.ThreeDimData.PsiConst := by
  intro k r z c g
  simp only [Formalism.QuantumDeterminants.psi, PI.BesselMapUniq.psiGen, ← Finset.mul_sum]
  rfl

end PI.WBL.S5
