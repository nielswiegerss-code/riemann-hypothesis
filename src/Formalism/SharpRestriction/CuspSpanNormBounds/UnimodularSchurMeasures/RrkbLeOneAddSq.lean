module

import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

theorem rrkb_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  apply _root_.PositivityTheory.Rg.BcB.E2.P.Locint.enorm_le_one_add_sq <;> assumption

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ] in
theorem rrkb_sq_fin (f : Lp ℂ 2 (μ.restrict D)) : ∫⁻ y in D, ‖(f : G → ℂ) y‖ₑ ^ 2 ∂μ ≠ ∞ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    (Lp.eLpNorm_lt_top f)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h.ne

theorem rrkb_lint (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G)
    {F : G → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F x ∂μ := by
  obtain ⟨h1, h2⟩ := rr_map h g
  calc ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F (rr_rep (Γ : Set G) D (x * g)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x hx
        rw [hx]
    _ = ∫⁻ y, F y ∂(Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) :=
        (lintegral_map' hF.aemeasurable h1).symm
    _ = ∫⁻ x in D, F x ∂μ := by rw [h2]

end Formalism.MainNotions.LeviCoordinates
