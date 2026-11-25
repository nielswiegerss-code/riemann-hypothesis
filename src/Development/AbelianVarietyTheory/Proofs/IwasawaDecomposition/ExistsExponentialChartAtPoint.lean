module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.LogCh

theorem unitOn_injective : Function.Injective (unitOn (R := ℂ)) := by
  intro c c' h
  ext
  have := congrArg (fun u : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (u : Γ(Sp ℂ, ⊤))) h
  simpa [unitOn] using this

theorem unitOn_one : unitOn (1 : ℂˣ) = 1 := by simp [unitOn]

theorem map_nsmul_eq_pow {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) (N : ℕ) (u : Fin g → ℂ) : f ((N : ℂ) • u) = f u ^ N := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Nat.cast_succ, add_smul, one_smul, hf, ih, pow_succ]

theorem pow_eq_one_of_map {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) {N : ℕ} (hN : 0 < N) {v : Fin g → ℂ} (hv : f v = 1) : f ((N : ℂ)⁻¹ • v) ^ N = 1 := by
  rw [← map_nsmul_eq_pow f hf h0, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_smul, hv]

end GlobalTheory.ShFam.Hor.LogCh
