module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Classical

namespace GlobalTheory.BadOrth




theorem finCosets : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → ∀ k : ℕ, 0 < k → ∃ C : Finset (WO S T), (∀ c ∈ C, IsHalf a c) ∧ ∀ s : WO S T, IsHalf a s → k • s ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → ∃ c ∈ C, ∃ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf a u ∧ s = c + k • u := by
  intro D S T ΛS ΛT hS hT a ha k hk
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) (k * k)
    (Nat.mul_pos hk hk)
  have half' : ∀ {b : AE D} {u : WO S T}, IsHalf b u ↔ b • u = u := fun {b u} =>
    (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)
  let r : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)
  have hrk : r * (k : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  have hrkz : ∀ z : WO S T, r • (k • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D) k z, smul_smul, hrk, one_smul]
  refine ⟨hR.toFinset.image (fun z => a • (r • z)), fun c hc => ?_, fun s hs hks => ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hc
    exact half'.2 (by rw [smul_smul, ha])
  · obtain ⟨z, hz, u, hu, hzu⟩ := hRm (k • s) hks
    refine ⟨a • (r • z), Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hz), a • u,
      PlaceModelSum.idem_smul_latO ha hu, half'.2 (by rw [smul_smul, ha]), ?_⟩
    calc s = a • (r • (k • s)) := by rw [hrkz, half'.1 hs]
      _ = a • (r • z) + k • (a • u) := by rw [hzu, smul_add, smul_add, mul_smul, hrkz, smul_comm a k u]




open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum




end GlobalTheory.BadOrth
