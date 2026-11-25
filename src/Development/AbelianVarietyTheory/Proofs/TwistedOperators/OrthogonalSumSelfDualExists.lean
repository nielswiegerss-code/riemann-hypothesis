module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
open GlobalTheory.Doubling GlobalTheory.AdelicU

namespace GlobalTheory.Twist.OrthSum

variable {D : D7}

theorem pair_hsum (V W : HSp D) (x y : Fin (hsum V W).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (hsum V W).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * V.gram i j * y (finSumFinEquiv (Sum.inl j))) +
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * W.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hsum]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Doubling.blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

theorem selfDual_hsum {V W : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') :
    IsSelfDualC (hsum V W) (sumLat finSumFinEquiv L L') := by
  have hsumLat : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L') := by
    let φ : ((Fin V.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (V.rank + W.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L' =
        (L.prod L').map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL'.1.fg).map _)
  refine ⟨hsumLat, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL'.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ + b₂, ?_⟩
    rw [pair_hsum]
    push_cast
    linear_combination hb₁ + hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL'.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero] at hb
      exact ⟨b, hb⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add] at hb
      exact ⟨b, hb⟩

end GlobalTheory.Twist.OrthSum
