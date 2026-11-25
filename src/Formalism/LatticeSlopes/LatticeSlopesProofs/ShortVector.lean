module

public import Formalism.LatticeSlopes.CovolAntiSameRank
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open Module Submodule MeasureTheory

namespace Formalism.F

universe u

theorem covol_eq_of_linearEquiv_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  exact hf (b i) (b j)

theorem exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by
  classical
  let n := finrank ℝ W
  let b := Module.finBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b MeasureTheory.volume
  have hc : 0 < covol L := hC W L ▸ ZLattice.covolume_pos L _
  have hF : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
      ENNReal.ofReal (covol L) := by
    rw [hC W L, ZLattice.covolume_eq_measure_fundamentalDomain L _ hfund,
      MeasureTheory.measureReal_def,
      ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]
  let t := covol L ^ ((1 : ℝ) / (n : ℝ))
  have ht : 0 ≤ t := Real.rpow_nonneg hc.le _
  have htn : t ^ n = covol L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  let o := stdOrthonormalBasis ℝ W
  let eW : W ≃L[ℝ] (Fin n → ℝ) :=
    o.repr.toContinuousLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  let S : Set W := eW ⁻¹' Set.Icc (fun _ => -t) (fun _ => t)
  have hSmem : ∀ x, x ∈ S ↔ ∀ i, |o.repr x i| ≤ t := fun x => by
    simp [S, eW, n, Pi.le_def, abs_le, forall_and]
  have hnorm : ∀ x ∈ S, ‖x‖ ≤ Real.sqrt (n : ℝ) * t := fun x hx => by
    rw [← o.repr.norm_map x, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖o.repr x i‖ ^ 2)
        ≤ Real.sqrt (∑ _i : Fin n, t ^ 2) := Real.sqrt_le_sqrt <| Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) ((Real.norm_eq_abs _).trans_le ((hSmem x).1 hx i)) 2
      _ = Real.sqrt (n : ℝ) * t := by
          simp [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]
  have hsymm : ∀ x ∈ S, -x ∈ S := fun x hx => (hSmem _).2 fun i => by simpa [map_neg] using (hSmem x).1 hx i
  have hconv : Convex ℝ S := (convex_Icc _ _).linear_preimage eW.toLinearMap
  have hcpt : IsCompact S := eW.toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (t - -t) ^ n := by
    have hmp : MeasurePreserving eW := (PiLp.volume_preserving_ofLp (Fin n)).comp o.measurePreserving_measurableEquiv
    rw [hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmeas : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) * 2 ^ n ≤
      MeasureTheory.volume S := by
    rw [hF, hvolS, ← ENNReal.ofReal_pow (by linarith),
      show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp, ← ENNReal.ofReal_mul hc.le]
    exact le_of_eq (congrArg ENNReal.ofReal (by rw [show t - -t = 2 * t by ring, mul_pow, htn, mul_comm]))
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hn
  have : Countable L.toAddSubgroup := b.equivFun.injective.countable
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := L.toAddSubgroup) hfund hsymm hconv hcpt hmeas
  exact ⟨(x : W), x.2, fun h0 => hx0 (Subtype.ext h0), hnorm _ hxS⟩

theorem shortVector_of (hC : CovolEqCovolume.{u}) : ShortVector.{u} := by
  intro E _ _ _ L hL hne
  classical
  have : DiscreteTopology L := hL
  let V := span ℝ (L : Set E)
  let L₀ : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let e : L ≃ₗ[ℤ] L₀ :=
    { toFun := fun y => ⟨⟨y, subset_span y.2⟩, y.2⟩
      invFun := fun x => ⟨((x : V) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : DiscreteTopology L₀ := DiscreteTopology.of_continuous_injective (f := e.symm)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) e.symm.injective
  have : IsZLattice ℝ L₀ := ⟨Submodule.span_span_coe_preimage⟩
  let : MeasurableSpace V := borel _
  have : BorelSpace V := ⟨rfl⟩
  have hcov : covol L₀ = covol L := covol_eq_of_linearEquiv_inner L L₀ e fun _ _ => rfl
  have hrk : finrank ℝ V = rk L := (ZLattice.rank ℝ L₀).symm.trans e.finrank_eq.symm
  have : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x, hx, hx0, hxn⟩ := exists_short_vector_of_isZLattice hC L₀ (hrk.symm ▸ Module.finrank_pos)
  exact ⟨(x : E), hx, fun h0 => hx0 (Subtype.ext h0), by rwa [hrk, hcov] at hxn⟩

end Formalism.F
