module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

theorem existsLatticeAutomorphismApprox : LocLin := by
  intro F E _ _ _ _ _ sig p L a e
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

theorem local_span_holds : LocSpan := by
  intro F E _ _ _ _ _ sig p L n b hb x
  have hsub : Set.range L.ιE ⊆ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨c, rfl⟩ := hb e

    rw [map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [existsLatticeAutomorphismApprox F E sig p L]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) = ⊤ := by
    rw [eq_top_iff, ← L.span]
    exact Submodule.span_le.mpr hsub
  have hx : x ∈ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := htop ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun L.Fp).mp hx
  exact ⟨α, hα.symm⟩

theorem intSpan' : IntSpan := by
  intro F E _ _ _ _ _
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let B := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (fun i => B i))
  refine ⟨Module.finrank F E, fun i => y • B i,
    fun i => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), fun e => ?_⟩
  refine ⟨fun i => B.repr e i / (y : F), ?_⟩
  conv_lhs => rw [← B.sum_repr e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy0
  rw [smul_comm, ← smul_assoc, zsmul_eq_mul, mul_div_cancel₀ _ hyF]

end PI.StrongApproxE
