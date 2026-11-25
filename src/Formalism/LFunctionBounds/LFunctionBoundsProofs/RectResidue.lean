module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Complex

namespace Formalism.FX

theorem rectangle_residue : RectResidue := by
  classical
  intro g G P b x0 x1 y0 y1 hx hy hP ⟨U, hU, hrect, hG⟩ hg
  rw [Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le] at hrect
  have hreg (S : Finset ℂ) {z : ℂ} (hz : z ∈ U) (hzS : z ∉ S) :
      AnalyticAt ℂ (fun w => G w + ∑ p ∈ S, b p / (w - p)) z := by
    refine (hG.analyticAt (hU.mem_nhds hz)).add (Finset.analyticAt_fun_sum _ fun p hp => ?_)
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem hp hzS).symm)
  apply GlobalTheory.ResRect.residue_rectangle_of_finite_principal_parts g
    ⟨x0, y0⟩ ⟨x1, y1⟩ P b (fun _ => 0) hx hy hP
  · refine DifferentiableOn.congr (f := fun w => G w + ∑ p ∈ P, b p / (w - p)) ?_ (fun w hw => hg w hw.2)
    exact fun w hw => (hreg P (hrect hw.1) hw.2).differentiableAt.differentiableWithinAt
  · intro p hp
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hP p hp
    have hpU := hrect (Complex.mem_reProdIm.mpr ⟨⟨hx0.le, hx1.le⟩, ⟨hy0.le, hy1.le⟩⟩)
    refine ⟨fun _ => 0, _, hreg (P.erase p) hpU (Finset.notMem_erase p P), ?_⟩
    have haway := (P.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds (Finset.notMem_erase p P)
    filter_upwards [mem_nhdsWithin_of_mem_nhds haway, self_mem_nhdsWithin] with w hw hwp
    have hwP : w ∉ P := fun hwP => hw (Finset.mem_erase.mpr ⟨hwp, hwP⟩)
    rw [hg w hwP, ← Finset.add_sum_erase P _ hp]
    simp [add_left_comm]

end Formalism.FX
