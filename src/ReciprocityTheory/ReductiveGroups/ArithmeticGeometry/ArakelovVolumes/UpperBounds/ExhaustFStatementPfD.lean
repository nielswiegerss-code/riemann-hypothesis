module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC
import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfC

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_nM (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ a b := by
  show ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b
  unfold nmat
  by_cases h : b < a
  · simp only [dite_eq_left h]
    first
      | fun_prop
  · simp only [dite_eq_right h]
    exact contDiff_const

theorem unipotentFrame_inv_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)⁻¹ = (n1 X z τ).adjugate := by
  have hdet : (n1 X z τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [n1, nM_diag]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      exact nM_upper X z τ (show Fin.castLE X.p0_le i < Fin.castLE X.p0_le j from hij')
  rw [Matrix.inv_def, hdet]
  simp

private lemma cd_adj_lemma_2 {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) (i j : Fin k) :
    ContDiff 𝕜 ∞ fun z => (M z).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD.contDiff_det_of fun a b => ?_
  by_cases hab : a = j
  · simp only [Matrix.updateRow_apply, hab, ite_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, hab, ite_false]
    exact h a b

theorem cd_Zt (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    ContDiff ℂ ∞ fun z : V (nd X) => Zt X z τ a m := by
  have hfun : (fun z : V (nd X) => Zt X z τ a m) =
      fun z => ∑ k, Wm X z τ m k * (n1 X z τ).adjugate k a := by
    funext z
    simp only [Zt, Matrix.transpose_apply, Matrix.mul_apply, unipotentFrame_inv_eq_adjugate]
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (qI X m) (Fin.castLE X.p0_le k)
    exact cd_nM X τ _ _
  · refine cd_adj_lemma_2 (M := fun z : V (nd X) => n1 X z τ) (fun i j => ?_) k a
    show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
    exact cd_nM X τ _ _

theorem cd_Am_entry (τ : X.Ψ) (a c : Fin X.p0) :
    ContDiff ℝ ∞ fun z : V (nd X) => Am X z τ a c := by
  have hZ : ∀ a m, ContDiff ℝ ∞ fun z : V (nd X) => Zt X z τ a m :=
    fun a m => (cd_Zt X τ a m).restrict_scalars ℝ
  have hfun : (fun z : V (nd X) => Am X z τ a c) = fun z =>
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a c - ∑ m, Zt X z τ a m * star (Zt X z τ c m) := by
    funext z
    simp only [Am, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  refine contDiff_const.sub (ContDiff.sum fun m _ => (hZ a m).mul ?_)
  first
    | exact Complex.conjCLE.contDiff.comp (hZ c m)

theorem cd_detAm (τ : X.Ψ) : ContDiff ℝ ∞ fun z : V (nd X) => (Am X z τ).det := by
  exact _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD.contDiff_det_of (M := fun z : V (nd X) => Am X z τ) fun a c => cd_Am_entry X τ a c

theorem rhF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.rhF_contDiffAt <;> assumption

theorem T_cd {n : ℕ} : ContDiff ℝ ∞ fun z : V n => Real.log (1 + ‖z‖ ^ 2) := by
  exact (contDiff_const.add (contDiff_norm_sq ℂ)).log fun z => by positivity

theorem eF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (eF X x0) z := by
  exact (rhF_contDiffAt X x0 ho hz).add (T_cd (n := nd X)).contDiffAt

theorem isOpen_OmF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  apply ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF <;> assumption

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
