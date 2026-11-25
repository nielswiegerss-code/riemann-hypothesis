module

import all ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Lemma
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NsqMulVecLeOpN

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma rmul_mem_dom {z b : Frame X.Ψ r} (hz : z ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul z b ∈ X.dom := by
  apply ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul <;> assumption

lemma opN_smul_le {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) ≤ ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ,
      Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2) =
        ‖t‖ * (Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)) := by
    intro v
    have h1 : ∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2 = ‖t‖ ^ 2 * ∑ i, ‖Matrix.mulVec A v i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmv : Matrix.mulVec (t • A) v i = t * Matrix.mulVec A v i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [hmv, norm_mul, mul_pow]
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg t), mul_div_assoc]
  open scoped Pointwise in
  have hS : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
      rw [smul_eq_mul, key v]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [smul_eq_mul, key v]⟩
  refine le_of_eq ?_
  rw [hS, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]

lemma zN_nonneg (Z : X.Coord) : 0 ≤ X.zN Z := by
  unfold Data.zN
  exact Real.iSup_nonneg fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.opN_nonneg _

lemma zN_smul_le (t : ℂ) (Z : X.Coord) : X.zN (t • Z) ≤ ‖t‖ * X.zN Z := by
  unfold Data.zN
  refine Real.iSup_le (fun τ => ?_) (mul_nonneg (norm_nonneg t) (zN_nonneg X Z))
  have h1 : Data.opN (Matrix.of ((t • Z) τ)) ≤ ‖t‖ * Data.opN (Matrix.of (Z τ)) :=
    opN_smul_le t (Matrix.of (Z τ))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg t))
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

lemma xZ_diff (x : Frame X.Ψ r) : Differentiable ℂ fun Z : X.Coord => X.xZ x Z := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hL : ∀ j, Differentiable ℂ fun Z : X.Coord => X.lowBlock Z τ j b := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  show Differentiable ℂ fun Z : X.Coord => ∑ j, mat x τ a j * X.lowBlock Z τ j b
  first
    | exact Differentiable.fun_sum (fun j _ => (hL j).const_mul _)

lemma xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show mat x τ * X.lowBlock 0 τ = x τ
  rw [h1, Matrix.mul_one]
  rfl

lemma exp_small : Real.exp (1 / 25) < 3 / 2 := by
  by_contra! hcon
  have h25 : Real.exp 1 = Real.exp (1 / 25) ^ 25 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (3 / 2 : ℝ) ^ 25 ≤ Real.exp (1 / 25) ^ 25 := pow_le_pow_left₀ (by norm_num) hcon 25
  have he := Real.exp_one_lt_d9
  norm_num at hpow
  linarith

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
