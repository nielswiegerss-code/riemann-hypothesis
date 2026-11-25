module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartTrans

namespace GlobalTheory.HomChain

variable {k : Type} [CommRing k] {d : ℕ}

theorem law_right_unit (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hs : ∀ j, GP ((![pt k (n := 2) d 1, pt k (n := 2) d 0] : Fin 2 → Pt k 2 d) j) :=
    pair_points_zero_constant (gp_pt 1) (gp_pt 0)
  rw [← G.comm i, gt_ev_ev' _ _ axis_GP hs, eval_pair_points, evP_pt _ axis_GP, evP_pt _ axis_GP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact G.unit i

theorem dof_hom (G G' : FGLaw k d) (α : Pt k 1 d) (hα : ∀ i, constantCoeff (α i) = 0)
    (hom : comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof G.F u (ev (n := 1) ![α] g) = ev (n := 1) ![α] (Dof G'.F ((dLin α).mulVec u) g) := by
  have hφ : GP α := hα
  have h0 : GP (comp1 α (pt k (n := 2) d 0)) := gp_comp1 α _ hφ (gp_pt 0)
  have h1 : GP (comp1 α (pt k (n := 2) d 1)) := gp_comp1 α _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hF : GP G.F := G.const
  have hF' : GP G'.F := G'.const
  have eF : G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1) = G.F := by
    funext i
    have e : (![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) = pt k d := by
      funext j; fin_cases j <;> rfl
    change ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] (G.F i) = _
    rw [e]
    exact congrFun (MvPowerSeries.subst_self (R := k) (σ := Fin 2 × Fin d)) (G.F i)
  have key : ev (n := 2) ![G.F] (ev (n := 1) ![α] g) =
      ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] (ev (n := 2) ![G'.F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF'), vec1]
    have : evP ![G.F] α = evP ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] G'.F := by
      rw [eF] at hom
      exact hom
    rw [this]
  have pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j))
      (f : PS k m d) (v : Fin n × Fin d) :
      pderiv (R := k) v (ev V f) =
        ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv (R := k) (j, l) f) * pderiv (R := k) v (V j l) := by
    unfold ev
    rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]
  have dof_eq (L : FGLaw k d) (v : Fin d → k) (f : PS k 1 d) :
      Dof L.F v f = ∑ i, C (v i) *
        ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), i) (ev ![L.F] f)) := by
    have hL := single_point_zero_constant L.const
    have eval_axis (h : PS k 1 d) : ev ![pt k (n := 1) d 0, 0] (ev ![L.F] h) = h := by
      rw [gt_ev_ev' _ _ axis_GP hL, vec1,
        show evP ![pt k (n := 1) d 0, 0] L.F = pt k d 0 from funext (law_right_unit L),
        gt_ev_pt_self]
    unfold Dof
    simp only [pderiv_ev _ hL, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP,
      eval_axis, Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have axis_pderiv_comp (H : PS k 2 d) (i : Fin d) :
      ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), i)
        (ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] H)) =
      ∑ l, C (dLin α l i) *
        ev ![α] (ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), l) H)) := by
    have eval_comp (K : PS k 2 d) :
        ev ![pt k (n := 1) d 0, 0]
          (ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] K) =
        ev ![α] (ev ![pt k (n := 1) d 0, 0] K) := by
      rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP α _ (gp_pt 0),
        evP_comp1 _ axis_GP α _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
        gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points,
        evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [gt_comp1_pt_right, gt_comp1_zero α hφ]
    have pderiv_comp_pt (b : Fin 2) (l : Fin d) :
        pderiv (R := k) ((1 : Fin 2), i) (comp1 α (pt k (n := 2) d b) l) =
          if (1 : Fin 2) = b then
            ev ![pt k (n := 2) d b] (pderiv (R := k) ((0 : Fin 1), i) (α l)) else 0 := by
      change pderiv (R := k) ((1 : Fin 2), i) (ev ![pt k (n := 2) d b] (α l)) = _
      rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
      simp only [Matrix.cons_val_zero, pt]
      split_ifs with h
      · subst b
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
        · simp
      · refine Finset.sum_eq_zero fun j _ => ?_
        rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]
    have eval_linear (l : Fin d) : ev ![pt k (n := 1) d 0, 0]
        (ev ![pt k (n := 2) d 1] (pderiv (R := k) ((0 : Fin 1), i) (α l))) = C (dLin α l i) := by
      rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
      simp [dLin]
    rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt,
      one_ne_zero, ite_false, ite_true, mul_zero, Finset.sum_const_zero, zero_add]
    rw [ev_sum _ axis_GP]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ axis_GP, eval_comp, eval_linear, mul_comm]
  rw [dof_eq G, dof_eq G', key,
    ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp, ev_C_mul _ (single_point_zero_constant hφ)]

  simp only [Matrix.mulVec, dotProduct, map_sum,
  map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.HomChain
