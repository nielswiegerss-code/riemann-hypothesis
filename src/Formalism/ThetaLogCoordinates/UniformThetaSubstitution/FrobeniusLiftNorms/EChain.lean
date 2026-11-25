module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EJoint
public import Formalism.GaussJetBounds.StatementP
public import Formalism.GrowthSums.StatementA

@[expose] public section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace ScaledSeriesSubstitution

theorem scale_scale {K ι : Type} [Field K] {ϖ : K} (hϖ : ϖ ≠ 0) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K))
      (MvPowerSeries.subst
        (fun i => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X i : MvPowerSeries ι K)) f) = f := by
  ext n
  rw [MinorFormHomogeneity.coeff_subst_scale, MinorFormHomogeneity.coeff_subst_scale, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hϖ, one_pow, one_mul]

theorem hasSubst_scale {K ι : Type} [Field K] [Finite ι] (a : K) :
    MvPowerSeries.HasSubst
      (fun i => MvPowerSeries.C a * (MvPowerSeries.X i : MvPowerSeries ι K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp

theorem subst_C_mul {K ι κ : Type} [Field K] {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) (a : K) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst b (MvPowerSeries.C a * f) = MvPowerSeries.C a * MvPowerSeries.subst b f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul hb]

theorem constantCoeff_zLin {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
  unfold zLin

  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp

theorem subst_scale_zLin {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (a : K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.subst
        (fun y => MvPowerSeries.C a * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (zLin om oms x) = MvPowerSeries.C a * zLin om oms x := by
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) a
  unfold zLin

  rw [← MvPowerSeries.coe_substAlgHom hb, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hb]
  split_ifs
  · rw [subst_C_mul hb, MvPowerSeries.subst_X hb, mul_left_comm]
  · rw [← MvPowerSeries.coe_substAlgHom hb, map_zero, mul_zero]
  · rw [subst_C_mul hb, MvPowerSeries.subst_X hb, mul_left_comm]
  · rw [← MvPowerSeries.coe_substAlgHom hb, map_zero, mul_zero]

theorem ps_subst_C_mul {K κ : Type} [Field K] {w : MvPowerSeries κ K}
    (hw : PowerSeries.HasSubst w) (a : K) (f : PowerSeries K) :
    PowerSeries.subst w (PowerSeries.C a * f) = MvPowerSeries.C a * PowerSeries.subst w f := by
  rw [← PowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hw]

end ScaledSeriesSubstitution

open ScaledSeriesSubstitution

end Formalism.InvariantFactorPaths.G7
