module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDF
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

theorem decay_length_sufficient {m k r c B : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (ha : B * m ^ 5 ≤ k) :
    (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 ≤ (9 * c + 3) * k * m ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hr1 : r + 1 = m / 2 := by linarith
  have e : (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 =
      6 * m * (c * r ^ 2) + (B * m ^ 3) / 4 + (B * m ^ 5) / 2 + (m / 2) * (12 * (m / 2) ^ 2) + 1 := by rw [hr1]; ring
  have p1 : 6 * m * (c * r ^ 2) ≤ 2 * (c * k * m ^ 2) := by
    have a : r ^ 2 ≤ m ^ 2 / 4 := by nlinarith
    have b : c * r ^ 2 ≤ c * (m ^ 2 / 4) := mul_le_mul_of_nonneg_left a hc
    have d : 6 * m * (c * r ^ 2) ≤ 6 * m * (c * (m ^ 2 / 4)) := mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hc (sq_nonneg m)) (by linarith : 0 ≤ k - m)]
  have m35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have p2 : B * m ^ 3 ≤ k := le_trans (mul_le_mul_of_nonneg_left m35 hB) ha
  have p4 : (m / 2) * (12 * (m / 2) ^ 2) ≤ (3 / 2) * (k * m ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : 0 ≤ k - m)]
  have p5 : (1 : ℝ) ≤ (1 / 2) * (k * m ^ 2) := by nlinarith
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  have p6 : k ≤ (1 / 4) * (k * m ^ 2) := by nlinarith [mul_nonneg hk0 (sub_nonneg.2 hm4)]
  have hU : 0 ≤ c * k * m ^ 2 := by positivity
  rw [e]
  have t : (9 * c + 3) * k * m ^ 2 = 9 * (c * k * m ^ 2) + 3 * (k * m ^ 2) := by ring
  rw [t]
  linarith

theorem le_max_four (a b c d : ℝ) : a ≤ max (max a b) (max c d) ∧ b ≤ max (max a b) (max c d) ∧
    c ≤ max (max a b) (max c d) ∧ d ≤ max (max a b) (max c d) :=
  ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word}

theorem height_pow_mono_constant (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h : |c'| + 2 ≤ c) (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := by
  have h1 : c' ≤ c := by linarith [le_abs_self c']
  have h2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have mono := rows_HHZ_mono large₂ hrd h1 h2 Z
  have o := rows_one_le_HHZ' D large₂ c' Z
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  calc HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c' Z ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := Real.rpow_le_rpow (by linarith) mono (by positivity)

theorem switch_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz what₂ hrows Z hZ
  have h0 := h hH F0 he hz what₂ hrows Z hZ
  unfold MeanLe at h0 ⊢
  have hB : HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ ≤
      HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ := by
    refine mul_le_mul_of_nonneg_right (height_pow_mono_constant large₂ (d_rdE_pos hH.1) h1 Z) ?_
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold nV
    exact D.R.k_even.pow_nonneg _
  exact h0.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB))

theorem partner_count_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ
  refine (h hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrd := d_rdE_pos hH.1
  have k1 : c' ≤ c := by linarith [le_abs_self c']
  have k2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  have ma := rows_HHZ_mono large₂ hrd k1 k2 (ZhatL (lf D F0) F')
  have mb := rows_HHZ_mono large₂ hrd k1 k2 Z
  have oa := rows_one_le_HHZ' D large₂ c' (ZhatL (lf D F0) F')
  have ob := rows_one_le_HHZ' D large₂ c' Z
  have o : 1 ≤ HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z := one_le_mul_of_one_le_of_one_le oa ob
  have hp : c' ^ D.R.f ≤ c ^ D.R.f :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
  refine mul_le_mul hp ?_ (Real.rpow_nonneg (by linarith) _) (pow_nonneg hc _)
  calc (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c' * (D.R.rS : ℝ) ^ 2)
      ≤ (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ _ := Real.rpow_le_rpow (by linarith) (mul_le_mul ma mb (by linarith) (by linarith)) (by positivity)

end Mono

end Formalism.MainNotions.BridgeLemma₂
