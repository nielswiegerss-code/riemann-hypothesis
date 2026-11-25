module

public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
public import Formalism.GL3MeanSquares.HookFormulaTorsion.OneAddInvPowLeExpOne
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

@[expose] public section

namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

section P3
open Formalism.MainNotions.S MeasureTheory
open scoped InnerProductSpace

theorem signature_counts_ge_one (D : D7) : 1 ≤ pY D ∧ 1 ≤ qY D := by
  unfold pY qY
  simp only [Formalism.BasicNotions.Ranks.sigY0]
  have := D.R.m_add_three_le_k
  constructor <;> omega

end P3

theorem explicit_gap_le_general_gap (D : D7) (C ep0 : ℝ) (hC : 8192 ≤ C) : spectralGapLowerBound D ep0 ≤ gap3 D C ep0 := by
  unfold spectralGapLowerBound gap3
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log D.R.r := Real.log_nonneg hr1
  have hX : 0 ≤ (↑(min (pY D) (qY D)) : ℝ) * (↑(pY D) * ↑(qY D)) ^ 3 := by positivity
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg ep0)
  have h1 : (8192 : ℝ) ≤ C * D.R.r := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hX hlog)]

theorem weighted_log_sum_lower_bound (D : D7) (w : ℕ → D.what₂.Tau → ℝ) (w0 : ℝ) (hw0 : 0 < w0) (hpi : Real.pi ≤ D.host.v)
    (hw : ∀ ρ j, j < D.R.m → w0 ≤ w j ρ) :
    (D.R.m : ℝ) * Real.log w0 ≤
      ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hv : 1 ≤ D.host.v / Real.pi := (one_le_div Real.pi_pos).2 hpi
  have hterm : ∀ j, j < D.R.m → (Fintype.card D.what₂.Tau : ℝ) * Real.log w0 ≤
      ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
    intro j hj
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ρ _
    apply Real.log_le_log hw0
    rw [mul_div_assoc]
    calc w0 = w0 * 1 := (mul_one _).symm
      _ ≤ w j ρ * (D.host.v / Real.pi) :=
        mul_le_mul (hw ρ j hj) hv zero_le_one (by linarith [hw ρ j hj])
  rw [D.what₂.card_Tau] at hterm
  calc (D.R.m : ℝ) * Real.log w0 =
        ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ((D.R.f : ℝ) * Real.log w0) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, inv_mul_cancel_left₀ hf.ne']
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hterm j (Finset.mem_range.1 hj)) (by positivity)

theorem weights_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ w j ρ := by
  obtain ⟨-, -, -, -, -, -, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hx := sc.one_lt_alt
  have hbase : 1 ≤ bN D ρ 0 := by
    have h := (hb0 ρ).1
    rw [le_div_iff₀ (by linarith)] at h
    have h4 : (1 : ℝ) ≤ D.R.k * (4 * Δ) := by nlinarith
    have h5 : (D.R.k : ℝ) * (4 * Δ) ≤ D.R.k * (4 * Δ) * sc.x :=
      le_mul_of_one_le_right (by positivity) hx.le
    linarith
  have hmono : ∀ i, i < D.R.m → bN D ρ 0 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hwb ρ i hi
      linarith
  linarith [(hw ρ j hj).2.1, hmono j hj]

theorem eight_L_le_log_g (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w) (i : Fin 2) :
    8 * sc.L ≤ Real.log (D.host.g i : ℝ) := by
  obtain ⟨-, -, -, -, -, hg, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb : 0 < sc.b := Real.exp_pos _
  have h1 := (hg i).1
  have hpos : 0 < ((D.R.k : ℝ) * sc.b) ^ 8 := by positivity
  calc 8 * sc.L = Real.log (sc.b ^ 8) := by
        rw [Real.log_pow, Formalism.BasicNotions.Scale.b, Real.log_exp]
        norm_num
    _ ≤ Real.log (((D.R.k : ℝ) * sc.b) ^ 8) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ hb.le (by nlinarith) 8)
    _ ≤ Real.log (D.host.g i : ℝ) := Real.log_le_log hpos h1

theorem corollary_five_four_of_explicit (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) : VandermondeCountExplicit D sc C0 CY := by
  intro Δ w hA Γ hΓ u hT2 hf2 hT1 hT3
  have hB := hA.1
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hD := dual_degree_pos D hg
  have hd := dual_degree_word_pos D hg (massI_pos D D.R.k) u
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := le_trans one_le_two (le_trans D.R.two_le_m D.R.m_le_f)
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hX : Real.exp (logXuD D u) ^ (D.R.f * D.R.k) = DstarD D / duStarU D u := by
    have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
    have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    rw [← Real.exp_nat_mul]
    unfold logXuD logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (DstarD D / duStarU D u)) =
      Real.log (DstarD D / duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
  obtain ⟨c1, c2, c3, c4⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ) (Real.exp (logXuD D u)) Γ
    (DstarD D) (duStarU D u) _ (logXuD D u) (logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ hD hd hX
    hT1 hT3 rfl (by rw [Real.log_exp]) (by rw [Real.log_exp])
  have hL := scale_one_le_L sc
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hΓ0 : 0 < Γ := by linarith
  have eΓ : Γ ^ (-(2 : ℝ)) = (Γ⁻¹) ^ 2 := by
    rw [Real.rpow_neg hΓ0.le, Real.rpow_two, inv_pow]
  have l1 := (h5 Δ w hA u).1
  refine ⟨⟨by rw [eΓ]; exact c1, by rw [eΓ]; exact c2⟩, by linarith, by linarith, fun hG => ⟨c4, by linarith, ?_⟩⟩
  have hm : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hA.2.2.2.1
  have s1 := weighted_log_sum_lower_bound D w 1 one_pos hB.1 (fun ρ j hj => weights_ge_one_section_B D sc C0 Δ w hB ρ j hj)
  rw [Real.log_one, mul_zero] at s1
  have s2 : 16 * sc.L ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
    rw [Fin.sum_univ_two]
    have := eight_L_le_log_g D sc C0 Δ w hB 0
    have := eight_L_le_log_g D sc C0 Δ w hB 1
    linarith
  unfold lowS at l1
  have s3 : (D.R.m : ℝ) * (16 * sc.L) ≤ (D.R.m : ℝ) * ∑ i : Fin 2, Real.log (D.host.g i : ℝ) :=
    mul_le_mul_of_nonneg_left s2 (by linarith)
  nlinarith

theorem part_five_explicit_of_propositions (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) (hv : VandermondeVariationExplicitBound D sc C0 CY) :
    VandermondeCountBound D sc C0 CY := ⟨h5, corollary_five_six_of_explicit D sc C0 CY h5, corollary_five_four_of_explicit D sc C0 CY h5, hv⟩

end Formalism.MainNotions.StandardLattice
