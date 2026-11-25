module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDeg
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsRpowPow

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_GamD_le (D : D7) (large₂ : SizeData₂ D) {Ca C2 C : ℝ} (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) :
    rows_GamD D large₂ Ca C2 ≤ GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
      (C / D.R.k) ^ (D.R.k * D.R.f) := by
  unfold rows_GamD
  have hb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL : 0 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hG : 0 ≤ GamS D large₂ := by unfold GamS; positivity
  have hQ : 0 ≤ (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L := mul_nonneg (by positivity) hL
  have hE : Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 ≤
      Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) := by
    rw [sq, ← Real.exp_add, Real.exp_le_exp, hb]
    have := mul_le_mul_of_nonneg_right hC2 hQ
    linarith
  have hX : (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
    calc (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ |Ca / D.R.k| ^ (D.R.k * D.R.f) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_div, abs_of_nonneg hk0]
          exact div_le_div_of_nonneg_right hCa hk0
  have hX2 : 0 ≤ (C / D.R.k) ^ (D.R.k * D.R.f) :=
    pow_nonneg (div_nonneg (le_trans (abs_nonneg _) hCa) hk0) _
  calc GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (Ca / D.R.k) ^ (D.R.k * D.R.f)
      ≤ GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (C / D.R.k) ^ (D.R.k * D.R.f) :=
        mul_le_mul_of_nonneg_left hX (mul_nonneg hG (sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hG) hX2

theorem rows_degB_le {C' Cl Cg cb Cu cT CT C0 A c Ca C2 Ch C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) (s : ℕ) :
    rows_degB D large₂ u c Ca C2 Ch s ≤
      LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have hXs0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) hc s
  have hXs := rows_XiP_le D large₂ u hc hcC hpe2 s
  have core := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := 2)
    (v := D.host.v) (Γ := rows_GamD D large₂ Ca C2) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := 0) (rD := 1) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by norm_num) (by linarith) (rows_GamD_nonneg D large₂ Ca C2) hc hcC hC1 le_rfl
    zero_le_one zero_le_one hXs0 hXs (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold LatticeSumBounds.ndRow at core
  rw [div_self (two_ne_zero), one_pow] at core
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) := by
    have : 0 ≤ gg D := by linarith
    positivity
  have hbig0 : 0 ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) := by
    unfold LatticeSumBounds.bigH
    have := d_two_le_b D large₂
    positivity
  have hM0 : 0 ≤ ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s * C ^ (D.R.k * D.R.f) *
      LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) * (C * s * D.R.f) ^ (6 * s * D.R.f) := by
    have : 0 ≤ XiB D large₂ u C s := hXs0.trans hXs
    have : 0 ≤ D.host.v := by linarith
    positivity
  unfold rows_degB rows_RD rows_Phi LatticeSumBounds.degRow
  unfold rows_P at core ⊢
  calc (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2
      = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
        (1 * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) * ((1 + 0) * 1) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * _ := mul_le_mul_of_nonneg_left core hA0
    _ = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * rows_GamD D large₂ Ca C2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * (GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
          (C / D.R.k) ^ (D.R.k * D.R.f))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rows_GamD_le D large₂ hC2 hCa) hM0) hA0
    _ = _ := by ring

theorem rows_RowsDeg_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c) (hc1 : 1 ≤ c)
    (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsDeg X Y C := by
  intro s hs hsk
  have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hE : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have := mul_nonneg (mul_nonneg h.hc (sub_nonneg.2 hsk')) hm
    linarith
  have hq2s : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1) := by linarith
  exact rows_RowBound_mono Y (rows_Deg_record Y h hK hc1 s hs hsk hq2s)
    (rows_degB_le h.hH h.hc hcC hC1 hC hC2 hCa s) h.hdim.le

end Rec

end Formalism.MainNotions.BridgeLemma₂
