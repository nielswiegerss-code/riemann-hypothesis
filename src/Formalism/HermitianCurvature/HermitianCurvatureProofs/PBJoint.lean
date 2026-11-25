module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Mathlib.Topology.Separation.CompletelyRegular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBJoint

open Formalism.FourierDecayAlt.P

theorem toBuiltPlace {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc A₀ : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    (h : KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    JCT.IsBuiltPlace Cc S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ := by
  obtain ⟨⟨hg1, hg2, hU, hcut, -, -, -, hl1, hl2, -, hGr, -, hLC, hCA, hA, hv⟩, hE, hIn⟩ := h
  exact ⟨hg1, hg2, hU, ⟨hcut, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩,
    hl1, hl2, hGr, hLC, hCA, fun v => (hv v).2.2.2.1, by omega, hA, hIn⟩

theorem built_setting_to_model_place {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc c A₀ : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    (hc : c ≤ Cc) (h : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : KB.IsLeadingFormSetting Cb c S p f χ A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun v => le_trans ?_ (h13 v), le_trans hc h14,
    le_trans ?_ h15, h16⟩
  · exact mul_le_mul_of_nonneg_right hc (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)

theorem prod_dlB {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (hU : S6.Unram E) (hg : 0 < S.g) (i : ℕ) :
    ∏ _v : Fin S.f, KB.dlB S i 1 =
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) := by
  rw [_root_.Formalism.FourierDecayAlt.P.Dx2.NH.nhat E hU S.g _ 1 hg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hf : S.f = S6.deg E := by
    rw [← (Formalism.FourierDecayAlt.P.S6x2.degreeFacts E).2.1, Fintype.card_congr S.pl.symm, Fintype.card_fin]
  rw [hf]
  unfold KB.dlB D.deG
  push_cast
  conv_rhs => rw [zpow_mul, zpow_natCast, pow_mul, ← mul_pow, ← mul_pow]
  rw [div_div_eq_mul_div]
  congr 1
  ring

end Formalism.FourierDecayAlt.P.PBJoint
