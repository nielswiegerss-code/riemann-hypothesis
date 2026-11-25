module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace UpperTheory.Gal.Wt

private theorem pow_mem_le {s m : ℤ} (h : m ≤ s) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpLe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem pow_mem_ge {s m : ℤ} (h : s ≤ m) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpGe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

open scoped Pointwise in
private theorem circle_mul_mem_of_mem_span_of_mem_span {S T : Set (Circle → ℂ)}
    {P : Submodule ℂ (Circle → ℂ)} (h : ∀ f ∈ S, ∀ g ∈ T, (fun z => f z * g z) ∈ P)
    {f g : Circle → ℂ} (hf : f ∈ Submodule.span ℂ S) (hg : g ∈ Submodule.span ℂ T) :
    (fun z => f z * g z) ∈ P := by
  refine (?_ : Submodule.span ℂ S * Submodule.span ℂ T ≤ P) (Submodule.mul_mem_mul hf hg)
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact h a ha b hb

private theorem circle_comp_inv_mem_of_mem_span {S : Set (Circle → ℂ)}
    {P : Submodule ℂ (Circle → ℂ)} (h : ∀ f ∈ S, (fun z : Circle => f z⁻¹) ∈ P)
    {f : Circle → ℂ} (hf : f ∈ Submodule.span ℂ S) : (fun z : Circle => f z⁻¹) ∈ P :=
  (Submodule.span_le.2 (fun f hfS => h f hfS) :
    Submodule.span ℂ S ≤ P.comap (LinearMap.funLeft ℂ ℂ (Inv.inv : Circle → Circle))) hf

private theorem circle_zpow_mul_zpow_eq_zpow_add (m n : ℤ) :
    (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) = fun z : Circle => (z : ℂ) ^ (m + n) := by
  funext z
  rw [zpow_add₀ (Circle.coe_ne_zero z)]

private theorem circle_inv_zpow_eq_zpow_neg (m : ℤ) :
    (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) = fun z : Circle => (z : ℂ) ^ (-m) := by
  funext z
  rw [Circle.coe_inv, inv_zpow, zpow_neg]

theorem expBasic_of : ExpBasic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_le (by omega)
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_ge (by omega)
  · intro s t hst
    constructor
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hm.trans hst, rfl⟩
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hst.trans hm, rfl⟩
  · intro c m
    exact ⟨(ExpLe m).smul_mem c (pow_mem_le le_rfl), (ExpGe m).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro c
    have e : (fun _ : Circle => c) = c • (fun z : Circle => (z : ℂ) ^ (0 : ℤ)) := by
      funext z
      simp
    rw [e]
    exact ⟨(ExpLe 0).smul_mem c (pow_mem_le le_rfl), (ExpGe 0).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro s f
    constructor
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_ge (by omega)
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_le (by omega)

end UpperTheory.Gal.Wt
