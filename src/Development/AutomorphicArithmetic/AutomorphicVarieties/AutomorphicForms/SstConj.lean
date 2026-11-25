module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.CoeffExt TensorProduct Module

namespace UpperTheory.V.Af

theorem sat_ae_of_smooth (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ)
    (hi : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS'⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1) ((hρ v).mem_nhds (by simp))
  filter_upwards [S.finite_toSet.eventually_cofinite_notMem] with w hw
  obtain ⟨σ, hσ⟩ := hi w
  obtain ⟨h1, h2⟩ := hS F n w σ
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hσ.2
    ⟨v, hv, fun u hu => hS' (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev n w
      (by rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top) hu,
      fun x hx => pLoc_locGL_of_ne (fun e : x = w => hw (e ▸ hx)) u⟩)⟩)
  exact ⟨B, (h2 _ _ hσ B).2 hB⟩

end UpperTheory.V.Af
