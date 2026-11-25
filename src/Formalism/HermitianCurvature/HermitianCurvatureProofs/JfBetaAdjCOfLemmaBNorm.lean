module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

variable {k r : ℕ}

section gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cptInCC_G {F : Mat k r → E} {C : Set (Mat k r)} (hF : CkOn ⊤ (GV k r) F) (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (A : ℝ) (m : ℕ) : InCC A m F := by
  classical
  set F₂ : Mat k r → E := fun g => if g ∈ GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hF₂c : CkOn ⊤ (GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, fun g hg hgG => (he g hgG).trans (hff g hg hgG)⟩
  obtain ⟨c, hc1, hc2⟩ := Formalism.FourierDecayAlt.P.compact_support_finite_class k r E F₂ C hF₂c hC (fun g hg => by
    by_cases hgG : g ∈ GV k r
    · rw [he g hgG]; exact hz g hgG hg
    · simp [hF₂, hgG]) A m
  refine ⟨c, B5.ckOn_mono le_top hF, fun u v hu hv hl g hg => ?_⟩
  have := hc2 u v hu hv hl g hg
  rwa [dLR_eq, W_congr (lr u v) (fun y hy => by
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1) he g hg, ← dLR_eq] at this

theorem ckOn_Rw_top {f : Mat k r → E} (h : CkOn ⊤ (GV k r) f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ (GV k r) (Rw w f) := by
  intro w
  induction w with
  | nil => intro _; exact h
  | cons X w ih =>
    intro hw
    show CkOn ⊤ (GV k r) (RdV X (Rw w f))
    have h1 : CkOn (⊤ + 1) (GV k r) (Rw w f) := by
      rw [top_add]; exact ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    exact B5.ckOn_RdV (hw X List.mem_cons_self) h1

end gen

end Formalism.FourierDecayAlt.P.JFxG
