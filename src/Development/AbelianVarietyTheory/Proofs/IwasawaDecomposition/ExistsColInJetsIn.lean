module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Col2

namespace JetEx

theorem hasLetters_of_over {K : Ctx} {P : Pre} (h : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  have hx : 0 < K.s.x := zero_lt_one.trans K.s.one_lt_alt
  refine ⟨(Delv K.s K.cD : ℚ), K.c, Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)), K.ok.inj,
    fun w τ l hl => ?_, K.ok.code⟩
  have h1 := (K.ok.hc w).1 τ
  change l + 1 < K.P.R.k - 1 at hl
  show (K.P.hcW w τ).v ⟨l, by omega⟩ - (K.P.hcW w τ).v ⟨l + 1, hl⟩ = _
  rw [h1, h1, show K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 by omega]
  push_cast
  ring

end JetEx

end GlobalTheory.Mem.Col2
