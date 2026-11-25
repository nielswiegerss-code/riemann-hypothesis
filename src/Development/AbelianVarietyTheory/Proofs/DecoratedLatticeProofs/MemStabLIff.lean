module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.StabRef

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_zero : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  rwa [map_zero] at this

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (intAt_zero (P := P))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_locP' {n : ℕ} (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ localization₂ P.asIdeal L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L := Iff.rfl

theorem mem_stdLat' {n : ℕ} (x : Sp E n) : x ∈ stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

theorem mem_locStd {n : ℕ} (x : Sp E n) : x ∈ localization₂ P.asIdeal (stdLat E n) ↔ ∀ i, IntAt P (x i) := by
  constructor
  · intro hx i
    obtain ⟨s, hs, h⟩ := (mem_locP' _ x).1 hx
    obtain ⟨r, hr⟩ := (mem_stdLat' _).1 h i
    exact ⟨r, s, hs, by rw [hr, Pi.smul_apply, Algebra.smul_def]⟩
  · intro H
    have : x = ∑ i, (Pi.single i (x i) : Sp E n) := (Finset.univ_sum_single x).symm
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, h⟩ := H i
    refine (mem_locP' _ _).2 ⟨s, hs, ?_⟩
    have e : s • (Pi.single i (x i) : Sp E n) = Pi.single i (algebraMap (𝓞 E) E r) := by
      rw [← Pi.single_smul, Algebra.smul_def, ← h]
    rw [e]
    rw [mem_stdLat']
    intro j
    by_cases hj : j = i
    · subst hj
      exact ⟨r, by simp⟩
    · exact ⟨0, by simp [hj]⟩

theorem mem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat stdAt
  rw [Submodule.mem_comap, mem_locStd]
  simp [LinearMap.pi_apply, smul_eq_mul]

end GlobalTheory.StabRef
