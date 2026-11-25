module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis
public import Lemmata.PaddedFamilies.PadFam
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma

@[expose] public section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace PI.SelfDualLoc.W.LB

open PI.SelfDualLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

lemma smul_OE (c : 𝓞 E) (w : Fin n → E) : c • w = (c : E) • w := by
  ext j; simp [Algebra.smul_def]

lemma algF_ne_zero {u : 𝓞 F} (hu : u ∉ v.asIdeal) : algebraMap F E (u : F) ≠ 0 := by
  have hu0 : (u : F) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using h)
    rw [this]; exact zero_mem _
  exact (map_ne_zero_iff _ (algebraMap F E).injective).2 hu0

end PI.SelfDualLoc.W.LB
