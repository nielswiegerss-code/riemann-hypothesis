module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.RationalTorsion

theorem section_ext {K k : Type} [Field K] [Field k] (t : Sp k ⟶ Sp K) {G : Over (Sp K)}
    {s s' : 𝟙_ (Over (Sp K)) ⟶ G} (h : toUnit (Over.mk t) ≫ s = toUnit (Over.mk t) ≫ s') : s = s' := by
  have h1 : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have h2 : Flat t := inferInstance
  have h3 : Epi t := Flat.epi_of_flat_of_surjective t
  have h4 : (toUnit (Over.mk t)).left = t := by simp
  have h5 : Epi (toUnit (Over.mk t)).left := by rw [h4]; exact h3
  have h6 : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_add_smul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a c : D.La) :
    I.ev n (a + n • c) = I.ev n a := by
  rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]

theorem exists_eq_nsmul (D : Datum H) (l : Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.CM.RationalTorsion
