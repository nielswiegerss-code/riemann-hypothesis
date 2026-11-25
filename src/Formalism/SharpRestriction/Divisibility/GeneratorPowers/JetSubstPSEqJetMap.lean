module

import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet

variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']

theorem psJet_coe (m : ℕ) (P : MvPolynomial κ S) : psJet m (P : MvPowerSeries κ S) = Ideal.Quotient.mk _ P := by
  unfold psJet
  rw [psTrunc_eq]
  exact mk_trunc_coe m P

theorem jetSubstPS_X (m : ℕ) (P : κ → MvPowerSeries κ' S) (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (i : κ) : jetSubstPS (m := m) P (Ideal.Quotient.mk _ (X i)) = psJet m (P i) := by
  unfold jetSubstPS
  rw [jetMap_mk, MvPolynomial.aeval_X, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', hP i, map_zero, sub_zero]
  rfl

theorem jetSubstPS_eq_jetMap (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    jetSubstPS (m := m) Q = jetMap (fun i => psTrunc m (Q i)) (fun i => psTrunc_mem_orig m (Q i) (hQ i)) := by
  apply _root_.Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.jetSubstPS_eq <;> assumption

theorem jetSubstPS_psJet (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) : jetSubstPS (m := m) Q (psJet m f) = psJet m (MvPowerSeries.subst Q f) := by
  rw [jetSubstPS_eq_jetMap m Q hQ, psJet_subst m Q hQ f]

theorem const_substPS (Q : κ' → MvPowerSeries κ'' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ' S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst Q f) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ) hQ hf

theorem jetSubstPS_comp (m : ℕ) (P : κ → MvPowerSeries κ' S) (Q : κ' → MvPowerSeries κ'' S)
    (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    (jetSubstPS (m := m) Q).comp (jetSubstPS (m := m) P) =
      jetSubstPS (m := m) (fun i => MvPowerSeries.subst Q (P i)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m P hP i, jetSubstPS_psJet m Q hQ,
    jetSubstPS_X m _ (fun i => const_substPS Q hQ (P i) (hP i)) i]

theorem jetSubstP_eq_jetSubstPS (m : ℕ) (σ : κ → MvPolynomial κ' S) (hσ : ∀ i, MvPolynomial.constantCoeff (σ i) = 0) :
    jetSubstP m σ = jetSubstPS (m := m) (fun i => (σ i : MvPowerSeries κ' S)) := by
  apply _root_.Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.jetSubstP_eq_jetSubstPS <;> assumption

theorem jetCopy_eq_PS {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ (fun p => MvPowerSeries.constantCoeff_X _) p, ← MvPolynomial.coe_X, psJet_coe]
  unfold jetCopy
  rw [jetMap_mk, MvPolynomial.aeval_X]

theorem psJet_subst_trunc (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) :
    psJet m (MvPowerSeries.subst Q ((psTrunc m f : MvPolynomial κ S) : MvPowerSeries κ S)) =
      psJet m (MvPowerSeries.subst Q f) := by
  rw [psJet_subst m Q hQ, psJet_subst m Q hQ, psJet_coe]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
