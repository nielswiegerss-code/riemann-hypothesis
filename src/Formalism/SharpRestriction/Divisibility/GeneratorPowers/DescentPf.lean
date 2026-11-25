module

public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Lin

variable {k : Type} [CommRing k] {n : ℕ}

theorem DpolyN_sub {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ e ∈ S, MvPowerSeries.C (P.coeff e) * DmonN F cp u e g := by
  unfold DpolyN
  refine Finset.sum_subset hS (fun e _ he => ?_)
  have h0 : P.coeff e = 0 := by simpa using he
  rw [h0, map_zero, zero_mul]

theorem DpolyN_addP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P Q : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [DpolyN_sub F cp u (P + Q) g (P.support ∪ Q.support) MvPolynomial.support_add,
    DpolyN_sub F cp u P g (P.support ∪ Q.support) Finset.subset_union_left,
    DpolyN_sub F cp u Q g (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem DpolyN_smulP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (c : k) (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (c • P) g = c • DpolyN F cp u P g := by
  rw [DpolyN_sub F cp u (c • P) g P.support MvPolynomial.support_smul,
    DpolyN_sub F cp u P g P.support subset_rfl, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, mul_assoc, ← MvPowerSeries.smul_eq_C_mul]

end Lin

theorem nabValN_addP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (P Q : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (P + Q) = nabValN B k h w0 m f cp u P + nabValN B k h w0 m f cp u Q := by
  unfold nabValN
  rw [DpolyN_addP, map_add (f := _)]

theorem nabValN_smulP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (c : k) (P : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (c • P) = c * nabValN B k h w0 m f cp u P := by
  unfold nabValN
  rw [DpolyN_smulP, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

end Gen

end Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf
