module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Zero

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_zero_qk (hB : D.TauBimult) (k : ℕ) :
    ∃ p0 : QkPt D F k, p0.y = 0 ∧ p0.g.IsZero ∧ p0.g.IsAdd p0.g p0.g := by
  obtain ⟨g, hg⟩ := exists_zero_gt (D := D) (F := F)
  have hz := (isZero_iff g).1 hg
  have hface {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) (i : Fin 3)
      (a b : TF (R := R) F ⟶ D.P.A) :
      val D.cub.t (lift a b ≫ faceMap D.P.A i).left y J = 1 := by
    rw [Over.comp_left]
    exact (val_pull hJ D.cub.t (faceMap D.P.A i).left (lift a b).left).symm.trans
      ((val_corr hJ (D.cub.face i) (lift a b).left).trans (val_one _))
  have hadd : g.IsAdd g g := by
    rw [isAdd_iff]
    refine ⟨by rw [hz.1, _root_.mul_one], fun χ y J hJ => ?_⟩
    rw [hz.2 χ y J hJ, hz.1, _root_.one_mul, _root_.one_mul]
    have hm : lift (cP D (TF (R := R) F) χ) (lift 1 1) =
        lift (cP D (TF (R := R) F) χ) 1 ≫ faceMap D.P.A 2 := by
      simp [faceMap, x2, pzero, Hom.one_def]
    change val D.cub.t (lift (cP D (TF (R := R) F) χ) (lift 1 1)).left y J = 1
    rw [hm]
    exact hface hJ 2 _ _
  have hiota : GtPtF.IsIota (0 : D.X) g := by
    rw [isIota_iff]
    refine ⟨by rw [hz.1, cPoint_zero], fun χ y J hJ => ?_⟩
    have hc : th D y J 1 1 (cP D (TF (R := R) F) χ) = 1 := by
      have hm : lift 1 (lift 1 (cP D (TF (R := R) F) χ)) =
          lift 1 (cP D (TF (R := R) F) χ) ≫ faceMap D.P.A 0 := by
        simp [faceMap, x2, pzero, Hom.one_def]
      change val D.cub.t (lift 1 (lift 1 (cP D (TF (R := R) F) χ))).left y J = 1
      rw [hm]
      exact hface hJ 0 _ _
    have h1 := tau_mul (σ := 𝟙 (TF (R := R) F)) (z := y) (J := J) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, hc, _root_.mul_one] at h1
    rw [hz.2 χ y J hJ]
    exact (mul_eq_left.1 h1.symm).symm
  exact ⟨⟨0, g, ⟨g, ⟨fun _ => g, hg, fun _ => hadd, rfl⟩, hiota⟩⟩, rfl, hg, hadd⟩

end Zero

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
