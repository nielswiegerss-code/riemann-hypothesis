module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Mathlib.Data.Finsupp.Pointwise
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullGenG

theorem hasGen_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) :
    HasGen Lr.L (lf (Finsupp.single (1 : G ⟶ G) 1)) := by
  have h0 := (HasGen.of_gen (L := Lr.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) Lr.rig Lr.rigGen).pull G.hom
  have e1 : (1 : G ⟶ G).left = G.hom ≫ eSec G := rfl
  convert h0 using 1
  rw [lf_single, e1]
  simp [fsum, Finsupp.mapDomain_single]

theorem hasGen_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (cub : CubicalStr G Lr)
    {O : Type} [CommRing O] [StarRing O] (ra : RingAct G O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hadj : Geo.Tor.LBIso (cubeLB G ![fst G G ≫ ra.act a, snd G G] Lr.L)
      (cubeLB G ![fst G G, snd G G ≫ ra.act (star a)] Lr.L))
    (hprim : Geo.Tor.LBIso Lr.L (cubeLB G ![𝟙 G, ra.act w0] Lr.L)) (k : ℕ) :
    HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, (ra.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := by
  have := ra.hom w0
  obtain ⟨uR, huR⟩ := GlobalTheory.NormRos.exists_gen_rosati Lr.isLB (ra.act a) (ra.act (star a)) hadj
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G Lr (ra.act w0) hprim
  have hP : HasGen Lr.L (fsum (GlobalTheory.JetSer.primφ (ra.act w0)) GlobalTheory.JetSer.primε) := HasGen.of_gen ρ hρ
  have h1 := hasGen_one Lr
  obtain ⟨uΨ, huΨ⟩ := HasGen.gen Lr.isLB (h1.sub hP) (K' := Fin 4)
    ![(padd G (𝟙 _) (ra.act w0)).left, 𝟙 G.left, (ra.act w0).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      unfold GlobalTheory.JetSer.primφ GlobalTheory.JetSer.primε
      have e1 : toUnit G ≫ η[G] = (1 : G ⟶ G) := rfl
      rw [padd_eq_mul, e1, lf_single]
      classical
      ext x
      simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
      split_ifs <;> omega)
  have hM := hasGen_pullMul ra w0 a N hN uΨ huΨ uR huR cub.t cub.isGen
  have h2 := (hM.zsmul (-(k : ℤ))).add (h1.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  convert h2 using 1
  classical
  simp only [lf_add, lf_sub, lf_smul, lf_single]
  ext x
  simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
  split_ifs <;> ring

end GlobalTheory.PullGenG
