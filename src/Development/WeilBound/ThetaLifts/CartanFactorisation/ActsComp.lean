module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem one_at {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := fun u _ => by simp [mat]

theorem one_kinf {m : ℕ} {Y : Spc F E m} (τ) : (1 : UA σ Y.J) ∈ KInf σ Y τ :=
  ⟨one_at _, fun w => by
    have : (mat (1 : UA σ Y.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _⟩

theorem one_line {m : ℕ} {Y : Spc F E m} : (1 : Multiplicative ℝ →* UA σ Y.J) ∈ Lines σ Y :=
  ⟨continuous_const, fun _ => one_at _⟩

theorem acts_comp (hp : IsPair B M χX χW om r s r' s') {x y} {f g k : SInf F (Fin n × Fin d)}
    (h1 : Acts (evI F) (om y) f g) (h2 : Acts (evI F) (om x) g k) : Acts (evI F) (om (x * y)) f k := fun r hr => by
  rw [map_mul, Module.End.mul_apply, h1 r hr]
  exact h2 r ⟨hr.1, h1 r hr ▸ hp.weil.isUSplitting.pres _ _ hr.2⟩

theorem sinf_ext {κ : Type} [Fintype κ] {f g : SInf F κ} (h : ∀ L : SInf F κ →L[ℂ] ℂ, L f = L g) : f = g := by
  classical
  refine SchwartzMap.ext fun x => ?_
  exact h ((BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _))

theorem exists_L (hp : IsPair B M χX χW om r s r' s') {𝓒} (hc : Cls B M om 𝓒) {ψ} (hψ : ψ ∈ SB (Fin n × Fin d → Af F))
    (h𝓒 : ∀ f : SInf F (Fin n × Fin d), pureA F f ψ ∈ 𝓒) :
    ∃ L : UA σ W.J → SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ h f, L h f = M.I om (pureA F f ψ) h :=
  ⟨fun h =>
    { toFun := fun f => M.I om (pureA F f ψ) h
      map_add' := fun f g => by
        have : pureA F ⇑(f + g) ψ = pureA F f ψ + pureA F g ψ := by funext x; simp [pureA, add_mul]
        rw [this, I_add' hp hc (h𝓒 f) (h𝓒 g)]; rfl
      map_smul' := fun c f => by
        have : pureA F ⇑(c • f) ψ = c • pureA F f ψ := by funext x; simp [pureA, mul_assoc]
        rw [this, PositivityTheory.ThKG.I_smul]; rfl
      cont := hc.contf ψ hψ h𝓒 h }, fun _ _ => rfl⟩


end PositivityTheory.ThKF
