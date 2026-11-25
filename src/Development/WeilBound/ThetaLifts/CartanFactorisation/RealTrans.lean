module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.CommuteConj
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

@[expose] public section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem ker_of_eq {Q P P₂ : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] [AddCommGroup P₂] [Module ℂ P₂]
    {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P} {p₂ : Q →ₗ[ℂ] P₂} (h : LinearMap.ker p ⊓ S = LinearMap.ker p₂ ⊓ S) :
    ∀ x ∈ S, p x = 0 ↔ p₂ x = 0 := fun x hx =>
  ⟨fun h0 => (h ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p ⊓ S) : x ∈ LinearMap.ker p₂ ⊓ S).1,
    fun h0 => (h.symm ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p₂ ⊓ S) : x ∈ LinearMap.ker p ⊓ S).1⟩

theorem max_uniq {α : Type} [SemilatticeSup α] {St : α → Prop} {S N N' : α} (hs : St (N ⊔ N'))
    (h : N ≠ S → N' ≠ S → N ⊔ N' ≠ S) (h1 : Maximal (fun P => St P ∧ P ≠ S) N) (h2 : Maximal (fun P => St P ∧ P ≠ S) N') :
    N = N' :=
  le_antisymm (le_sup_left.trans (h2.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_right)) (le_sup_right.trans (h1.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_left))

theorem real_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {R : RealMaps F a a'} {V V' W} (t : IsTriple B G X om om')
    (t₂ : IsTriple B (reG G V V' W) X om om') (r : IsRealMaps B G om om' R) {g g' h T T'} (hg : Moves B G.V V g)
    (hg' : Moves B G.V' V' g') (hh : Moves B G.W W h) (hT : IsArchOp om (g, h) T) (hT' : IsArchOp om' (g', h) T')
    (hP : ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = G.M.Pol B.ψ B.emb)
    (hP' : ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) = G.M'.Pol B.ψ B.emb) :
    IsRealMaps B (reG G V V' W) om om' ⟨R.Pi, R.p ∘ₗ (T : _ →ₗ[ℂ] _), R.p' ∘ₗ (T' : _ →ₗ[ℂ] _)⟩ := by
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m)
      (h' : ResEtaPow K χ' n) (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have pairV {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      res_div h.chars.resβ h.chars.resα rfl, h.weil⟩
  have pairV' {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩
  have quot_trans {n d : ℕ} {Y Y₂ : Spc F E n} {Z Z₂ : Spc F E d}
      {M : Model σ Y Z} {M₂ : Model σ (reS Y Y₂) (reS Z Z₂)}
      {χY χZ : Chr F E} {o : Rep σ Y Z} {u v u' v' : ℕ}
      (hp : IsPair B M χY χZ o u v u' v') (hp₂ : IsPair B M₂ χY χZ o u v u' v')
      {g h T} (hg : Moves B Y Y₂ g) (hT : IsArchOp o (g, h) T)
      (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb)
      {P : Type} [AddCommGroup P] [Module ℂ P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P}
      (q : RealQuot B M o p) : RealQuot B M₂ o (p ∘ₗ (T : _ →ₗ[ℂ] _)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.map_comp, hP, q.onto]
    · exact fun γ hγ f hf f₁ ha => q.lie _ (conj_line hg.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
        (transL hO hL hQ hp hp₂ hT hP (conj_line hg.1 hγ) one_line hγ one_line (fun t => cj1 g (γ t) h) hf ha)
    · exact fun k hk f hf f₁ ha => q.cpt _ (hg.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
        (transK hO hQ hp hT (hg.up hk).1 (one_at _) (cj1 g k h) ha)
  have p1 := pairV t
  have p2 := pairV' t
  have q1 := pairV t₂
  have q2 := pairV' t₂
  refine ⟨quot_trans p1 q1 hg hT hP r.quot, quot_trans p2 q2 hg' hT' hP' r.quot',
    fun γ hγ f hf f' hf' f₁ f₁' a1 a2 => r.lie _ (conj_line hh.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transL hO hL hQ p1 q1 hT hP one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g h (γ t)) hf a1)
      (transL hO hL hQ p2 q2 hT' hP' one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g' h (γ t)) hf' a2),
    fun k hk f hf f' hf' f₁ f₁' a1 a2 => r.cpt _ (hh.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transK hO hQ p1 hT (one_at _) (hh.up hk).1 (cj2 g h k) a1) (transK hO hQ p2 hT' (one_at _) (hh.up hk).1 (cj2 g' h k) a2),
    r.nontriv, fun N h1 h2 => r.irred N (fun γ hγ f hf y e hp => ?_) fun k hk f hf y e hp => ?_⟩
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := conj_line (re_inv hh.1) hγ
    obtain ⟨z, -, hz⟩ := pol_lie hO hL hQ q1 one_line l hu
    have := transL hO hL hQ p1 q1 hT hP one_line hγ one_line l (fun t => cj3 g h (γ t)) hu ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).2 _ e this]
    exact h1 _ l u hu z ((hz z).2 rfl) hp
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := hh.down hk
    obtain ⟨z, -, hz⟩ := pol_k hO hQ q1 (one_kinf _) l hu
    have := transK hO hQ p1 hT (one_at _) hk.1 (cj3 g h k) ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).1 _ e this]
    exact h2 _ l u hu z ((hz z).2 rfl) hp

theorem I_move (hI : ILeft) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W}
    {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s') {Φ} (hΦ : Φ ∈ schA F _) (g h x) :
    M.I o (o (g, h) Φ) x = M.I o Φ (x * h) := by
  rw [show (g, h) = ((g, 1) : UA σ Y.J × UA σ W.J) * (1, h) by simp, map_mul, Module.End.mul_apply,
    hI F E σ B n d Y W M χ χ' o r s r' s' hp _ (hp.weil.isUSplitting.pres _ _ hΦ), I_right]

theorem move_sum {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ} (hM : M.IsGood ψ) {o : Rep σ Y W} {x T}
    (hT : IsArchOp o x T) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ i v, φ i v ∈ SB _) (h2 : ∀ i, ∀ᶠ v in cofinite, φ i v = M.vac v) :
    o x (∑ i, pure (f i) (φ i)) = ∑ i, pure (T (f i)) (φ i) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨g, hg, e⟩ := pure_eq_pureA hM (φ i) (h1 i) (h2 i)
  rw [e, e, hT.1 _ g hg]

theorem so_re (V V' W) : G.M'.So B.ψ B.τ₁ ≤ (reG G V V' W).M'.So B.ψ B.τ₁ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, φ, h1, h2, ⟨h3, ι, h4, h5⟩, rfl⟩
  exact ⟨f, φ, h1, h2, ⟨h3, ι, ⟨h4.bij, h4.trans, h4.mult⟩, h5⟩, rfl⟩

end PositivityTheory.ThKF
