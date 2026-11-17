import GptLean.DFT

/-!
The convex-analysis core of `prop-zero-current-density-functional`.

The constraint space is a product `R × J` of densities and currents, and the
constrained search is even in the current, `search (ρ, -j) = search (ρ, j)`.

* If the search is convex, the current constraint can be dropped at zero
  current: `search (ρ, 0) = inf {E(s) : ρ_s = ρ}`. The midpoint of `(ρ, j)` and
  `(ρ, -j)` is `(ρ, 0)`, and both points carry the same value.
* For a pairing `⟨(u, a), (ρ, j)⟩ = ⟨u, ρ⟩ + ⟨a, j⟩` that is odd in the
  current, the Lieb supremum at zero current needs only scalar potentials:
  `lieb (ρ, 0) = sup_u [ground (u, 0) - ⟨u, ρ⟩]`. No convexity is used. The
  variational bounds at `(ρ', j)` and `(ρ', -j)` average to
  `ground (u, a) ≤ ground (u, 0)`.
* With an energy-preserving pure-to-mixed embedding and exact-pair pure
  recovery, the pure search at zero current is the density-only pure search.
-/

namespace GptLean.ZeroCurrent

open GptLean.DFT

variable {S M R J U W : Type*}

/-- Averaging the upper bounds `c + (r + t)` and `c + (r - t)` gives `c + r`. -/
theorem ereal_le_of_pm {x c : EReal} {r t : ℝ}
    (h₁ : x ≤ c + ((r + t : ℝ) : EReal)) (h₂ : x ≤ c + ((r - t : ℝ) : EReal)) :
    x ≤ c + (r : EReal) := by
  induction c using EReal.rec with
  | bot => simpa only [EReal.bot_add] using h₁
  | top => simp only [EReal.top_add_coe, le_top]
  | coe c =>
    induction x using EReal.rec with
    | bot => exact bot_le
    | top =>
      rw [← EReal.coe_add] at h₁
      exact absurd h₁ (not_le.mpr (EReal.coe_lt_top _))
    | coe x =>
      rw [← EReal.coe_add] at h₁ h₂ ⊢
      have h1 := EReal.coe_le_coe_iff.mp h₁
      have h2 := EReal.coe_le_coe_iff.mp h₂
      exact EReal.coe_le_coe_iff.mpr (by linarith)

section Search

variable [AddCommGroup R] [Module ℝ R] [AddCommGroup J] [Module ℝ J]

/-- A convex search that is even in the current is minimized over the current
at zero current, so the current constraint can be dropped there. -/
theorem search_zero_current (B : StateModel S (R × J)) (hconv : ConvexEpigraph (search B))
    (hsym : ∀ ρ j, search B (ρ, -j) = search B (ρ, j)) (ρ : R) :
    search B (ρ, 0) = search (densityOnly B) ρ := by
  apply le_antisymm
  · refine le_iInf₂ fun s hs => ?_
    have hs' : (B.density s).1 = ρ := hs
    have h₁ : ((((ρ, (B.density s).2) : R × J), B.energy s) : (R × J) × ℝ) ∈
        {p : (R × J) × ℝ | search B p.1 ≤ (p.2 : EReal)} :=
      search_le B (Prod.ext hs' rfl)
    have h₂ : ((((ρ, -(B.density s).2) : R × J), B.energy s) : (R × J) × ℝ) ∈
        {p : (R × J) × ℝ | search B p.1 ≤ (p.2 : EReal)} :=
      (hsym ρ _).le.trans h₁
    have hc := hconv h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hp : (1 / 2 : ℝ) • ((((ρ, (B.density s).2) : R × J), B.energy s) : (R × J) × ℝ) +
        (1 / 2 : ℝ) • ((((ρ, -(B.density s).2) : R × J), B.energy s) : (R × J) × ℝ) =
        (((ρ, 0) : R × J), B.energy s) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · simp only [Prod.fst_add, Prod.smul_fst]
        rw [← add_smul]
        norm_num
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_neg,
          add_neg_cancel]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        ring
    rw [hp] at hc
    exact hc
  · exact le_iInf₂ fun s hs => search_le (densityOnly B) (congrArg Prod.fst hs)

/-- If the search is attained wherever it is finite, the density-only search
is attained at zero current. -/
theorem attained_zero_current (B : StateModel S (R × J)) (hconv : ConvexEpigraph (search B))
    (hsym : ∀ ρ j, search B (ρ, -j) = search B (ρ, j)) (ρ : R)
    (hatt : search B (ρ, 0) < ⊤ → Attained B (ρ, 0))
    (hfin : search (densityOnly B) ρ < ⊤) :
    ∃ s, B.density s = (ρ, 0) ∧ (B.energy s : EReal) = search (densityOnly B) ρ := by
  rw [← search_zero_current B hconv hsym ρ] at hfin ⊢
  exact hatt hfin

/-- With exact-pair pure recovery the pure search at zero current is the
density-only pure search. -/
theorem pure_zero_current (A : StateModel S (R × J)) (B : StateModel M (R × J))
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B)
    (hconv : ConvexEpigraph (search B))
    (hsym : ∀ ρ j, search B (ρ, -j) = search B (ρ, j)) (ρ : R) :
    search A (ρ, 0) = search (densityOnly A) ρ := by
  have emb' : PureEmbedding (densityOnly A) (densityOnly B) :=
    { toMixed := emb.toMixed
      energy_eq := emb.energy_eq
      density_eq := fun s => congrArg Prod.fst (emb.density_eq s) }
  have recovery' : ExactRecovery (densityOnly A) (densityOnly B) := by
    intro m ε hε
    obtain ⟨s, hs, hes⟩ := recovery m ε hε
    exact ⟨s, congrArg Prod.fst hs, hes⟩
  calc
    search A (ρ, 0) = search B (ρ, 0) := pure_eq_mixed A B emb recovery _
    _ = search (densityOnly B) ρ := search_zero_current B hconv hsym ρ
    _ = search (densityOnly A) ρ :=
      (pure_eq_mixed (densityOnly A) (densityOnly B) emb' recovery' ρ).symm

end Search

section Dual

variable [AddCommGroup J] [Zero W]

/-- Evenness of the search in the current makes the vector potential raise
nothing: `ground (u, a) ≤ ground (u, 0)`. -/
theorem ground_le_scalar (A : StateModel S (R × J)) (pair : U × W → R × J → ℝ)
    (p₁ : U → R → ℝ) (p₂ : W → J → ℝ) (hpair : ∀ v d, pair v d = p₁ v.1 d.1 + p₂ v.2 d.2)
    (hneg : ∀ a j, p₂ a (-j) = -p₂ a j) (hzero : ∀ j, p₂ 0 j = 0)
    (hsym : ∀ ρ j, search A (ρ, -j) = search A (ρ, j)) (u : U) (a : W) :
    ground A pair (u, a) ≤ ground A pair (u, 0) := by
  rw [density_variational_principle A pair (u, a), density_variational_principle A pair (u, 0)]
  refine le_iInf fun d => ?_
  obtain ⟨ρ', j⟩ := d
  have h₁ : (⨅ d', search A d' + (pair (u, a) d' : EReal)) ≤
      search A (ρ', j) + ((p₁ u ρ' + p₂ a j : ℝ) : EReal) := by
    refine (iInf_le _ (ρ', j)).trans_eq ?_
    rw [hpair]
  have h₂ : (⨅ d', search A d' + (pair (u, a) d' : EReal)) ≤
      search A (ρ', j) + ((p₁ u ρ' - p₂ a j : ℝ) : EReal) := by
    refine (iInf_le _ (ρ', -j)).trans_eq ?_
    rw [hsym ρ' j, hpair]
    simp only [hneg, sub_eq_add_neg]
  refine (ereal_le_of_pm h₁ h₂).trans_eq ?_
  rw [hpair]
  simp only [hzero, add_zero]

/-- **The scalar dual at zero current.** -/
theorem lieb_zero_current (A : StateModel S (R × J)) (pair : U × W → R × J → ℝ)
    (p₁ : U → R → ℝ) (p₂ : W → J → ℝ) (hpair : ∀ v d, pair v d = p₁ v.1 d.1 + p₂ v.2 d.2)
    (hneg : ∀ a j, p₂ a (-j) = -p₂ a j) (hzero : ∀ j, p₂ 0 j = 0)
    (hsym : ∀ ρ j, search A (ρ, -j) = search A (ρ, j)) (ρ : R) :
    lieb A pair (ρ, 0) = ⨆ u : U, ground A pair (u, 0) - (p₁ u ρ : EReal) := by
  have hp (v : U × W) : pair v (ρ, 0) = p₁ v.1 ρ := by
    have h0 : p₂ v.2 0 = 0 := by
      have h := hneg v.2 0
      rw [neg_zero] at h
      linarith
    rw [hpair]
    exact (congrArg (fun t => p₁ v.1 ρ + t) h0).trans (add_zero _)
  apply le_antisymm
  · refine iSup_le fun v => ?_
    rw [hp v]
    refine le_trans ?_ (le_iSup (fun u : U => ground A pair (u, 0) - (p₁ u ρ : EReal)) v.1)
    exact EReal.sub_le_sub (ground_le_scalar A pair p₁ p₂ hpair hneg hzero hsym v.1 v.2) le_rfl
  · refine iSup_le fun u => ?_
    refine le_trans ?_ (le_iSup (fun v : U × W => ground A pair v - (pair v (ρ, 0) : EReal)) (u, 0))
    rw [hp (u, 0)]

end Dual

end GptLean.ZeroCurrent
