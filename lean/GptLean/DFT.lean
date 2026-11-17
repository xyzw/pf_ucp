import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Linarith

/-!
The constrained-search and convex-duality implications of `qedft.tex`.

States have finite real energy. The search itself takes values in `EReal`,
so empty fibers have value `⊤` and no attainment is silently assumed.
The density space and the state spaces are abstract. In particular this file
does not construct the Pauli–Fierz form domain or prove the paper's compactness,
soft-photon recovery, or lower-semicontinuity estimates.

The final equality theorem separates three inputs. An energy-preserving
pure-to-mixed embedding and exact-density pure recovery are the inputs from
Pauli–Fierz analysis. Mixed-search closedness is the article's compactness
input. Fenchel–Moreau is supplied as a universally quantified convex-analysis
fact, rather than assuming the equality of the particular functionals.

Attribution. The earlier `claude_lean/QEDFT/DFT/ConstrainedSearch.lean` was
consulted for the finite-translation `EReal` API and for the epigraph proof
pattern. This module is independent and imports no `QEDFT` modules.
-/

namespace GptLean.DFT

variable {S M D V : Type*}

/-- Internal energy and the complete density/current constraint. -/
structure StateModel (S D : Type*) where
  energy : S → ℝ
  density : S → D

noncomputable def search (A : StateModel S D) (d : D) : EReal :=
  ⨅ s : S, ⨅ (_ : A.density s = d), (A.energy s : EReal)

noncomputable def ground (A : StateModel S D) (pair : V → D → ℝ) (v : V) : EReal :=
  ⨅ s : S, ((A.energy s + pair v (A.density s) : ℝ) : EReal)

noncomputable def lieb (A : StateModel S D) (pair : V → D → ℝ) (d : D) : EReal :=
  ⨆ v : V, ground A pair v - (pair v d : EReal)

def Attained (A : StateModel S D) (d : D) : Prop :=
  ∃ s, A.density s = d ∧ (A.energy s : EReal) = search A d

theorem search_le (A : StateModel S D) {s : S} {d : D}
    (hd : A.density s = d) : search A d ≤ (A.energy s : EReal) :=
  iInf₂_le s hd

theorem search_eq_top_iff (A : StateModel S D) (d : D) :
    search A d = ⊤ ↔ ∀ s, A.density s ≠ d := by
  simp only [search, iInf_eq_top, EReal.coe_ne_top, imp_false]

/-- This is finite-from-above representability. A lower energy bound rules out `⊥`. -/
theorem representable_iff (A : StateModel S D) (d : D) :
    search A d < ⊤ ↔ d ∈ Set.range A.density := by
  rw [lt_top_iff_ne_top, Ne, search_eq_top_iff]
  simp [Set.mem_range]

theorem lower_bound (A : StateModel S D) (b : ℝ)
    (hb : ∀ s, b ≤ A.energy s) (d : D) : (b : EReal) ≤ search A d := by
  exact le_iInf₂ fun s _ => EReal.coe_le_coe (hb s)

theorem search_ne_bot (A : StateModel S D) (b : ℝ)
    (hb : ∀ s, b ≤ A.energy s) (d : D) : search A d ≠ ⊥ := by
  exact ne_of_gt ((EReal.bot_lt_coe b).trans_le (lower_bound A b hb d))

/-- Equation `density-variational-principle` after the diamagnetic reparametrization. -/
theorem density_variational_principle (A : StateModel S D)
    (pair : V → D → ℝ) (v : V) :
    ground A pair v = ⨅ d : D, search A d + (pair v d : EReal) := by
  apply le_antisymm
  · refine le_iInf fun d => ?_
    apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))).mp
    refine le_iInf₂ fun s hs => ?_
    apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))).mpr
    calc
      ground A pair v ≤ ((A.energy s + pair v (A.density s) : ℝ) : EReal) :=
        iInf_le _ s
      _ = (A.energy s : EReal) + (pair v d : EReal) := by rw [hs, EReal.coe_add]
  · refine le_iInf fun s => ?_
    calc
      (⨅ d : D, search A d + (pair v d : EReal)) ≤
          search A (A.density s) + (pair v (A.density s) : EReal) :=
        iInf_le _ (A.density s)
      _ ≤ (A.energy s : EReal) + (pair v (A.density s) : EReal) :=
        add_le_add (search_le A rfl) le_rfl
      _ = _ := (EReal.coe_add _ _).symm

/-- Equation `L-vs-LL`, the weak-duality half. -/
theorem lieb_le_search (A : StateModel S D) (pair : V → D → ℝ) (d : D) :
    lieb A pair d ≤ search A d := by
  refine iSup_le fun v => EReal.sub_le_of_le_add ?_
  rw [density_variational_principle]
  exact iInf_le _ d

theorem potential_lower_bound (A : StateModel S D) (pair : V → D → ℝ)
    (v : V) (d : D) : ground A pair v - (pair v d : EReal) ≤ lieb A pair d :=
  le_iSup (fun v => ground A pair v - (pair v d : EReal)) v

/-- Convex relaxation leaves the variational energy unchanged, including infinite values. -/
theorem lieb_variational_principle (A : StateModel S D)
    (pair : V → D → ℝ) (v : V) :
    ground A pair v = ⨅ d : D, lieb A pair d + (pair v d : EReal) := by
  apply le_antisymm
  · refine le_iInf fun d => ?_
    exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))).mp (potential_lower_bound A pair v d)
  · rw [density_variational_principle]
    exact iInf_mono fun d => add_le_add (lieb_le_search A pair d) le_rfl

/-- The discussion of pure ground states after `prop-pure-nonattainment`. -/
theorem ground_state_attains (A : StateModel S D) (pair : V → D → ℝ)
    (s : S) (v : V)
    (hs : ∀ t, A.energy s + pair v (A.density s) ≤
      A.energy t + pair v (A.density t)) :
    Attained A (A.density s) := by
  refine ⟨s, rfl, le_antisymm ?_ (search_le A rfl)⟩
  refine le_iInf₂ fun t ht => EReal.coe_le_coe ?_
  have h := hs t
  rw [ht] at h
  linarith

/-- An embedding models rank-one density matrices and preserves both observables. -/
structure PureEmbedding (A : StateModel S D) (B : StateModel M D) where
  toMixed : S → M
  energy_eq : ∀ s, B.energy (toMixed s) = A.energy s
  density_eq : ∀ s, B.density (toMixed s) = A.density s

theorem mixed_le_pure (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (d : D) : search B d ≤ search A d := by
  refine le_iInf₂ fun s hs => ?_
  simpa only [emb.energy_eq] using
    (search_le B ((emb.density_eq s).trans hs))

/-- The precise analytic recovery input in `many-electron-pure-approximation`.
This is not asserted as an axiom or proved for continuum Pauli–Fierz states here. -/
def ExactRecovery (A : StateModel S D) (B : StateModel M D) : Prop :=
  ∀ m (ε : ℝ), 0 < ε → ∃ s,
    A.density s = B.density m ∧ A.energy s ≤ B.energy m + ε

/-- Taking an arbitrarily small positive real error works even if the LHS is infinite. -/
theorem ereal_le_of_epsilon {x : EReal} {a : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → x ≤ ((a + ε : ℝ) : EReal)) : x ≤ (a : EReal) := by
  by_contra hn
  obtain ⟨b, hab, hbx⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hab' : a < b := EReal.coe_lt_coe_iff.mp hab
  have hx := h (b - a) (sub_pos.mpr hab')
  have he : a + (b - a) = b := by ring
  rw [he] at hx
  exact (not_le_of_gt hbx) hx

/-- The equality-of-infima implication in `thm-many-electron-soft-purification`. -/
theorem pure_eq_mixed (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B) (d : D) :
    search A d = search B d := by
  refine le_antisymm ?_ (mixed_le_pure A B emb d)
  refine le_iInf₂ fun m hm => ereal_le_of_epsilon fun ε hε => ?_
  obtain ⟨s, hs, he⟩ := recovery m ε hε
  exact (search_le A (hs.trans hm)).trans (EReal.coe_le_coe he)

/-- Equality of pure/mixed representability is stronger than merely closure equality. -/
theorem pure_mixed_representability (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B) :
    Set.range A.density = Set.range B.density := by
  ext d
  rw [← representable_iff A d, ← representable_iff B d,
    pure_eq_mixed A B emb recovery]

/-- `rank-one` here means precisely the image of the supplied pure embedding. -/
theorem pure_attained_iff_rank_one (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B) (d : D) :
    Attained A d ↔ ∃ m, m ∈ Set.range emb.toMixed ∧
      B.density m = d ∧ (B.energy m : EReal) = search B d := by
  constructor
  · rintro ⟨s, hs, he⟩
    refine ⟨emb.toMixed s, ⟨s, rfl⟩, (emb.density_eq s).trans hs, ?_⟩
    rw [emb.energy_eq, he, pure_eq_mixed A B emb recovery]
  · rintro ⟨_, ⟨s, rfl⟩, hs, he⟩
    refine ⟨s, ?_, ?_⟩
    · simpa only [emb.density_eq] using hs
    · simpa only [emb.energy_eq, pure_eq_mixed A B emb recovery] using he

/-- Equal constrained searches have equal potential energies and Lieb conjugates. -/
theorem ground_eq_of_search_eq (A : StateModel S D) (B : StateModel M D)
    (pair : V → D → ℝ) (h : ∀ d, search A d = search B d) (v : V) :
    ground A pair v = ground B pair v := by
  simp only [density_variational_principle, h]

theorem lieb_eq_of_search_eq (A : StateModel S D) (B : StateModel M D)
    (pair : V → D → ℝ) (h : ∀ d, search A d = search B d) (d : D) :
    lieb A pair d = lieb B pair d := by
  simp only [lieb, ground_eq_of_search_eq A B pair h]

section ConvexDuality

variable [AddCommGroup D] [Module ℝ D]

/-- Epigraph convexity avoids undefined arithmetic involving `0 * ∞`. -/
def ConvexEpigraph (f : D → EReal) : Prop :=
  Convex ℝ {p : D × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- The standard density-matrix mixture operation, stated without constructing operators. -/
def MixtureClosed (B : StateModel M D) : Prop :=
  ∀ m n (t u : ℝ), 0 ≤ t → 0 ≤ u → t + u = 1 →
    ∃ p, B.density p = t • B.density m + u • B.density n ∧
      B.energy p ≤ t * B.energy m + u * B.energy n

omit [AddCommGroup D] [Module ℝ D] in
theorem approximate_search_upper_bound (A : StateModel S D) {d : D} {a ε : ℝ}
    (ha : search A d ≤ (a : EReal)) (hε : 0 < ε) :
    ∃ s, A.density s = d ∧ A.energy s < a + ε := by
  have h : search A d < ((a + ε : ℝ) : EReal) :=
    ha.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  simpa only [search, iInf_lt_iff, EReal.coe_lt_coe_iff, exists_prop] using h

/-- Convexity of the mixed search follows from mixing approximate minimizers.
In particular this result does not assume mixed attainment. -/
theorem mixed_search_convex (B : StateModel M D) (hmix : MixtureClosed B) :
    ConvexEpigraph (search B) := by
  rintro ⟨d, a⟩ hd ⟨d', a'⟩ hd' t u ht hu hsum
  change search B d ≤ (a : EReal) at hd
  change search B d' ≤ (a' : EReal) at hd'
  change search B (t • d + u • d') ≤ ((t * a + u * a' : ℝ) : EReal)
  apply ereal_le_of_epsilon
  intro ε hε
  obtain ⟨m, hm, he⟩ := approximate_search_upper_bound B hd hε
  obtain ⟨n, hn, he'⟩ := approximate_search_upper_bound B hd' hε
  obtain ⟨p, hp, hep⟩ := hmix m n t u ht hu hsum
  rw [hm, hn] at hp
  apply (search_le B hp).trans
  apply EReal.coe_le_coe
  have h1 := mul_le_mul_of_nonneg_left he.le ht
  have h2 := mul_le_mul_of_nonneg_left he'.le hu
  have heps : t * ε + u * ε = ε := by rw [← add_mul, hsum, one_mul]
  nlinarith

/-- Convexity of the representability class follows directly from exact mixed-state mixing. -/
theorem mixed_range_convex (B : StateModel M D) (hmix : MixtureClosed B) :
    Convex ℝ (Set.range B.density) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ t u ht hu hsum
  obtain ⟨p, hp, _⟩ := hmix m n t u ht hu hsum
  exact ⟨p, hp⟩

theorem pure_range_convex (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B)
    (hmix : MixtureClosed B) : Convex ℝ (Set.range A.density) := by
  rw [pure_mixed_representability A B emb recovery]
  exact mixed_range_convex B hmix

theorem pure_search_convex (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B)
    (hmix : MixtureClosed B) : ConvexEpigraph (search A) := by
  have heq : search A = search B := funext (pure_eq_mixed A B emb recovery)
  rw [heq]
  exact mixed_search_convex B hmix

theorem lieb_convex (A : StateModel S D) (pair : V → D →ₗ[ℝ] ℝ) :
    ConvexEpigraph (lieb A fun v d => pair v d) := by
  rintro ⟨d, a⟩ hd ⟨d', a'⟩ hd' t t' ht ht' hsum
  change lieb A (fun v d => pair v d) d ≤ (a : EReal) at hd
  change lieb A (fun v d => pair v d) d' ≤ (a' : EReal) at hd'
  change lieb A (fun v d => pair v d) (t • d + t' • d') ≤
    ((t * a + t' * a' : ℝ) : EReal)
  refine iSup_le fun v => ?_
  have h := (potential_lower_bound A (fun v d => pair v d) v d).trans hd
  have h' := (potential_lower_bound A (fun v d => pair v d) v d').trans hd'
  generalize ground A (fun v d => pair v d) v = c at h h' ⊢
  induction c with
  | bot => simp
  | top => simp at h
  | coe c =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h h' ⊢
    simp only [map_add, map_smul, smul_eq_mul]
    have hc : c = t * c + t' * c := by rw [← add_mul, hsum, one_mul]
    have h1 := mul_le_mul_of_nonneg_left h ht
    have h2 := mul_le_mul_of_nonneg_left h' ht'
    linarith

variable [TopologicalSpace D]

omit [AddCommGroup D] [Module ℝ D] in
theorem lieb_lowerSemicontinuous (A : StateModel S D) (pair : V → D → ℝ)
    (hc : ∀ v, Continuous (pair v)) : LowerSemicontinuous (lieb A pair) := by
  apply lowerSemicontinuous_iSup
  intro v
  suffices Continuous (fun d => ground A pair v - (pair v d : EReal)) from
    this.lowerSemicontinuous
  generalize ground A pair v = c
  induction c with
  | bot => simpa only [EReal.bot_sub] using continuous_const
  | top => simpa only [EReal.top_sub_coe] using continuous_const
  | coe c =>
    simp only [← EReal.coe_sub]
    exact continuous_coe_real_ereal.comp (continuous_const.sub (hc v))

omit [AddCommGroup D] [Module ℝ D] in
theorem pure_search_lowerSemicontinuous (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B)
    (hlsc : LowerSemicontinuous (search B)) : LowerSemicontinuous (search A) := by
  have heq : search A = search B := funext (pure_eq_mixed A B emb recovery)
  rw [heq]
  exact hlsc

noncomputable def biconjugate (pair : V → D → ℝ) (f : D → EReal) (d : D) : EReal :=
  ⨆ v : V, (⨅ x : D, f x + (pair v x : EReal)) - (pair v d : EReal)

/-- The standard theorem is quantified over all proper closed convex functions.
The application must supply a separating continuous dual pairing and its theorem. -/
def FenchelMoreau (pair : V → D → ℝ) : Prop :=
  ∀ f : D → EReal,
    (∀ d, f d ≠ ⊥) → (∃ d, f d ≠ ⊤) →
    ConvexEpigraph f → LowerSemicontinuous f → ∀ d, f d = biconjugate pair f d

theorem mixed_eq_lieb (B : StateModel M D) (pair : V → D → ℝ)
    (fm : FenchelMoreau pair) (b : ℝ) (hb : ∀ m, b ≤ B.energy m)
    (m₀ : M) (hconvex : ConvexEpigraph (search B))
    (hlsc : LowerSemicontinuous (search B)) (d : D) :
    search B d = lieb B pair d := by
  have hproper : ∃ x, search B x ≠ ⊤ := by
    refine ⟨B.density m₀, ne_of_lt ?_⟩
    exact (search_le B rfl).trans_lt (EReal.coe_lt_top _)
  have h := fm (search B) (search_ne_bot B b hb) hproper hconvex hlsc d
  simpa only [biconjugate, ← density_variational_principle, lieb] using h

/-- Main functional equality, conditional on the explicitly listed analytic inputs.
In particular mixed lower semicontinuity is an unproved article-specific input. -/
theorem pure_eq_lieb (A : StateModel S D) (B : StateModel M D)
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B)
    (pair : V → D → ℝ) (fm : FenchelMoreau pair)
    (b : ℝ) (hb : ∀ m, b ≤ B.energy m) (m₀ : M)
    (hconvex : ConvexEpigraph (search B))
    (hlsc : LowerSemicontinuous (search B)) (d : D) :
    search A d = lieb A pair d := by
  calc
    search A d = search B d := pure_eq_mixed A B emb recovery d
    _ = lieb B pair d := mixed_eq_lieb B pair fm b hb m₀ hconvex hlsc d
    _ = lieb A pair d := (lieb_eq_of_search_eq A B pair
      (pure_eq_mixed A B emb recovery) d).symm

end ConvexDuality

/-- Core of `prop-zero-current-density-functional`. Averaging with time reversal
must supply `symmetrize`, preserve the density, kill the current, and not raise energy. -/
theorem zero_current_search_eq_density_search {R J : Type*} [Zero J]
    (A : StateModel S (R × J)) (symmetrize : S → S)
    (hd : ∀ s, (A.density (symmetrize s)).1 = (A.density s).1)
    (hj : ∀ s, (A.density (symmetrize s)).2 = 0)
    (he : ∀ s, A.energy (symmetrize s) ≤ A.energy s) (ρ : R) :
    search A (ρ, 0) =
      search { energy := A.energy, density := fun s => (A.density s).1 } ρ := by
  apply le_antisymm
  · refine le_iInf₂ fun s hs => ?_
    have hpair : A.density (symmetrize s) = (ρ, 0) :=
      Prod.ext ((hd s).trans hs) (hj s)
    exact (search_le A hpair).trans (EReal.coe_le_coe (he s))
  · refine le_iInf₂ fun s hs => ?_
    exact search_le _ (congrArg Prod.fst hs)

/-- Forgetting the current is an actual change in the constraint, not in the states. -/
def densityOnly {R J : Type*} (A : StateModel S (R × J)) : StateModel S R :=
  { energy := A.energy, density := fun s => (A.density s).1 }

/-- For pure states the zero-current reduction uses mixed symmetrization followed
by exact-pair soft recovery. It does not assume that pure states can be averaged. -/
theorem pure_zero_current_search {R J : Type*} [Zero J]
    (A : StateModel S (R × J)) (B : StateModel M (R × J))
    (emb : PureEmbedding A B) (recovery : ExactRecovery A B)
    (symmetrize : M → M)
    (hd : ∀ m, (B.density (symmetrize m)).1 = (B.density m).1)
    (hj : ∀ m, (B.density (symmetrize m)).2 = 0)
    (he : ∀ m, B.energy (symmetrize m) ≤ B.energy m) (ρ : R) :
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
    _ = search (densityOnly B) ρ :=
      zero_current_search_eq_density_search B symmetrize hd hj he ρ
    _ = search (densityOnly A) ρ :=
      (pure_eq_mixed (densityOnly A) (densityOnly B) emb' recovery' ρ).symm

end GptLean.DFT
