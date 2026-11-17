import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Vector
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected



/-!
Geometry used in the exact soft-photon removal proof.
Adapted from claude_lean/QEDFT/Attainment/Clusters.lean and checked against
current qedft.tex, proof of lem-exact-soft-removal, Steps 1, 3 and 4.

This proves the finite active-partition algebra, cluster graph diameter,
cutoff derivative bounds, and the phase/residual-velocity identities.
The lattice partition's local finiteness and Sobolev behavior on zero sets
remain analytic inputs. The norm-gradient statement below concerns only
strictly positive fiber weights.
-/

namespace GptLean.RemovalGeometry

open Finset
open scoped InnerProductSpace



section Localization

variable {A : Type*} {N : ℕ}


theorem sum_prod_weights_eq_one [Fintype A] (w : A → Fin N → ℝ) (hw : ∀ i, ∑ a, w a i = 1) :
    ∑ f : Fin N → A, ∏ i, w (f i) i = 1 := by
  rw [← Fintype.prod_sum (fun i a => w a i)]
  simp [hw]


def valueSym (f : Fin N → A) : Sym A N :=
  ⟨(univ : Finset (Fin N)).val.map f, by simp⟩


noncomputable def multisetWeight [Fintype A] [DecidableEq A] (w : A → Fin N → ℝ)
    (lam : Sym A N) : ℝ :=
  ∑ f ∈ univ.filter (fun f : Fin N → A => valueSym f = lam), ∏ i, w (f i) i


theorem sum_multisetWeight_eq_one [Fintype A] [DecidableEq A] (w : A → Fin N → ℝ)
    (hw : ∀ i, ∑ a, w a i = 1) :
    ∑ lam : Sym A N, multisetWeight w lam = 1 := by
  unfold multisetWeight
  rw [Finset.sum_fiberwise]
  exact sum_prod_weights_eq_one w hw


theorem valueSym_comp_perm (f : Fin N → A) (π : Equiv.Perm (Fin N)) :
    valueSym (f ∘ π) = valueSym f := by
  apply Subtype.ext
  show Multiset.map (f ∘ π) univ.val = Multiset.map f univ.val
  rw [← Multiset.map_map]
  congr 1
  have h := congrArg Finset.val (Finset.map_univ_equiv π)
  simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
  exact h


theorem multisetWeight_perm [Fintype A] [DecidableEq A] (w : A → Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (lam : Sym A N) :
    multisetWeight (fun a i => w a (π i)) lam = multisetWeight w lam := by
  unfold multisetWeight
  rw [sum_filter, sum_filter]
  refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl A)) _ _ (fun f => ?_)
  have h1 : valueSym (Equiv.arrowCongr π (Equiv.refl A) f) = valueSym f :=
    valueSym_comp_perm f π.symm
  have h2 : ∏ i, w (f i) (π i) = ∏ i, w (Equiv.arrowCongr π (Equiv.refl A) f i) i := by
    rw [← Equiv.prod_comp π (fun i => w (Equiv.arrowCongr π (Equiv.refl A) f i) i)]
    apply Finset.prod_congr rfl
    intro i _
    show w (f i) (π i) = w (f (π.symm (π i))) (π i)
    rw [Equiv.symm_apply_apply]
  rw [h1, h2]


theorem sum_prod_slot_replace [Fintype A] (w w' : A → Fin N → ℝ) (i : Fin N)
    (hw : ∀ j, j ≠ i → ∑ a, w a j = 1) :
    ∑ f : Fin N → A, ∏ j, (if j = i then w' (f j) j else w (f j) j) = ∑ a, w' a i := by
  rw [← Fintype.prod_sum (fun j a => if j = i then w' a j else w a j)]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj, hw j hj]
  · intro h; exact absurd (mem_univ i) h

end Localization



section NormGradient

variable {m : Type*} [Fintype m]


theorem hasDerivAt_sqrt_sum_sq (g g' : m → ℝ → ℝ) (t : ℝ)
    (hg : ∀ j, HasDerivAt (g j) (g' j t) t) (hS : 0 < ∑ j, g j t ^ 2) :
    HasDerivAt (fun s => Real.sqrt (∑ j, g j s ^ 2))
      ((∑ j, g j t * g' j t) / Real.sqrt (∑ j, g j t ^ 2)) t := by
  have h1 : HasDerivAt (fun s => ∑ j, g j s ^ 2) (∑ j, 2 * g j t * g' j t) t := by
    have h := HasDerivAt.fun_sum (u := univ) (A := fun j s => g j s ^ 2)
      (A' := fun j => 2 * g j t * g' j t) (fun j _ => by
        have := (hg j).fun_pow 2
        simpa using this)
    exact h
  have h2 := h1.sqrt hS.ne'
  refine h2.congr_deriv ?_
  have hsq : 0 < Real.sqrt (∑ j, g j t ^ 2) := Real.sqrt_pos.mpr hS
  rw [Finset.sum_congr rfl (fun j _ => show 2 * g j t * g' j t = 2 * (g j t * g' j t) by ring),
    ← Finset.mul_sum]
  field_simp


theorem deriv_sqrt_sum_sq_le (g g' : m → ℝ → ℝ) (t : ℝ) (hS : 0 < ∑ j, g j t ^ 2) :
    ((∑ j, g j t * g' j t) / Real.sqrt (∑ j, g j t ^ 2)) ^ 2 ≤ ∑ j, g' j t ^ 2 := by
  rw [div_pow, Real.sq_sqrt hS.le, div_le_iff₀ hS]
  exact (Finset.sum_mul_sq_le_sq_mul_sq univ _ _).trans_eq (mul_comm _ _)


theorem sum_fiber_deriv_sq_le {F Λ : Type*} [Fintype F] [Fintype Λ] [DecidableEq Λ] (v : F → Λ)
    (g g' : F → ℝ → ℝ) (t : ℝ) (hpos : ∀ lam, 0 < ∑ f : {f // v f = lam}, g f t ^ 2) :
    ∑ lam, ((∑ f : {f // v f = lam}, g f t * g' f t)
        / Real.sqrt (∑ f : {f // v f = lam}, g f t ^ 2)) ^ 2 ≤ ∑ f, g' f t ^ 2 := by
  rw [← Fintype.sum_fiberwise v (fun f => g' f t ^ 2)]
  exact sum_le_sum fun lam _ =>
    deriv_sqrt_sum_sq_le (fun f : {f // v f = lam} => g f) (fun f : {f // v f = lam} => g' f) t
      (hpos lam)

end NormGradient



section Clusters


theorem dist_le_of_reachable {V X : Type*} [Fintype V] [PseudoMetricSpace X]
    (G : SimpleGraph V) (p : V → X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hadj : ∀ u v, G.Adj u v → dist (p u) (p v) ≤ δ) {u v : V} (h : G.Reachable u v) :
    dist (p u) (p v) ≤ ((Fintype.card V : ℝ) - 1) * δ := by
  have hwalk : ∀ {u v : V} (w : G.Walk u v), dist (p u) (p v) ≤ w.length * δ := by
    intro u v w
    induction w with
    | nil => simp
    | @cons u v' v h w ih =>
      calc dist (p u) (p v) ≤ dist (p u) (p v') + dist (p v') (p v) := dist_triangle _ _ _
        _ ≤ δ + w.length * δ := add_le_add (hadj _ _ h) ih
        _ = (SimpleGraph.Walk.cons h w).length * δ := by
          rw [SimpleGraph.Walk.length_cons]; push_cast; ring
  obtain ⟨w, hw⟩ := h.exists_isPath
  have hlen : (w.length : ℝ) + 1 ≤ Fintype.card V := by
    have := hw.length_lt
    exact_mod_cast this
  calc dist (p u) (p v) ≤ w.length * δ := hwalk w
    _ ≤ ((Fintype.card V : ℝ) - 1) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ
      linarith


theorem dist_le_of_reachable_card_le {V X : Type*} [Fintype V] [PseudoMetricSpace X]
    (G : SimpleGraph V) (p : V → X) {c₀ R : ℝ} (hc₀R : 0 ≤ c₀ * R) {N : ℕ}
    (hN : Fintype.card V ≤ N)
    (hadj : ∀ u v, G.Adj u v → dist (p u) (p v) ≤ 4 * c₀ * R) {u v : V} (h : G.Reachable u v) :
    dist (p u) (p v) ≤ ((N : ℝ) - 1) * (4 * c₀ * R) := by
  have h1 := dist_le_of_reachable G p (by linarith) hadj h
  have h2 : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast hN
  calc dist (p u) (p v) ≤ ((Fintype.card V : ℝ) - 1) * (4 * c₀ * R) := h1
    _ ≤ ((N : ℝ) - 1) * (4 * c₀ * R) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith


theorem ball_disjoint_of_far {X : Type*} [PseudoMetricSpace X] {c₀ R : ℝ} (hc₀R : 0 ≤ c₀ * R)
    {x y : X} (hd : 4 * c₀ * R < dist x y) :
    Disjoint (Metric.ball x (3 * c₀ * R / 2)) (Metric.ball y (3 * c₀ * R / 2)) :=
  Metric.ball_disjoint_ball (by linarith)


theorem mem_ball_anchor {X : Type*} [PseudoMetricSpace X] {c₀ R : ℝ} {N : ℕ}
    {x ca cls : X} (hx : x ∈ Metric.ball ca (3 * c₀ * R / 2))
    (hca : dist ca cls ≤ ((N : ℝ) - 1) * (4 * c₀ * R)) :
    x ∈ Metric.ball cls ((4 * ((N : ℝ) - 1) + 3 / 2) * (c₀ * R)) := by
  rw [Metric.mem_ball] at hx ⊢
  calc dist x cls ≤ dist x ca + dist ca cls := dist_triangle _ _ _
    _ < 3 * c₀ * R / 2 + ((N : ℝ) - 1) * (4 * c₀ * R) := by linarith
    _ = (4 * ((N : ℝ) - 1) + 3 / 2) * (c₀ * R) := by ring

variable {E : Type*} {S : Type*} [Fintype S]


def clusterCutoff (θ : S → E → ℝ) (x : E) : ℝ := 1 - ∏ a, (1 - θ a x)


theorem clusterCutoff_mem_Icc (θ : S → E → ℝ) (x : E) (h : ∀ a, 0 ≤ θ a x ∧ θ a x ≤ 1) :
    0 ≤ clusterCutoff θ x ∧ clusterCutoff θ x ≤ 1 := by
  unfold clusterCutoff
  have h0 : 0 ≤ ∏ a, (1 - θ a x) := prod_nonneg fun a _ => by linarith [(h a).2]
  have h1 : ∏ a, (1 - θ a x) ≤ 1 := prod_le_one (fun a _ => by linarith [(h a).2])
    (fun a _ => by linarith [(h a).1])
  constructor <;> linarith


theorem clusterCutoff_eq_one (θ : S → E → ℝ) (x : E) {a : S} (h : θ a x = 1) :
    clusterCutoff θ x = 1 := by
  unfold clusterCutoff
  rw [prod_eq_zero (mem_univ a) (by rw [h]; ring), sub_zero]


theorem clusterCutoff_eq_zero (θ : S → E → ℝ) (x : E) (h : ∀ a, θ a x = 0) :
    clusterCutoff θ x = 0 := by
  simp [clusterCutoff, h]


theorem hasFDerivAt_clusterCutoff [DecidableEq S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : S → E → ℝ) (θ' : S → E →L[ℝ] ℝ) (x : E) (hθ : ∀ a, HasFDerivAt (θ a) (θ' a) x) :
    HasFDerivAt (clusterCutoff θ) (∑ a, (∏ b ∈ univ.erase a, (1 - θ b x)) • θ' a) x := by
  have h := (HasFDerivAt.finsetProd (u := univ) (g := fun a y => 1 - θ a y)
    (g' := fun a => -θ' a) (fun a _ => (hθ a).const_sub 1)).const_sub 1
  refine HasFDerivAt.congr_fderiv h ?_
  simp [Finset.sum_neg_distrib]


theorem norm_fderiv_clusterCutoff_le [DecidableEq S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : S → E → ℝ) (θ' : S → E →L[ℝ] ℝ) (x : E) (h : ∀ a, 0 ≤ θ a x ∧ θ a x ≤ 1) :
    ‖∑ a, (∏ b ∈ univ.erase a, (1 - θ b x)) • θ' a‖ ≤ ∑ a, ‖θ' a‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have h0 : 0 ≤ ∏ b ∈ univ.erase a, (1 - θ b x) := prod_nonneg fun b _ => by linarith [(h b).2]
  have h1 : ∏ b ∈ univ.erase a, (1 - θ b x) ≤ 1 :=
    prod_le_one (fun b _ => by linarith [(h b).2]) (fun b _ => by linarith [(h b).1])
  rw [abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

end Clusters



section Phase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]


def phase (e : ℝ) (θ : ι → E → ℝ) (c : ι → E) (a : E → E) (x : E) : ℝ :=
  -e * ∑ s, θ s x * ⟪a (c s), x - c s⟫_ℝ


def residualVelocity (e : ℝ) (θ : ι → E → ℝ) (c : ι → E) (a : E → E) (x : E) : E :=
  -e • ∑ s, θ s x • (a x - a (c s))


theorem hasFDerivAt_phase (e : ℝ) (θ : ι → E → ℝ) (c : ι → E) (a : E → E) (x : E) (s₀ : ι)
    (hθ : ∀ s, HasFDerivAt (θ s) (0 : E →L[ℝ] ℝ) x) (h1 : θ s₀ x = 1)
    (h0 : ∀ s, s ≠ s₀ → θ s x = 0) :
    HasFDerivAt (phase e θ c a) ((-e) • innerSL ℝ (a (c s₀))) x := by
  have hinner : ∀ s, HasFDerivAt (fun y => ⟪a (c s), y - c s⟫_ℝ) (innerSL ℝ (a (c s))) x := by
    intro s
    have h := (innerSL ℝ (a (c s))).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (c s))
    simpa [Function.comp_def] using h
  have hsum := (HasFDerivAt.fun_sum (u := univ)
    (A := fun s y => θ s y * ⟪a (c s), y - c s⟫_ℝ)
    (A' := fun s => θ s x • innerSL ℝ (a (c s)) + ⟪a (c s), x - c s⟫_ℝ • (0 : E →L[ℝ] ℝ))
    (fun s _ => (hθ s).fun_mul (hinner s))).const_mul (-e)
  refine HasFDerivAt.congr_fderiv hsum ?_
  rw [Finset.sum_eq_single s₀]
  · simp [h1]
  · intro s _ hs; simp [h0 s hs]
  · intro h; exact absurd (mem_univ s₀) h


theorem gradient_phase_add_residualVelocity (e : ℝ) (θ : ι → E → ℝ) (c : ι → E) (a : E → E)
    (x : E) (s₀ : ι) (h1 : θ s₀ x = 1) (h0 : ∀ s, s ≠ s₀ → θ s x = 0) :
    (-e) • a (c s₀) + residualVelocity e θ c a x = (-e) • a x := by
  unfold residualVelocity
  rw [Finset.sum_eq_single s₀]
  · rw [h1, one_smul, smul_sub]; abel
  · intro s _ hs; simp [h0 s hs]
  · intro h; exact absurd (mem_univ s₀) h


theorem norm_residualVelocity_le (e : ℝ) (θ : ι → E → ℝ) (c : ι → E) (a : E → E)
    (a' : E → E →L[ℝ] E) {ρ₀ Z : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ₀) (hZ : 0 ≤ Z)
    (hθ : ∀ s x, 0 ≤ θ s x ∧ θ s x ≤ 1)
    (hdisj : ∀ x s s', s ≠ s' → θ s x ≠ 0 → θ s' x = 0)
    (hsupp : ∀ s x, θ s x ≠ 0 → x ∈ Metric.ball (c s) ρ₀)
    (ha : ∀ s, ∀ y ∈ Metric.ball (c s) ρ₀, HasFDerivWithinAt a (a' y) (Metric.ball (c s) ρ₀) y)
    (ha' : ∀ s, ∀ y ∈ Metric.ball (c s) ρ₀, ‖a' y‖ ≤ Z) (x : E) :
    ‖residualVelocity e θ c a x‖ ≤ e * ρ₀ * Z := by
  unfold residualVelocity
  by_cases hex : ∃ s, θ s x ≠ 0
  · obtain ⟨s, hs⟩ := hex
    rw [Finset.sum_eq_single s (fun s' _ hs' => by rw [hdisj x s s' (Ne.symm hs') hs, zero_smul])
      (fun h => absurd (mem_univ s) h)]
    have hx : x ∈ Metric.ball (c s) ρ₀ := hsupp s x hs
    have hρpos : 0 < ρ₀ := by
      have := Metric.mem_ball.mp hx; linarith [dist_nonneg (x := x) (y := c s)]
    have hmv : ‖a x - a (c s)‖ ≤ Z * ‖x - c s‖ :=
      (convex_ball (c s) ρ₀).norm_image_sub_le_of_norm_hasFDerivWithin_le (ha s) (ha' s)
        (Metric.mem_ball_self hρpos) hx
    have hdist : ‖x - c s‖ ≤ ρ₀ := by
      have := Metric.mem_ball.mp hx; rw [dist_eq_norm] at this; exact this.le
    rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg he,
      abs_of_nonneg (hθ s x).1]
    calc e * (θ s x * ‖a x - a (c s)‖) ≤ e * (1 * (Z * ρ₀)) := by
          gcongr
          · exact (hθ s x).2
          · exact hmv.trans (mul_le_mul_of_nonneg_left hdist hZ)
      _ = e * ρ₀ * Z := by ring
  · have hall : ∀ s, θ s x = 0 := fun s => by
      by_contra h; exact hex ⟨s, h⟩
    simp only [hall, zero_smul, sum_const_zero, smul_zero, norm_zero]
    positivity


theorem norm_fderiv_residualVelocity_le (e : ℝ) (θ : ι → E → ℝ) (θ' : ι → E → E →L[ℝ] ℝ)
    (c : ι → E) (a : E → E) (a' : E → E →L[ℝ] E) {ρ₀ Z g : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ₀)
    (hZ : 0 ≤ Z) (hg : 0 ≤ g) (hθ : ∀ s x, 0 ≤ θ s x ∧ θ s x ≤ 1)
    (hθ' : ∀ s x, HasFDerivAt (θ s) (θ' s x) x) (hθ'g : ∀ s x, ‖θ' s x‖ ≤ g)
    (hdisj : ∀ x s s', s ≠ s' → (θ s x ≠ 0 ∨ θ' s x ≠ 0) → θ s' x = 0 ∧ θ' s' x = 0)
    (hsupp : ∀ s x, (θ s x ≠ 0 ∨ θ' s x ≠ 0) → x ∈ Metric.ball (c s) ρ₀)
    (ha : ∀ y, HasFDerivAt a (a' y) y)
    (ha' : ∀ s, ∀ y ∈ Metric.ball (c s) ρ₀, ‖a' y‖ ≤ Z) (x : E) :
    HasFDerivAt (residualVelocity e θ c a)
        ((-e) • ∑ s, (θ s x • a' x + (θ' s x).smulRight (a x - a (c s)))) x ∧
      ‖(-e) • ∑ s, (θ s x • a' x + (θ' s x).smulRight (a x - a (c s)))‖
        ≤ e * (g * ρ₀ + 1) * Z := by
  constructor
  · exact (HasFDerivAt.fun_sum (u := univ) (A := fun s y => θ s y • (a y - a (c s)))
      (A' := fun s => θ s x • a' x + (θ' s x).smulRight (a x - a (c s)))
      (fun s _ => (hθ' s x).fun_smul ((ha x).sub_const (a (c s))))).const_smul (-e)
  · by_cases hex : ∃ s, θ s x ≠ 0 ∨ θ' s x ≠ 0
    · obtain ⟨s, hs⟩ := hex
      rw [Finset.sum_eq_single s (fun s' _ hs' => by
          obtain ⟨h1, h2⟩ := hdisj x s s' (Ne.symm hs') hs
          simp [h1, h2]) (fun h => absurd (mem_univ s) h)]
      have hx : x ∈ Metric.ball (c s) ρ₀ := hsupp s x hs
      have hρpos : 0 < ρ₀ := by
        have := Metric.mem_ball.mp hx; linarith [dist_nonneg (x := x) (y := c s)]
      have hmv : ‖a x - a (c s)‖ ≤ Z * ‖x - c s‖ :=
        (convex_ball (c s) ρ₀).norm_image_sub_le_of_norm_hasFDerivWithin_le
          (fun y _ => (ha y).hasFDerivWithinAt) (ha' s) (Metric.mem_ball_self hρpos) hx
      have hdist : ‖x - c s‖ ≤ ρ₀ := by
        have := Metric.mem_ball.mp hx; rw [dist_eq_norm] at this; exact this.le
      have h1 : θ s x * ‖a' x‖ ≤ 1 * Z :=
        mul_le_mul (hθ s x).2 (ha' s x hx) (norm_nonneg _) zero_le_one
      have h2 : ‖θ' s x‖ * ‖a x - a (c s)‖ ≤ g * (Z * ρ₀) :=
        mul_le_mul (hθ'g s x) (hmv.trans (mul_le_mul_of_nonneg_left hdist hZ)) (norm_nonneg _) hg
      have h3 : ‖θ s x • a' x + (θ' s x).smulRight (a x - a (c s))‖
          ≤ θ s x * ‖a' x‖ + ‖θ' s x‖ * ‖a x - a (c s)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ s x).1,
          ContinuousLinearMap.norm_smulRight_apply]
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg he]
      calc e * ‖θ s x • a' x + (θ' s x).smulRight (a x - a (c s))‖
          ≤ e * (1 * Z + g * (Z * ρ₀)) :=
            mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) he
        _ = e * (g * ρ₀ + 1) * Z := by ring
    · have hall : ∀ s, θ s x = 0 ∧ θ' s x = 0 := fun s =>
        ⟨by by_contra h; exact hex ⟨s, Or.inl h⟩, by by_contra h; exact hex ⟨s, Or.inr h⟩⟩
      simp only [hall, zero_smul, ContinuousLinearMap.zero_smulRight, add_zero, sum_const_zero,
        smul_zero, norm_zero]
      positivity

end Phase

end GptLean.RemovalGeometry
