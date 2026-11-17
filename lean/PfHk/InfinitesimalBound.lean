import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Elementary closure rules for infinitesimal relative norm bounds. -/

noncomputable section
namespace PfHk.InfinitesimalBound

variable {X : Type*}

def Bound (F U T : X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ x, T x ≤ ε * F x + K * U x

theorem mono {F U T S : X → ℝ} (h : Bound F U S) (hle : ∀ x, T x ≤ S x) :
    Bound F U T := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := h ε hε
  exact ⟨K, hK, fun x => (hle x).trans (hb x)⟩

theorem bounded {F U T : X → ℝ} (hF : ∀ x, 0 ≤ F x)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ x, T x ≤ C * U x) : Bound F U T := by
  intro ε hε
  exact ⟨C, hC, fun x => (h x).trans (le_add_of_nonneg_left (mul_nonneg hε.le (hF x)))⟩

theorem add {F U T S : X → ℝ} (hT : Bound F U T) (hS : Bound F U S) :
    Bound F U (fun x => T x + S x) := by
  intro ε hε
  obtain ⟨K, hK, hk⟩ := hT (ε / 2) (by positivity)
  obtain ⟨L, hL, hl⟩ := hS (ε / 2) (by positivity)
  refine ⟨K + L, add_nonneg hK hL, fun x => ?_⟩
  exact (add_le_add (hk x) (hl x)).trans_eq (by ring)

theorem sum {J : Type*} (s : Finset J) {F U : X → ℝ} (T : J → X → ℝ)
    (hF : ∀ x, 0 ≤ F x) (h : ∀ j ∈ s, Bound F U (T j)) :
    Bound F U (fun x => ∑ j ∈ s, T j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using bounded (T := fun _ => 0) hF 0 le_rfl (fun _ => by simp)
  | @insert j s hj ih =>
    have h₁ := h j (Finset.mem_insert_self _ _)
    have h₂ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hj] using add h₁ h₂

theorem of_squared {F U T : X → ℝ} (hF : ∀ x, 0 ≤ F x) (hU : ∀ x, 0 ≤ U x)
    (hT : ∀ x, 0 ≤ T x)
    (h : ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, T x ^ 2 ≤ δ * F x ^ 2 + K * U x ^ 2) : Bound F U T := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg K, fun x => ?_⟩
  have hFx := hF x
  have hUx := hU x
  have hs := Real.sq_sqrt hK
  have hs' : (Real.sqrt K * U x) ^ 2 = K * U x ^ 2 := by rw [mul_pow, hs]
  have hc : 0 ≤ ε * F x * (Real.sqrt K * U x) := by positivity
  have hp : 0 ≤ ε * F x + Real.sqrt K * U x := by positivity
  nlinarith only [hb x, hs', hc, hp, hT x]

theorem squared_scale {F U T P : X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, T x ^ 2 ≤ B * P x)
    (h : ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, P x ≤ δ * F x ^ 2 + K * U x ^ 2) :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, T x ^ 2 ≤ δ * F x ^ 2 + K * U x ^ 2 := by
  intro δ hδ
  have hp : 0 < B + 1 := by linarith
  obtain ⟨K, hK, hk⟩ := h (δ / (B + 1)) (div_pos hδ hp)
  refine ⟨B * K, mul_nonneg hB hK, fun x => ?_⟩
  have hc : B * (δ / (B + 1)) ≤ δ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  calc
    _ ≤ B * (δ / (B + 1) * F x ^ 2 + K * U x ^ 2) :=
      (hb x).trans (mul_le_mul_of_nonneg_left (hk x) hB)
    _ = (B * (δ / (B + 1))) * F x ^ 2 + (B * K) * U x ^ 2 := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) le_rfl

theorem comparison {F L U T : X → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hF : ∀ x, 0 ≤ F x) (hU : ∀ x, 0 ≤ U x)
    (hL : ∀ x, L x ≤ D * (F x + U x)) (h : Bound L U T) : Bound F U T := by
  intro ε hε
  have hp : 0 < D + 1 := by linarith
  have he : 0 < ε / (D + 1) := div_pos hε hp
  obtain ⟨K, hK, hk⟩ := h (ε / (D + 1)) he
  have hc : ε / (D + 1) * D ≤ ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨ε / (D + 1) * D + K, add_nonneg (mul_nonneg he.le hD) hK, fun x => ?_⟩
  calc
    _ ≤ ε / (D + 1) * (D * (F x + U x)) + K * U x :=
      (hk x).trans (add_le_add (mul_le_mul_of_nonneg_left (hL x) he.le) le_rfl)
    _ = (ε / (D + 1) * D) * F x + (ε / (D + 1) * D + K) * U x := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (hF x)) le_rfl

end PfHk.InfinitesimalBound
