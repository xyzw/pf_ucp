import PfHk.PauliQuantumFormPairing
import PfHk.InfinitesimalBound

/-! Hilbert-space and scalar algebra for finite magnetic perturbations. -/
noncomputable section
namespace PfHk.PauliMagneticRelative
open MeasureTheory PfHk.PauliSpin PfHk.InfinitesimalBound
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

section Finite
variable {S X Y H : Type*} [Fintype S] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ν : Measure Y}

theorem norm_bundle_le_sum (v : S → Lp H 2 ν) :
    ‖FiniteFiberL2.bundle v‖ ≤ ∑ s, ‖v s‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [FiniteFiberL2.norm_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem norm_coordinate_le_bundle (v : S → Lp H 2 ν) (s : S) :
    ‖v s‖ ≤ ‖FiniteFiberL2.bundle v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [FiniteFiberL2.norm_sq]
  exact Finset.single_le_sum (fun t _ => sq_nonneg ‖v t‖) (Finset.mem_univ s)

theorem bundle_relative {F U : X → ℝ} (T : X → S → Lp H 2 ν)
    (hF : ∀ x, 0 ≤ F x) (h : ∀ s, Bound F U (fun x => ‖T x s‖)) :
    Bound F U (fun x => ‖FiniteFiberL2.bundle (T x)‖) :=
  InfinitesimalBound.mono (InfinitesimalBound.sum Finset.univ
    (fun s x => ‖T x s‖) hF (fun s _ => h s)) (fun x => norm_bundle_le_sum (T x))

theorem enlarge_relative {F U F' U' T : X → ℝ}
    (hF : ∀ x, F x ≤ F' x) (hU : ∀ x, U x ≤ U' x) (h : Bound F U T) :
    Bound F' U' T := by
  intro ε hε
  obtain ⟨K, hK, hk⟩ := h ε hε
  exact ⟨K, hK, fun x => (hk x).trans (add_le_add
    (mul_le_mul_of_nonneg_left (hF x) hε.le)
    (mul_le_mul_of_nonneg_left (hU x) hK))⟩

theorem scale_relative {F U T : X → ℝ} (c : ℝ) (hc : 0 ≤ c) (h : Bound F U T)
    (hF : ∀ x, 0 ≤ F x) : Bound F U (fun x => c * T x) := by
  intro ε hε
  obtain ⟨K, hK, hk⟩ := h (ε / (c + 1)) (by positivity)
  have hcoef : c * (ε / (c + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < c + 1)).mpr
    nlinarith
  refine ⟨c * K, mul_nonneg hc hK, fun x => ?_⟩
  calc
    _ ≤ c * (ε / (c + 1) * F x + K * U x) := mul_le_mul_of_nonneg_left (hk x) hc
    _ = (c * (ε / (c + 1))) * F x + (c * K) * U x := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoef (hF x)) le_rfl


theorem scalar_pairing_eq_inner (b : Y → ℝ) (z u v : Lp H 2 ν)
    (hv : v =ᵐ[ν] fun x => (b x : ℂ) • u x) :
    (∫ x, (b x : ℂ) * inner ℂ (z x) (u x) ∂ν) = inner ℂ z v := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx, inner_smul_right]



theorem integral_sum_norm_sq (v : S → Lp H 2 ν) :
    (∫ x, ∑ s, ‖v s x‖ ^ 2 ∂ν) = ∑ s, ‖v s‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [integral_finsetSum _ (fun s _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v s))).mp (Lp.memLp (v s)))]
  exact Finset.sum_congr rfl fun s _ =>
    (GptLean.PhotonKernelLocalization.l2_norm_sq_eq_integral (v s)).symm

omit [InnerProductSpace ℂ H] in
theorem sum_norm_sq_integrable (v : S → Lp H 2 ν) :
    Integrable (fun x => (1 : ℝ) * ∑ s, ‖v s x‖ ^ 2) ν := by
  simpa only [one_mul] using integrable_finsetSum Finset.univ (fun s _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v s))).mp (Lp.memLp (v s)))

theorem unweighted_norm_bound (v r m : S → Lp H 2 ν) (K : ℝ)
    (h : (∫ x, (1 : ℝ) * ∑ s, ‖v s x‖ ^ 2 ∂ν) ≤ K *
      ((1 : ℝ) * (∫ x, (1 : ℝ) * ∑ s, ‖r s x‖ ^ 2 ∂ν) +
       (1 : ℝ) * (∫ x, (1 : ℝ) * ∑ s, ‖m s x‖ ^ 2 ∂ν))) :
    ‖FiniteFiberL2.bundle v‖ ^ 2 ≤ K * ((∑ s, ‖r s‖ ^ 2) + ∑ s, ‖m s‖ ^ 2) := by
  simp only [one_mul] at h
  rw [integral_sum_norm_sq, integral_sum_norm_sq, integral_sum_norm_sq] at h
  rw [FiniteFiberL2.norm_sq]
  exact h



omit [InnerProductSpace ℂ H] in
theorem norm_bundle_add_add_le (a b c : S → Lp H 2 ν) :
    ‖FiniteFiberL2.bundle (fun s => a s + b s + c s)‖ ≤
      (‖FiniteFiberL2.bundle a‖ + ‖FiniteFiberL2.bundle b‖) + ‖FiniteFiberL2.bundle c‖ := by
  change ‖FiniteFiberL2.bundle ((a + b) + c)‖ ≤ _
  rw [FiniteFiberL2.bundle_add, FiniteFiberL2.bundle_add]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem finite_comparison_norm (u f L : S → Lp H 2 ν) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ s, ‖L s‖ ≤ D * (‖f s‖ + ‖u s‖)) :
    ‖FiniteFiberL2.bundle L‖ ≤ (D * Fintype.card S) *
      (‖FiniteFiberL2.bundle f‖ + ‖FiniteFiberL2.bundle u‖) := by
  calc
    _ ≤ ∑ s, ‖L s‖ := norm_bundle_le_sum L
    _ ≤ ∑ s, D * (‖FiniteFiberL2.bundle f‖ + ‖FiniteFiberL2.bundle u‖) :=
      Finset.sum_le_sum fun s _ => (h s).trans
        (mul_le_mul_of_nonneg_left (add_le_add (norm_coordinate_le_bundle f s)
          (norm_coordinate_le_bundle u s)) hD)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Finite

section FurtherFinite
variable {S J X Y H : Type*} [Fintype S] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ν : Measure Y}

omit [InnerProductSpace ℂ H] in
theorem bundle_sum (t : Finset J) (v : J → S → Lp H 2 ν) :
    FiniteFiberL2.bundle (∑ j ∈ t, v j) = ∑ j ∈ t, FiniteFiberL2.bundle (v j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, FiniteFiberL2.bundle_zero]
  | @insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, FiniteFiberL2.bundle_add, ih]

theorem product_relative {F U T : X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ x, 0 ≤ F x) (hU : ∀ x, 0 ≤ U x) (hT : ∀ x, 0 ≤ T x)
    (h : ∀ x, T x ^ 2 ≤ B * (U x * F x)) : Bound F U T := by
  intro ε hε
  let c : ℝ := B / (4 * ε)
  have hc : 0 ≤ c := div_nonneg hB (by positivity)
  have he : 4 * ε * c = B := by dsimp [c]; field_simp
  refine ⟨c, hc, fun x => ?_⟩
  have he' : 4 * ε * c * (U x * F x) = B * (U x * F x) :=
    congrArg (fun z : ℝ => z * (U x * F x)) he
  have hs := sq_nonneg (ε * F x - c * U x)
  have hp : 0 ≤ ε * F x + c * U x :=
    add_nonneg (mul_nonneg hε.le (hF x)) (mul_nonneg hc (hU x))
  apply (sq_le_sq₀ (hT x) hp).mp
  nlinarith only [h x, he', hs]

end FurtherFinite

variable {N : ℕ}

section GenericSpin
variable {Y H : Type*} [MeasurableSpace Y] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {ν : Measure Y}

theorem sigma_bundle_norm (n : Fin N) (μ : Fin 3)
    (u : SpinIndex N → Lp H 2 ν) :
    ‖FiniteFiberL2.bundle (sigmaFamily n μ u)‖ = ‖FiniteFiberL2.bundle u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [FiniteFiberL2.norm_sq, FiniteFiberL2.norm_sq]
  exact PauliMagneticSpin.sigma_sum_norm_sq n μ u

theorem scaled_sigma_bundle_norm_le (t : Fin N → Fin 3 → SpinIndex N → Lp H 2 ν) :
    ‖FiniteFiberL2.bundle (fun s => ((1 / 2 : ℝ) : ℂ) •
      ∑ n, ∑ μ : Fin 3, sigmaFamily n μ (t n μ) s)‖ ≤
      (1 / 2 : ℝ) * ∑ n, ∑ μ : Fin 3, ‖FiniteFiberL2.bundle (t n μ)‖ := by
  have he : (fun s => ((1 / 2 : ℝ) : ℂ) • ∑ n, ∑ μ : Fin 3, sigmaFamily n μ (t n μ) s) =
      ((1 / 2 : ℝ) : ℂ) • ∑ n, ∑ μ : Fin 3, sigmaFamily n μ (t n μ) := by
    funext s
    simp only [Pi.smul_apply, Finset.sum_apply]
  rw [he, FiniteFiberL2.bundle_smul, norm_smul]
  norm_num only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [bundle_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [bundle_sum]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun μ _ => sigma_bundle_norm n μ _)

theorem radiation_mass_bound {J : Type*} [Fintype J]
    (r m L : SpinIndex N → Lp H 2 ν) (d : SpinIndex N → J → Lp H 2 ν)
    (h : ∀ s, (∑ i, ‖d s i‖ ^ 2) + ‖r s‖ ^ 2 + ‖m s‖ ^ 2 ≤ ‖m s‖ * ‖L s‖) :
    (∑ s, ‖r s‖ ^ 2) + (∑ s, ‖m s‖ ^ 2) ≤
      ‖FiniteFiberL2.bundle m‖ * ‖FiniteFiberL2.bundle L‖ := by
  have hs : (∑ s, ‖r s‖ ^ 2) + (∑ s, ‖m s‖ ^ 2) ≤ ∑ s, ‖m s‖ * ‖L s‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun s _ => by
      have hg : 0 ≤ ∑ i, ‖d s i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith only [h s, hg]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => ‖m s‖) (fun s => ‖L s‖)
  rw [← FiniteFiberL2.norm_sq, ← FiniteFiberL2.norm_sq, ← mul_pow] at hcs
  exact hs.trans ((sq_le_sq₀ (Finset.sum_nonneg fun _ _ => by positivity)
    (by positivity : 0 ≤ ‖FiniteFiberL2.bundle m‖ * ‖FiniteFiberL2.bundle L‖)).mp hcs)

end GenericSpin


section Trace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem half_trace_pairing (z : SpinIndex N → H)
    (t : Fin N → Fin 3 → SpinIndex N → H)
    (q : Fin N → Fin 3 → SpinIndex N → SpinIndex N → ℂ)
    (hq : ∀ n k s r, q n k s r = inner ℂ (z s) (t n k r)) :
    (1 / 2 : ℂ) * ∑ n, ∑ k, PauliSquareAlgebra.matrixSpinTrace n k (q n k) =
      ∑ s, inner ℂ (z s) (((1 / 2 : ℝ) : ℂ) •
        ∑ n, ∑ k, sigmaFamily n k (t n k) s) := by
  have he : q = fun n k s r => inner ℂ (z s) (t n k r) :=
    funext fun n => funext fun k => funext fun s => funext fun r => hq n k s r
  rw [he]
  have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [← hc]
  exact (PauliQuantumFormPairing.scaled_contraction_pairing
    (H := H) (((1 / 2 : ℝ) : ℂ)) z t).symm
end Trace


end PfHk.PauliMagneticRelative
