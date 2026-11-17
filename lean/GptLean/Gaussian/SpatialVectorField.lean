import GptLean.Gaussian.SpatialFieldSize
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The actual three-component measured field, its spatial derivative
vectors, and a local bound for the Fréchet derivative operator. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

/-- Assemble the scalar WIS coordinates into the physical Euclidean vector. -/
def vectorField {Q : Type*} (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (ds : List (Fin 3)) (q : Q) (x : FieldSpace) : FieldSpace :=
  WithLp.toLp 2 (fun i => field i ds x q)

theorem vectorField_jointly_measurable {Q : Type*} [MeasurableSpace Q]
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds))) (ds : List (Fin 3)) :
    Measurable (Function.uncurry (vectorField field ds)) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (measurable_pi_lambda _ (fun i => (hm i ds).comp measurable_swap))

theorem vectorField_contDiff {Q : Type*}
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (q : Q) (ds : List (Fin 3))
    (hs : ∀ i, ContDiff ℝ ∞ (fun x => field i ds x q)) :
    ContDiff ℝ ∞ (vectorField field ds q) := by
  apply contDiff_piLp'
  exact hs

theorem vectorField_fderiv_coordinate {Q : Type*}
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ) (q : Q)
    (hs : ∀ i ds, ContDiff ℝ ∞ (fun x => field i ds x q))
    (hd : ∀ i ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
      (field i (j :: ds) x q) x (EuclideanSpace.single j 1))
    (ds : List (Fin 3)) (x : FieldSpace) (i j : Fin 3) :
    fderiv ℝ (vectorField field ds q) x (EuclideanSpace.single j 1) i =
      field i (j :: ds) x q := by
  have ha := ((vectorField_contDiff field q ds (fun i => hs i ds)).differentiable (by simp) x).hasFDerivAt
  have hp := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (vectorField field ds q x) i).comp x ha
  have he := congrArg (fun A : FieldSpace →L[ℝ] ℝ => A (EuclideanSpace.single j 1)) hp.fderiv
  change fderiv ℝ (fun x => field i ds x q) x (EuclideanSpace.single j 1) =
    fderiv ℝ (vectorField field ds q) x (EuclideanSpace.single j 1) i at he
  exact he.symm.trans (fderiv_coordinate_of_smooth_field
    (fun ds x => field i ds x q) (hs i) (hd i) ds j x)

theorem vectorField_fderiv_apply {Q : Type*}
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ) (q : Q)
    (hs : ∀ i ds, ContDiff ℝ ∞ (fun x => field i ds x q))
    (hd : ∀ i ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
      (field i (j :: ds) x q) x (EuclideanSpace.single j 1))
    (ds : List (Fin 3)) (x : FieldSpace) (j : Fin 3) :
    fderiv ℝ (vectorField field ds q) x (EuclideanSpace.single j 1) =
      vectorField field (j :: ds) q x := by
  ext i
  exact vectorField_fderiv_coordinate field q hs hd ds x i j

theorem vectorField_derivative_jointly_measurable {Q : Type*} [MeasurableSpace Q]
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (hs : ∀ q i ds, ContDiff ℝ ∞ (fun x => field i ds x q))
    (hd : ∀ q i ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
      (field i (j :: ds) x q) x (EuclideanSpace.single j 1))
    (ds : List (Fin 3)) (j : Fin 3) :
    Measurable (fun p : Q × FieldSpace =>
      fderiv ℝ (vectorField field ds p.1) p.2 (EuclideanSpace.single j 1)) := by
  simp_rw [vectorField_fderiv_apply field _ (hs _) (hd _)]
  exact vectorField_jointly_measurable field hm (j :: ds)

/-- The three-dimensional operator norm is at most three times a uniform
absolute bound for its matrix entries. -/
theorem euclidean_opNorm_le_three
    (A : FieldSpace →L[ℝ] FieldSpace) {Z : ℝ} (hZ : 0 ≤ Z)
    (hb : ∀ i j, |A (EuclideanSpace.single j 1) i| ≤ Z) : ‖A‖ ≤ 3 * Z := by
  apply A.opNorm_le_bound (by positivity)
  intro v
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j (1 : ℝ)) = v := by
    ext i
    simp [PiLp.single_apply, Pi.single_apply]
  have hentry (i : Fin 3) : A v i =
      ∑ j : Fin 3, v j * A (EuclideanSpace.single j 1) i := by
    nth_rw 1 [← hv]
    simp only [Fin.sum_univ_three, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hsq (i : Fin 3) : (A v i) ^ 2 ≤ ‖v‖ ^ 2 * (3 * Z ^ 2) := by
    rw [hentry]
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : Fin 3 => v j) (fun j => A (EuclideanSpace.single j 1) i)
    have hb' : (∑ j : Fin 3, (A (EuclideanSpace.single j 1) i) ^ 2) ≤ 3 * Z ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin 3, Z ^ 2 := Finset.sum_le_sum (fun j _ => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i j) 2)
        _ = _ := by simp
    have hn : (∑ j : Fin 3, (v j) ^ 2) = ‖v‖ ^ 2 := by
      simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    exact hc.trans (by rw [hn]; exact mul_le_mul_of_nonneg_left hb' (sq_nonneg _))
  have hnorm : ‖A v‖ ^ 2 ≤ (3 * Z * ‖v‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 * (3 * Z ^ 2) := Finset.sum_le_sum (fun i _ => hsq i)
      _ = _ := by simp; ring
  have hright : 0 ≤ 3 * Z * ‖v‖ := by positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).mp hnorm

/-- A single size for all components and all supplied cluster balls. -/
def clusterFieldSize {S Q : Type*} [Fintype S]
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : S → FieldSpace) (r : ℝ) (q : Q) : ℝ :=
  3 * localFieldSize (fun i : S × Fin 3 => field i.2) (fun i => centre i.1) r q

theorem clusterFieldSize_nonneg {S Q : Type*} [Fintype S]
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : S → FieldSpace) (r : ℝ) (q : Q) : 0 ≤ clusterFieldSize field centre r q :=
  mul_nonneg (by norm_num) (localFieldSize_nonneg _ _ _ _)

theorem clusterFieldSize_measurable {S Q : Type*} [Fintype S] [MeasurableSpace Q]
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (centre : S → FieldSpace) (r : ℝ) : Measurable (clusterFieldSize field centre r) :=
  (measurable_localFieldSize (fun i : S × Fin 3 => field i.2)
    (fun i ds => hm i.2 ds) (fun i => centre i.1) r).const_mul 3

theorem vectorField_fderiv_le_clusterFieldSize {S Q : Type*} [Fintype S]
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (q : Q) (hs : ∀ i ds, ContDiff ℝ ∞ (fun x => field i ds x q))
    (hd : ∀ i ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
      (field i (j :: ds) x q) x (EuclideanSpace.single j 1))
    (centre : S → FieldSpace) {r : ℝ} (hr : 0 < r) (s : S)
    (x : FieldSpace) (hx : x ∈ Metric.closedBall (centre s) r) :
    ‖fderiv ℝ (vectorField field [] q) x‖ ≤ clusterFieldSize field centre r q := by
  apply euclidean_opNorm_le_three _ (localFieldSize_nonneg _ _ _ _)
  intro i j
  rw [vectorField_fderiv_coordinate field q hs hd]
  exact localFieldSize_controls_component_on_ball
    (fun a : S × Fin 3 => field a.2) (fun a => centre a.1) hr q (s, i) j
      (hs i [j]).continuous x hx

namespace KernelFieldData

variable {S Q H K G Ω : Type*} [Fintype S]
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

/-- The actual vector-field size on at most N cluster balls of radius
(6 + 12N)R has a moment constant independent of the localization cell.
The factor nine accounts for the conversion to the derivative operator norm. -/
theorem clusterFieldSize_moment_from_kernels
    (momentum : Ω → FieldSpace) {k R C : ℝ} (a b : ℝ) (N : ℕ)
    (hcard : Fintype.card S ≤ N)
    (hk : 0 ≤ k) (hR : 0 < R) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (sobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (centre : S → FieldSpace) (base : Fin 3 → Ω → ℂ)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (hkernel : ∀ i ds x,
      D.kernel (label i ds x) = softDerivativeKernel momentum ds k x (base i))
    (hbaseA : ∀ i, Integrable (fun y => w y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hbaseB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hmA : ∀ i ds x, AEStronglyMeasurable
      (fun y => w y * ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hmB : ∀ i ds x, AEStronglyMeasurable
      (fun y => ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hcutA : ∀ i, (∫ y, w y * ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ a ^ 2)
    (hcutB : ∀ i, (∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ b ^ 2)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (heq : ∀ i ds x, field i ds x =ᵐ[μ] W.coordinate (label i ds x))
    (hsmooth : ∀ q i,
      (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
        (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) :
    Integrable (fun q => W.sourceMass ψ q *
      clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q *
      clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2 ∂μ) ≤
      (72 * C * (117 * (N : ℝ)) ^ 2 *
        ((Real.pi * 4 / 3) * (6 + 12 * (N : ℝ)) ^ 3)) * k ^ 2 *
          (a ^ 2 * (∑' n, ‖D.radiation (ψ n)‖ ^ 2) + b ^ 2 * (∑' n, ‖ψ n‖ ^ 2)) := by
  have hcap : Fintype.card ((S × Fin 3) × Fin 3 × LocalSobolevIndex) ≤ 117 * N := by
    rw [localSobolev_term_card, Fintype.card_prod, Fintype.card_fin]
    omega
  have hL : 0 ≤ (6 + 12 * (N : ℝ)) := by positivity
  obtain ⟨hi, hb⟩ := D.localFieldSize_uniform_moment_from_kernels
    momentum a b (117 * N) hcap hk hL hR hC hkR sobolev
    (fun i : S × Fin 3 => centre i.1) (fun i : S × Fin 3 => base i.2)
    (fun i : S × Fin 3 => label i.2) (fun i => hkernel i.2)
    (fun i => hbaseA i.2) (fun i => hbaseB i.2)
    (fun i => hmA i.2) (fun i => hmB i.2) (fun i => hcutA i.2) (fun i => hcutB i.2)
    ψ hdom hE hP (fun i : S × Fin 3 => field i.2) (fun i => hm i.2)
    (fun i => heq i.2) (Eventually.of_forall (fun q i => hsmooth q i.2))
  have he : (fun q => W.sourceMass ψ q *
      clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2) =
      (fun q => 9 * (W.sourceMass ψ q * localFieldSize
        (fun i : S × Fin 3 => field i.2) (fun i => centre i.1)
        ((6 + 12 * (N : ℝ)) * R) q ^ 2)) := by
    funext q
    dsimp [clusterFieldSize]
    ring
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hi.const_mul 9
  · rw [he, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 9)
    refine h.trans_eq ?_
    push_cast
    ring

end KernelFieldData

end GptLean.Gaussian
