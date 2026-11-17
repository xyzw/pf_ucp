import GptLean.Gaussian.SpatialVectorField

/-! The local Gaussian field moment for one actual localized source vector.
Zero-fiber preservation follows from WIS isometry. Only the standard zero
facts for the radiation operator and its domain are used to form the
singleton source sequence. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace WienerSegalData

variable {Q H K G : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedSpace ℝ K]
  (W : WienerSegalData Q H K G μ)

theorem toFiber_zero_ae : W.toFiber 0 =ᵐ[μ] 0 := by
  have h : (fun q => ENNReal.ofReal (‖W.toFiber 0 q‖ ^ 2)) =ᵐ[μ] 0 := by
    apply (lintegral_eq_zero_iff'
      ((W.measurable_fiber 0).norm.pow 2).aemeasurable.ennreal_ofReal).mp
    simpa using W.norm_sq 0
  filter_upwards [h] with q hq
  have hz : ‖W.toFiber 0 q‖ = 0 := by
    have hh := ENNReal.ofReal_eq_zero.mp hq
    nlinarith [norm_nonneg (W.toFiber 0 q)]
  exact norm_eq_zero.mp hz

def singleSource (u : H) (n : ℕ) : H := if n = 0 then u else 0

theorem sourceMass_singleSource (u : H) :
    W.sourceMass (singleSource u) =ᵐ[μ] (fun q => ‖W.toFiber u q‖ ^ 2) := by
  filter_upwards [W.toFiber_zero_ae] with q hq
  unfold sourceMass
  rw [tsum_eq_single 0]
  · simp [singleSource]
  · intro n hn
    simp [singleSource, hn, hq]

end WienerSegalData

namespace KernelFieldData

variable {S Q H K G Ω : Type*} [Fintype S]
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

/-- One localized vector has the source-weighted cluster field moment,
with a constant depending only on N and deterministic Sobolev constants. -/
theorem single_clusterFieldSize_moment_from_kernels
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
    (u : H) (hdom : D.radiationDomain u)
    (hdom0 : D.radiationDomain 0) (hrad0 : D.radiation 0 = 0)
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (heq : ∀ i ds x, field i ds x =ᵐ[μ] W.coordinate (label i ds x))
    (hsmooth : ∀ q i,
      (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
        (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) :
    Integrable (fun q => ‖W.toFiber u q‖ ^ 2 *
      clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2) μ ∧
    (∫ q, ‖W.toFiber u q‖ ^ 2 *
      clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2 ∂μ) ≤
      (72 * C * (117 * (N : ℝ)) ^ 2 *
        ((Real.pi * 4 / 3) * (6 + 12 * (N : ℝ)) ^ 3)) * k ^ 2 *
          (a ^ 2 * ‖D.radiation u‖ ^ 2 + b ^ 2 * ‖u‖ ^ 2) := by
  let ψ := WienerSegalData.singleSource u
  have hψ (n : ℕ) : D.radiationDomain (ψ n) := by
    by_cases hn : n = 0 <;> simp [ψ, WienerSegalData.singleSource, hn, hdom, hdom0]
  have hrad : (fun n => ‖D.radiation (ψ n)‖ ^ 2) =
      (fun n : ℕ => if n = 0 then ‖D.radiation u‖ ^ 2 else 0) := by
    funext n
    by_cases hn : n = 0 <;> simp [ψ, WienerSegalData.singleSource, hn, hrad0]
  have hnorm : (fun n => ‖ψ n‖ ^ 2) =
      (fun n : ℕ => if n = 0 then ‖u‖ ^ 2 else 0) := by
    funext n
    by_cases hn : n = 0 <;> simp [ψ, WienerSegalData.singleSource, hn]
  have hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2) := by
    rw [hrad]
    exact (hasSum_ite_eq 0 _).summable
  have hP : Summable (fun n => ‖ψ n‖ ^ 2) := by
    rw [hnorm]
    exact (hasSum_ite_eq 0 _).summable
  obtain ⟨hi, hb⟩ := D.clusterFieldSize_moment_from_kernels momentum a b N hcard
    hk hR hC hkR sobolev centre base label hkernel hbaseA hbaseB hmA hmB hcutA hcutB
    ψ hψ hE hP field hm heq hsmooth
  have he : (fun q => W.sourceMass ψ q *
      clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2) =ᵐ[μ]
      (fun q => ‖W.toFiber u q‖ ^ 2 *
        clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2) :=
    (W.sourceMass_singleSource u).mono (fun q hq => congrArg
      (fun t : ℝ => t * clusterFieldSize field centre ((6 + 12 * (N : ℝ)) * R) q ^ 2) hq)
  refine ⟨hi.congr he, ?_⟩
  rw [← integral_congr_ae he]
  simpa only [hrad, hnorm, tsum_ite_eq] using hb

end KernelFieldData

end GptLean.Gaussian
