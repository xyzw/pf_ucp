import GptLean.PhysicalFockKrausL2
import GptLean.PhysicalPhotonMarginalMoments

/-!
Nonnegative quadratic resolution identities lift through the actual
electronic L² space by dominated convergence. The family and operators
are arbitrary bounded maps, and no physical localization estimate is
included in the statement.
-/

noncomputable section
namespace GptLean.PhysicalL2QuadraticSeries

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {ι : Type*} [Countable ι] {K : ι → Type*}
  [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]

theorem lift_hasSum (Q : ∀ i, H →L[ℂ] K i) (B : ∀ i, K i →L[ℂ] K i)
    (A : H →L[ℂ] H)
    (hpos : ∀ i v, 0 ≤ (⟪Q i v, B i (Q i v)⟫_ℂ).re)
    (hseries : ∀ v, HasSum (fun i => (⟪Q i v, B i (Q i v)⟫_ℂ).re)
      (⟪v, A v⟫_ℂ).re) (u : Lp H 2 μ) :
    HasSum (fun i => (⟪(Q i).compLpL 2 μ u,
      (B i).compLpL 2 μ ((Q i).compLpL 2 μ u)⟫_ℂ).re)
      (⟪u, A.compLpL 2 μ u⟫_ℂ).re := by
  have hm (i : ι) : AEStronglyMeasurable
      (fun x => (⟪Q i (u x), B i (Q i (u x))⟫_ℂ).re) μ := by
    exact (Complex.continuous_re.comp
      ((Q i).continuous.inner ((B i).continuous.comp (Q i).continuous))).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable u)
  have hi : Integrable (fun x => ∑' i, (⟪Q i (u x), B i (Q i (u x))⟫_ℂ).re) μ := by
    simpa only [(hseries _).tsum_eq] using PhysicalPhotonMarginal.quadratic_integrable A u
  have hs := hasSum_integral_of_dominated_convergence
    (fun i x => (⟪Q i (u x), B i (Q i (u x))⟫_ℂ).re) hm
    (fun i => ae_of_all μ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos i (u x))]))
    (ae_of_all μ (fun x => (hseries (u x)).summable)) hi
    (ae_of_all μ (fun x => hseries (u x)))
  rw [← PhysicalPhotonMarginal.quadratic_integral] at hs
  have he (i : ι) : (∫ x, (⟪Q i (u x), B i (Q i (u x))⟫_ℂ).re ∂μ) =
      (⟪(Q i).compLpL 2 μ u,
        (B i).compLpL 2 μ ((Q i).compLpL 2 μ u)⟫_ℂ).re := by
    rw [PhysicalPhotonMarginal.quadratic_integral]
    apply integral_congr_ae
    filter_upwards [(Q i).coeFn_compLpL u] with x hx
    exact congrArg (fun v => (⟪v, B i v⟫_ℂ).re) hx.symm
  simpa only [he] using hs

theorem lift_norm_hasSum (Q : ∀ i, H →L[ℂ] K i) (w : ι → ℝ)
    (A : H →L[ℂ] H) (hpos : ∀ i, 0 ≤ w i)
    (hseries : ∀ v, HasSum (fun i => w i * ‖Q i v‖ ^ 2) (⟪v, A v⟫_ℂ).re)
    (u : Lp H 2 μ) :
    HasSum (fun i => w i * ‖(Q i).compLpL 2 μ u‖ ^ 2)
      (⟪u, A.compLpL 2 μ u⟫_ℂ).re := by
  have hm (i : ι) : AEStronglyMeasurable (fun x => w i * ‖Q i (u x)‖ ^ 2) μ :=
    ((Q i).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm.pow 2 |>.const_mul (w i)
  have hi : Integrable (fun x => ∑' i, w i * ‖Q i (u x)‖ ^ 2) μ := by
    simpa only [(hseries _).tsum_eq] using PhysicalPhotonMarginal.quadratic_integrable A u
  have hs := hasSum_integral_of_dominated_convergence
    (fun i x => w i * ‖Q i (u x)‖ ^ 2) hm
    (fun i => ae_of_all μ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos i) (sq_nonneg _))]))
    (ae_of_all μ (fun x => (hseries (u x)).summable)) hi
    (ae_of_all μ (fun x => hseries (u x)))
  rw [← PhysicalPhotonMarginal.quadratic_integral] at hs
  have he (i : ι) : (∫ x, w i * ‖Q i (u x)‖ ^ 2 ∂μ) =
      w i * ‖(Q i).compLpL 2 μ u‖ ^ 2 := by
    let : InnerProductSpace ℝ (K i) := InnerProductSpace.rclikeToReal ℂ (K i)
    rw [integral_const_mul, PhotonKernelLocalization.l2_norm_sq_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [(Q i).coeFn_compLpL u] with x hx
    exact congrArg (fun v : K i => ‖v‖ ^ 2) hx.symm
  simpa only [he] using hs

theorem lift_norm_defect_hasSum (Q : ∀ i, H →L[ℂ] K i) (w : ι → ℝ)
    (A : H →L[ℂ] H) (hpos : ∀ i, 0 ≤ w i)
    (hseries : ∀ v, HasSum (fun i => w i * ‖Q i v‖ ^ 2) (‖v‖ ^ 2 - ‖A v‖ ^ 2))
    (u : Lp H 2 μ) :
    HasSum (fun i => w i * ‖(Q i).compLpL 2 μ u‖ ^ 2)
      (‖u‖ ^ 2 - ‖A.compLpL 2 μ u‖ ^ 2) := by
  have hm (i : ι) : AEStronglyMeasurable (fun x => w i * ‖Q i (u x)‖ ^ 2) μ :=
    ((Q i).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm.pow 2 |>.const_mul (w i)
  have hu : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hA : Integrable (fun x => ‖A (u x)‖ ^ 2) μ := by
    apply ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A.compLpL 2 μ u))).mp
      (Lp.memLp (A.compLpL 2 μ u))).congr
    filter_upwards [A.coeFn_compLpL u] with x hx
    exact congrArg (fun v : H => ‖v‖ ^ 2) hx
  have hi : Integrable (fun x => ∑' i, w i * ‖Q i (u x)‖ ^ 2) μ := by
    exact (hu.sub hA).congr (ae_of_all μ fun x => (hseries (u x)).tsum_eq.symm)
  have hs := hasSum_integral_of_dominated_convergence
    (fun i x => w i * ‖Q i (u x)‖ ^ 2) hm
    (fun i => ae_of_all μ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos i) (sq_nonneg _))]))
    (ae_of_all μ (fun x => (hseries (u x)).summable)) hi
    (ae_of_all μ (fun x => hseries (u x)))
  have he (i : ι) : (∫ x, w i * ‖Q i (u x)‖ ^ 2 ∂μ) =
      w i * ‖(Q i).compLpL 2 μ u‖ ^ 2 := by
    let : InnerProductSpace ℝ (K i) := InnerProductSpace.rclikeToReal ℂ (K i)
    rw [integral_const_mul, PhotonKernelLocalization.l2_norm_sq_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [(Q i).coeFn_compLpL u] with x hx
    exact congrArg (fun v : K i => ‖v‖ ^ 2) hx.symm
  have hnorm : (∫ x, ‖u x‖ ^ 2 - ‖A (u x)‖ ^ 2 ∂μ) =
      ‖u‖ ^ 2 - ‖A.compLpL 2 μ u‖ ^ 2 := by
    let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    rw [integral_sub hu hA, PhotonKernelLocalization.l2_norm_sq_eq_integral,
      PhotonKernelLocalization.l2_norm_sq_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [A.coeFn_compLpL u] with x hx
    exact congrArg (fun v : H => ‖v‖ ^ 2) hx.symm
  simpa only [he, hnorm] using hs

end GptLean.PhysicalL2QuadraticSeries
