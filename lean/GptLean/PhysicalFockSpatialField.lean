import GptLean.PhysicalFockKernelField
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
Actual position-dependent fields on electronic L² of the radiation graph.

The operator acts pointwise through the constructed Fock field. Strong
measurability follows from continuous kernel dependence, and uniform
bounds on the paired physical kernels imply the integrated radiation
estimate. No spatial field-output estimate is assumed.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

section Multiplier

variable {X Q H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (μ : Measure X) (A : X → Q →L[ℂ] H)
  (hA : AEStronglyMeasurable A μ) (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ M)

include hA hb in
private theorem operatorMultiplier_memLp (u : Lp Q 2 μ) :
    MemLp (fun x => A x (u x)) 2 μ := by
  have hc : Continuous (fun z : (Q →L[ℂ] H) × Q => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  apply ((Lp.memLp u).norm.const_mul M).mono'
    (hc.comp_aestronglyMeasurable (hA.prodMk (Lp.aestronglyMeasurable u)))
  filter_upwards [hb] with x hx
  exact ((A x).le_opNorm (u x)).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

private def operatorMultiplierOutput (u : Lp Q 2 μ) : Lp H 2 μ :=
  (operatorMultiplier_memLp μ A hA M hb u).toLp _

private theorem operatorMultiplierOutput_ae (u : Lp Q 2 μ) :
    operatorMultiplierOutput μ A hA M hb u =ᵐ[μ] fun x => A x (u x) :=
  (operatorMultiplier_memLp μ A hA M hb u).coeFn_toLp

private def operatorMultiplierLinear : Lp Q 2 μ →ₗ[ℂ] Lp H 2 μ :=
    { toFun := operatorMultiplierOutput μ A hA M hb
      map_add' u v := by
        apply Lp.ext
        filter_upwards [operatorMultiplierOutput_ae μ A hA M hb (u + v),
          operatorMultiplierOutput_ae μ A hA M hb u,
          operatorMultiplierOutput_ae μ A hA M hb v, Lp.coeFn_add u v,
          Lp.coeFn_add (operatorMultiplierOutput μ A hA M hb u)
            (operatorMultiplierOutput μ A hA M hb v)] with x ha hb hc hd he
        rw [ha, he, Pi.add_apply, hb, hc, hd, Pi.add_apply, map_add]
      map_smul' c u := by
        apply Lp.ext
        filter_upwards [operatorMultiplierOutput_ae μ A hA M hb (c • u),
          operatorMultiplierOutput_ae μ A hA M hb u, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (operatorMultiplierOutput μ A hA M hb u)] with x ha hb hc hd
        simp only [RingHom.id_apply]
        rw [ha, hd, Pi.smul_apply, hb, hc, Pi.smul_apply, map_smul] }

private theorem operatorMultiplierOutput_norm_le (u : Lp Q 2 μ) :
    ‖operatorMultiplierOutput μ A hA M hb u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operatorMultiplierOutput_ae μ A hA M hb u, hb] with x hx hk
  rw [hx]
  exact ((A x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right hk (norm_nonneg _))

private def operatorMultiplier : Lp Q 2 μ →L[ℂ] Lp H 2 μ :=
  (operatorMultiplierLinear μ A hA M hb).mkContinuous M
    (operatorMultiplierOutput_norm_le μ A hA M hb)

private theorem operatorMultiplier_ae (u : Lp Q 2 μ) :
    operatorMultiplier μ A hA M hb u =ᵐ[μ] fun x => A x (u x) :=
  operatorMultiplierOutput_ae μ A hA M hb u

/-- Pointwise bounded operator multiplication on L². -/
def spatialOperator : Lp Q 2 μ →L[ℂ] Lp H 2 μ := operatorMultiplier μ A hA M hb

theorem spatialOperator_ae (u : Lp Q 2 μ) :
    spatialOperator μ A hA M hb u =ᵐ[μ] fun x => A x (u x) :=
  operatorMultiplier_ae μ A hA M hb u

end Multiplier

section IntegralBound

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (μ : Measure X)

theorem l2_square_bound (f d v : Lp H 2 μ) (A B : ℝ)
    (hp : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 ≤ A * ‖d x‖ ^ 2 + B * ‖v x‖ ^ 2) :
    ‖f‖ ^ 2 ≤ A * ‖d‖ ^ 2 + B * ‖v‖ ^ 2 := by
  have hd := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable d)).mp (Lp.memLp d)
  have hv := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral f,
    PhotonKernelLocalization.l2_norm_sq_eq_integral d,
    PhotonKernelLocalization.l2_norm_sq_eq_integral v,
    ← integral_const_mul, ← integral_const_mul, ← integral_add (hd.const_mul A) (hv.const_mul B)]
  exact integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
    ((hd.const_mul A).add (hv.const_mul B)) hp

end IntegralBound

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (C : CanonicalSectorCCR photonMeasure)

abbrev SpatialRadiationGraph := Lp RadiationGraphSpace 2 μ
abbrev SpatialPhotonSpace := Lp PhotonFock 2 μ

def spatialRadiationInclusion : SpatialRadiationGraph μ →L[ℂ] SpatialPhotonSpace μ :=
  radiationGraphInclusion.compLpL 2 μ

def spatialRadiationDerivative : SpatialRadiationGraph μ →L[ℂ] SpatialPhotonSpace μ :=
  radiationGraphDerivative.compLpL 2 μ

variable (κ : X → WeightedPhotonKernel) (hκ : AEStronglyMeasurable κ μ)
  (M : ℝ) (hbound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)

include hκ in
theorem spatialField_aestronglyMeasurable (u : SpatialRadiationGraph μ) :
    AEStronglyMeasurable (fun x => kernelField C (κ x) (u x)) μ := by
  have hc : Continuous (fun z : (RadiationGraphSpace →L[ℂ] PhotonFock) × RadiationGraphSpace =>
      z.1 z.2) := continuous_fst.clm_apply continuous_snd
  exact hc.comp_aestronglyMeasurable
    (((kernelField_continuous C).comp_aestronglyMeasurable hκ).prodMk
      (Lp.aestronglyMeasurable u))

/-- The spatial field is the actual pointwise Fock operator. -/
def spatialField : SpatialRadiationGraph μ →L[ℂ] SpatialPhotonSpace μ :=
  operatorMultiplier μ (fun x => kernelField C (κ x))
    ((kernelField_continuous C).comp_aestronglyMeasurable hκ)
    ((2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) * M)
    (by
      filter_upwards [hbound] with x hx
      exact (kernelField_opNorm_le C (κ x)).trans (by gcongr))

theorem spatialField_ae (u : SpatialRadiationGraph μ) :
    spatialField μ C κ hκ M hbound u =ᵐ[μ] fun x => kernelField C (κ x) (u x) :=
  operatorMultiplier_ae μ _ _ _ _ u

attribute [irreducible] spatialField

private theorem scalar_field_square_bound {s a b d i : ℝ} (hs : 0 ≤ s)
    (h : s ≤ 2 * a * d + b * i) : s ^ 2 ≤ 8 * a ^ 2 * d ^ 2 + 2 * b ^ 2 * i ^ 2 := by
  have hsq := pow_le_pow_left₀ hs h 2
  nlinarith [sq_nonneg (2 * a * d - b * i)]

/-- Separate kernel norms give the physical radiation-relative field bound. -/
theorem spatialField_radiation_bound (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hneg : ∀ᵐ x ∂μ, ‖(κ x).val.2‖ ≤ A)
    (hl2 : ∀ᵐ x ∂μ, ‖(κ x).val.1‖ ≤ B) (u : SpatialRadiationGraph μ) :
    ‖spatialField μ C κ hκ M hbound u‖ ^ 2 ≤
      8 * A ^ 2 * ‖spatialRadiationDerivative μ u‖ ^ 2 +
        2 * B ^ 2 * ‖spatialRadiationInclusion μ u‖ ^ 2 := by
  let : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ PhotonFock
  refine l2_square_bound μ (spatialField μ C κ hκ M hbound u)
    (spatialRadiationDerivative μ u) (spatialRadiationInclusion μ u)
    (8 * A ^ 2) (2 * B ^ 2) ?_
  have hD : spatialRadiationDerivative μ u =ᵐ[μ]
      fun x => radiationGraphDerivative (u x) := radiationGraphDerivative.coeFn_compLpL u
  have hI : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  filter_upwards [spatialField_ae μ C κ hκ M hbound u, hneg, hl2, hD, hI]
    with x hf hn hl hd hi
  have hb : ‖kernelField C (κ x) (u x)‖ ≤
      2 * A * ‖radiationGraphDerivative (u x)‖ + B * ‖radiationGraphInclusion (u x)‖ :=
    (kernelField_norm_le C (κ x) (u x)).trans (by gcongr)
  calc
    _ = ‖kernelField C (κ x) (u x)‖ ^ 2 := congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hf
    _ ≤ 8 * A ^ 2 * ‖radiationGraphDerivative (u x)‖ ^ 2 +
        2 * B ^ 2 * ‖radiationGraphInclusion (u x)‖ ^ 2 :=
      scalar_field_square_bound (norm_nonneg _) hb
    _ = _ := congrArg₂ (fun d v : PhotonFock => 8 * A ^ 2 * ‖d‖ ^ 2 + 2 * B ^ 2 * ‖v‖ ^ 2)
      hd.symm hi.symm

end GptLean.PhysicalFock
