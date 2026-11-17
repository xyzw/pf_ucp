import GptLean.PhysicalGaussianSource
import GptLean.PhysicalPFSpatialObservables
import GptLean.RemovalSourceTests

/-!
Spatial scalar intertwining determines the conjugated multiplication
operator. This gives the density and current tests used by the original
source package directly from ordinary spectral integral identities.
-/

noncomputable section

namespace GptLean.PhysicalGaussianScalarTests

open MeasureTheory MeasureTheory.Measure Filter Topology RemovalSource
  PhotonLocalization PhysicalPFSource
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {Q X H K : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def scalarOperator (a : ℝ) : H →L[ℂ] H := (a : ℂ) • ContinuousLinearMap.id ℂ H

theorem scalarOperator_bound (a A : ℝ) (ha : |a| ≤ A) : ‖scalarOperator (H := H) a‖ ≤ A := by
  change ‖(a : ℂ) • ContinuousLinearMap.id ℂ H‖ ≤ A
  rw [norm_smul]
  calc
    _ ≤ ‖(a : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ A := by simpa only [mul_one, Complex.norm_real, Real.norm_eq_abs] using ha

theorem scalarOperator_inner (a : ℝ) (v : H) :
    inner ℂ v (scalarOperator a v) = ((a * ‖v‖ ^ 2 : ℝ) : ℂ) := by
  simp only [scalarOperator, _root_.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_mul, Complex.ofReal_pow]
  rfl

variable (a : X → ℝ) (ha : AEStronglyMeasurable a ν)
  (A : ℝ) (hb : ∀ x, |a x| ≤ A)

include ha in
theorem productWeightMeasurable : AEStronglyMeasurable (fun qx : Q × X => a qx.2) (μ.prod ν) :=
  ha.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

def productMultiplier : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν) :=
  realL2Multiplier (fun qx => a qx.2) (productWeightMeasurable a ha) A
    (ae_of_all _ fun qx => hb qx.2)

theorem multiplier_complex_inner (v w : Lp H 2 ν) :
    inner ℂ v (realL2Multiplier a ha A (ae_of_all _ hb) w) =
      ∫ x, inner ℂ (v x) (scalarOperator (a x) (w x)) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realL2Multiplier_apply a ha A (ae_of_all _ hb) w] with x hx
  rw [hx]
  simp only [scalarOperator, _root_.smul_apply, ContinuousLinearMap.id_apply,
    Complex.coe_smul]

theorem multiplier_density (v : Lp H 2 ν) :
    inner ℂ v (realL2Multiplier a ha A (ae_of_all _ hb) v) =
      ((∫ x, a x * ‖v x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
  rw [multiplier_complex_inner a ha A hb]
  simp_rw [scalarOperator_inner]
  exact integral_complex_ofReal

variable (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
  (hU : SpatialScalarIntertwining U)

include hU

theorem multiplier_intertwining (v : Lp H 2 ν) :
    U (realL2Multiplier a ha A (ae_of_all _ hb) v) = productMultiplier a ha A hb (U v) := by
  apply Lp.ext
  have hs := hU a ha A hb v (realL2Multiplier a ha A (ae_of_all _ hb) v)
    (by simpa only [Complex.coe_smul] using realL2Multiplier_apply a ha A (ae_of_all _ hb) v)
  have ht := realL2Multiplier_apply (fun qx : Q × X => a qx.2)
    (productWeightMeasurable a ha) A (ae_of_all _ fun qx => hb qx.2) (U v)
  exact hs.trans (by simpa only [productMultiplier, Complex.coe_smul] using ht.symm)

theorem conjugatedMultiplier (v : Lp H 2 ν) :
    conjugatedOperator U (productMultiplier a ha A hb) v =
      realL2Multiplier a ha A (ae_of_all _ hb) v := by
  change U.symm (productMultiplier a ha A hb (U v)) = _
  rw [← multiplier_intertwining a ha A hb U hU v, U.symm_apply_apply]

def densityTest (ψ : ℕ → Lp H 2 ν) (target : ℝ) (hA : 0 ≤ A)
    (hs : HasSum (fun n => ∫ x, a x * ‖ψ n x‖ ^ 2 ∂ν) target) :
    ProductDensityTest U ψ target where
  operator := productMultiplier a ha A hb
  sourceMultiplier x := scalarOperator (a x)
  targetMultiplier qx := scalarOperator (a qx.2)
  sourceBound := A
  targetBound := A
  source_bounded := ae_of_all _ fun x => scalarOperator_bound (a x) A (hb x)
  target_bounded := ae_of_all _ fun qx => scalarOperator_bound (a qx.2) A (hb qx.2)
  source_measurable n :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable ha).smul (Lp.aestronglyMeasurable (ψ n))
  target_measurable v :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (productWeightMeasurable a ha)).smul (Lp.aestronglyMeasurable v)
  source_rankOne v := by
    rw [conjugatedMultiplier a ha A hb U hU]
    exact multiplier_complex_inner a ha A hb v v
  target_rankOne v := by
    simpa only [productMultiplier] using
      (multiplier_complex_inner (ν := μ.prod ν) (H := K) (fun qx : Q × X => a qx.2)
        (productWeightMeasurable a ha) A (fun qx => hb qx.2) v v)
  original := by
    apply (Complex.ofRealCLM.hasSum hs).congr_fun
    intro n
    rw [conjugatedMultiplier a ha A hb U hU]
    exact multiplier_density a ha A hb (ψ n)
  weight := a
  bound := A
  bound_nonneg := hA
  weight_measurable := ha
  weight_bounded := ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x
  scalar qx v := scalarOperator_inner (a qx.2) v

def currentTest [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ dψ : ℕ → Lp H 2 ν) (target : ℝ)
    (hs : HasSum (fun n => ∫ x, a x * (inner ℂ (ψ n x) (dψ n x)).re ∂ν) target) :
    ProductCurrentData U ψ dψ target where
  operator := productMultiplier a ha A hb
  sourceWeight := a
  weight := a
  sourceBound := A
  bound := A
  source_measurable := ha
  source_bounded := ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x
  weight_measurable := ha
  weight_bounded := ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x
  source_rankOne v d := by
    rw [conjugatedMultiplier a ha A hb U hU]
    exact multiplier_tested_inner a ha A (ae_of_all _ hb) v d
  target_rankOne v d := by
    simpa only [productMultiplier] using
      (multiplier_tested_inner (fun qx : Q × X => a qx.2)
        (productWeightMeasurable a ha) A (ae_of_all _ fun qx => hb qx.2) v d)
  original := by
    apply hs.congr_fun
    intro n
    rw [conjugatedMultiplier a ha A hb U hU]
    exact multiplier_tested_inner a ha A (ae_of_all _ hb) (ψ n) (dψ n)

end GptLean.PhysicalGaussianScalarTests
