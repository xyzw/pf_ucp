import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Closure of weak derivative identities under strong L2 approximation.
The test pairings are actual Bochner integrals. Their continuity is proved
using Hölder's inequality, rather than assuming convergence of the tested
integrals. Scalar tests and their derivatives need only belong to L2.

This supplies the approximation passage once an approximating sequence and
L2 convergence of its derivative fields have been established. It does not
construct such approximations or assume a completed Sobolev tensor lift.
-/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter
open scoped ENNReal Topology

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual Bochner pairing with a scalar test function. -/
def l2TestIntegral (φ : X → ℝ) (f : Lp V 2 μ) : V :=
  ∫ x, φ x • f x ∂μ

theorem integrable_l2_test {φ : X → ℝ} (hφ : MemLp φ 2 μ) (f : Lp V 2 μ) :
    Integrable (fun x => φ x • f x) μ := by
  exact memLp_one_iff_integrable.mp ((Lp.memLp f).smul hφ)

/-- Hölder controls a vector-valued test pairing by the two L2 norms. -/
theorem norm_l2TestIntegral_le {φ : X → ℝ} (hφ : MemLp φ 2 μ) (f : Lp V 2 μ) :
    ‖l2TestIntegral φ f‖ ≤ ‖hφ.toLp φ‖ * ‖f‖ := by
  have hsmul : AEStronglyMeasurable (fun x => φ x • f x) μ :=
    hφ.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)
  calc
    ‖l2TestIntegral φ f‖ ≤ ∫ x, ‖φ x • f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (φ • (fun x => f x)) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact integral_norm_eq_lintegral_enorm hsmul
    _ ≤ (eLpNorm φ 2 μ * eLpNorm f 2 μ).toReal := by
      apply ENNReal.toReal_mono (ENNReal.mul_ne_top hφ.eLpNorm_ne_top (Lp.eLpNorm_ne_top f))
      exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable f) hφ.aestronglyMeasurable
    _ = ‖hφ.toLp φ‖ * ‖f‖ := by
      rw [ENNReal.toReal_mul, Lp.norm_toLp, Lp.norm_def]

theorem l2TestIntegral_sub {φ : X → ℝ} (hφ : MemLp φ 2 μ) (f g : Lp V 2 μ) :
    l2TestIntegral φ (f - g) = l2TestIntegral φ f - l2TestIntegral φ g := by
  unfold l2TestIntegral
  calc
    (∫ x, φ x • (f - g) x ∂μ) = ∫ x, φ x • (f x - g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub f g] with x hx
      simpa only [Pi.sub_apply] using congrArg (fun v : V => φ x • v) hx
    _ = _ := by
      simp only [smul_sub]
      exact integral_sub (integrable_l2_test hφ f) (integrable_l2_test hφ g)

theorem l2TestIntegral_lipschitz {φ : X → ℝ} (hφ : MemLp φ 2 μ) :
    LipschitzWith ‖hφ.toLp φ‖₊ (l2TestIntegral (μ := μ) (V := V) φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm, dist_eq_norm, ← l2TestIntegral_sub hφ]
  exact norm_l2TestIntegral_le hφ (f - g)

/-- Strong L2 convergence implies convergence of every L2 test pairing. -/
theorem tendsto_l2TestIntegral {A : Type*} {l : Filter A} {φ : X → ℝ}
    (hφ : MemLp φ 2 μ) {f : A → Lp V 2 μ} {g : Lp V 2 μ}
    (hf : Tendsto f l (𝓝 g)) :
    Tendsto (fun n => ∫ x, φ x • f n x ∂μ) l (𝓝 (∫ x, φ x • g x ∂μ)) :=
  ((l2TestIntegral_lipschitz (V := V) hφ).continuous.tendsto g).comp hf

/-- The integration-by-parts identity is closed under L2 convergence of
both the function and its candidate weak derivative. -/
theorem weak_derivative_identity_closed_l2
    {A : Type*} {l : Filter A} [NeBot l] {φ φ' : X → ℝ}
    (hφ : MemLp φ 2 μ) (hφ' : MemLp φ' 2 μ)
    {f df : A → Lp V 2 μ} {g dg : Lp V 2 μ}
    (hf : Tendsto f l (𝓝 g)) (hdf : Tendsto df l (𝓝 dg))
    (hweak : ∀ᶠ n in l, (∫ x, φ x • df n x ∂μ) = -(∫ x, φ' x • f n x ∂μ)) :
    (∫ x, φ x • dg x ∂μ) = -(∫ x, φ' x • g x ∂μ) := by
  have hleft := tendsto_l2TestIntegral hφ hdf
  have hright := (tendsto_l2TestIntegral hφ' hf).neg
  exact tendsto_nhds_unique hleft (hright.congr' (hweak.mono (fun _ hn => hn.symm)))

/-- The same passage applies simultaneously to any test family, including
the compact smooth tests defining a distributional coordinate derivative. -/
theorem weak_derivative_tests_closed_l2
    {A J : Type*} {l : Filter A} [NeBot l]
    (φ φ' : J → X → ℝ) (hφ : ∀ j, MemLp (φ j) 2 μ)
    (hφ' : ∀ j, MemLp (φ' j) 2 μ)
    {f df : A → Lp V 2 μ} {g dg : Lp V 2 μ}
    (hf : Tendsto f l (𝓝 g)) (hdf : Tendsto df l (𝓝 dg))
    (hweak : ∀ j, ∀ᶠ n in l,
      (∫ x, φ j x • df n x ∂μ) = -(∫ x, φ' j x • f n x ∂μ)) :
    ∀ j, (∫ x, φ j x • dg x ∂μ) = -(∫ x, φ' j x • g x ∂μ) := by
  intro j
  exact weak_derivative_identity_closed_l2 (hφ j) (hφ' j) hf hdf (hweak j)

/-- Passing to the L2 equivalence class does not change the actual test integral. -/
theorem l2TestIntegral_toLp (φ : X → ℝ) {f : X → V} (hf : MemLp f 2 μ) :
    l2TestIntegral φ (hf.toLp f) = ∫ x, φ x • f x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Raw-function version of test-pairing convergence, in the L2 seminorm. -/
theorem tendsto_integral_l2_test_of_eLpNorm
    {A : Type*} {l : Filter A} {φ : X → ℝ} (hφ : MemLp φ 2 μ)
    {f : A → X → V} {g : X → V}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ x, φ x • f n x ∂μ) l (𝓝 (∫ x, φ x • g x ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv
  have htest := tendsto_l2TestIntegral hφ hLp
  change Tendsto (fun n => l2TestIntegral φ ((hf n).toLp (f n))) l
    (𝓝 (l2TestIntegral φ (hg.toLp g))) at htest
  simpa only [l2TestIntegral_toLp] using htest

/-- The weak identity closes for raw approximants and raw derivative fields.
Only convergence in the two L2 seminorms is required. -/
theorem weak_derivative_identity_closed_eLpNorm
    {A : Type*} {l : Filter A} [NeBot l] {φ φ' : X → ℝ}
    (hφ : MemLp φ 2 μ) (hφ' : MemLp φ' 2 μ)
    {f df : A → X → V} {g dg : X → V}
    (hf : ∀ n, MemLp (f n) 2 μ) (hdf : ∀ n, MemLp (df n) 2 μ)
    (hg : MemLp g 2 μ) (hdg : MemLp dg 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0))
    (hdconv : Tendsto (fun n => eLpNorm (df n - dg) 2 μ) l (𝓝 0))
    (hweak : ∀ᶠ n in l, (∫ x, φ x • df n x ∂μ) = -(∫ x, φ' x • f n x ∂μ)) :
    (∫ x, φ x • dg x ∂μ) = -(∫ x, φ' x • g x ∂μ) := by
  have hleft := tendsto_integral_l2_test_of_eLpNorm hφ hdf hdg hdconv
  have hright := (tendsto_integral_l2_test_of_eLpNorm hφ' hf hg hconv).neg
  exact tendsto_nhds_unique hleft (hright.congr' (hweak.mono (fun _ hn => hn.symm)))

/-- Raw-function closure for every test in a prescribed family. -/
theorem weak_derivative_tests_closed_eLpNorm
    {A J : Type*} {l : Filter A} [NeBot l]
    (φ φ' : J → X → ℝ) (hφ : ∀ j, MemLp (φ j) 2 μ)
    (hφ' : ∀ j, MemLp (φ' j) 2 μ)
    {f df : A → X → V} {g dg : X → V}
    (hf : ∀ n, MemLp (f n) 2 μ) (hdf : ∀ n, MemLp (df n) 2 μ)
    (hg : MemLp g 2 μ) (hdg : MemLp dg 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0))
    (hdconv : Tendsto (fun n => eLpNorm (df n - dg) 2 μ) l (𝓝 0))
    (hweak : ∀ j, ∀ᶠ n in l,
      (∫ x, φ j x • df n x ∂μ) = -(∫ x, φ' j x • f n x ∂μ)) :
    ∀ j, (∫ x, φ j x • dg x ∂μ) = -(∫ x, φ' j x • g x ∂μ) := by
  intro j
  exact weak_derivative_identity_closed_eLpNorm (hφ j) (hφ' j)
    hf hdf hg hdg hconv hdconv (hweak j)

end GptLean.SymmetricLift
