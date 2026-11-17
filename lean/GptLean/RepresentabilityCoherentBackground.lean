import GptLean.PhysicalFockFieldGraphMeasurable
import GptLean.PhysicalFockFiniteOperators
import GptLean.PhysicalFockAnnihilationForm
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Exponential

/-!
Universal Weyl calculus on the already constructed symmetric L2 Fock model.
The generators and both operator graphs below use the actual sector operators.
This is explicit permitted operator background, not a representability result.
No particle configuration, density, prescribed current or trial state occurs
in its fields. Coherent and radiation conclusions are derived in companions.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- The maximal annihilation graph is fixed by adjacent-sector annihilation. -/
def AnnihilationGraph (g : Lp ℂ 2 μ) (u v : Fock μ) : Prop :=
  ∀ n, v n = annihilationSector μ n g (u (n + 1))

/-- A fixed finite number cutoff, rather than a bound on the spatial support. -/
def FiniteNumberSupport (M : ℕ) (u : Fock μ) : Prop :=
  ∀ n, M < n → u n = 0

/-- Creation in a variable kernel, with its input sector fixed. -/
def creationDirection (n : ℕ) (u : Sector μ n) : Lp ℂ 2 μ →L[ℝ] Fock μ :=
  ((lp.singleContinuousLinearMap ℂ (Sector μ) 2 (n + 1)).comp
    ((creationSectorKernelMap μ n).flip u)).restrictScalars ℝ

@[simp] theorem creationDirection_apply (n : ℕ) (u : Sector μ n) (h : Lp ℂ 2 μ) :
    creationDirection μ n u h = lp.single 2 (n + 1) (creationSector μ n h u) := rfl

/-- Annihilation is real linear in its variable kernel. -/
def annihilationDirection (n : ℕ) (u : Sector μ (n + 1)) :
    Lp ℂ 2 μ →L[ℝ] Fock μ where
  toFun h := lp.single 2 n (annihilationSector μ n h u)
  map_add' h k := by
    rw [annihilationSector_add, add_apply, lp.single_add]
  map_smul' r h := by
    change lp.single 2 n (annihilationSector μ n ((r : ℂ) • h) u) =
      (r : ℂ) • lp.single 2 n (annihilationSector μ n h u)
    rw [annihilationSector_smul, Complex.conj_ofReal, smul_apply, lp.single_smul]
  cont := (lp.singleContinuousLinearMap ℂ (Sector μ) 2 n).continuous.comp
    ((annihilationSector_continuous_kernel μ n).clm_apply continuous_const)

@[simp] theorem annihilationDirection_apply (n : ℕ) (u : Sector μ (n + 1))
    (h : Lp ℂ 2 μ) :
    annihilationDirection μ n u h = lp.single 2 n (annihilationSector μ n h u) := rfl

/-- The actual finite-number infinitesimal Weyl generator. -/
def finiteWeylGenerator (M : ℕ) (u : Fock μ) : Lp ℂ 2 μ →L[ℝ] Fock μ :=
  (∑ n ∈ Finset.range (M + 1), creationDirection μ n (u n)) -
    ∑ n ∈ Finset.range M, annihilationDirection μ n (u (n + 1))

theorem finiteWeylGenerator_apply (M : ℕ) (u : Fock μ) (h : Lp ℂ 2 μ) :
    finiteWeylGenerator μ M u h =
      creationFinite μ M h u - annihilationFinite μ M h u := by
  simp only [finiteWeylGenerator, sub_apply,
    sum_apply, creationDirection_apply, annihilationDirection_apply,
    creationFinite, annihilationFinite, creationBlock, annihilationBlock,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rfl

/-- The scalar phase term in the derivative of the Weyl action. -/
def weylBerryDirection (f : Lp ℂ 2 μ) (u : Fock μ) : Lp ℂ 2 μ →L[ℝ] Fock μ :=
  (Complex.imCLM.comp ((innerSL ℂ f).restrictScalars ℝ)).smulRight (Complex.I • u)

theorem weylBerryDirection_apply (f h : Lp ℂ 2 μ) (u : Fock μ) :
    weylBerryDirection μ f u h = (Complex.I * ((⟪f, h⟫_ℂ).im : ℂ)) • u := by
  simp only [weylBerryDirection, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    innerSL_apply_apply, Complex.imCLM_apply]
  change ((⟪f, h⟫_ℂ).im : ℂ) • (Complex.I • u) = _
  rw [smul_smul, mul_comm]

/-- A continuous real-linear map defined entirely by the concrete generators. -/
def finiteWeylDerivative
    (W : Lp ℂ 2 μ → Fock μ ≃ₗᵢ[ℂ] Fock μ)
    (M : ℕ) (f : Lp ℂ 2 μ) (u : Fock μ) : Lp ℂ 2 μ →L[ℝ] Fock μ :=
  ((W f).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).comp
    (finiteWeylGenerator μ M u + weylBerryDirection μ f u)

theorem finiteWeylDerivative_apply
    (W : Lp ℂ 2 μ → Fock μ ≃ₗᵢ[ℂ] Fock μ)
    (M : ℕ) (f h : Lp ℂ 2 μ) (u : Fock μ) :
    finiteWeylDerivative μ W M f u h = W f
      (creationFinite μ M h u - annihilationFinite μ M h u +
        (Complex.I * ((⟪f, h⟫_ℂ).im : ℂ)) • u) := by
  rw [finiteWeylDerivative, ContinuousLinearMap.comp_apply,
    add_apply, finiteWeylGenerator_apply, weylBerryDirection_apply]
  rfl

/-- Ordinary Weyl identities on one specified concrete Fock model.
The differential formula is on every finite-number vector and the graph
rules are on the maximal actual graphs, so neither is a trial-state premise. -/
structure ConcreteWeylLaw where
  weyl : Lp ℂ 2 μ → Fock μ ≃ₗᵢ[ℂ] Fock μ
  zero : weyl 0 = LinearIsometryEquiv.refl ℂ (Fock μ)
  compose : ∀ f g u,
    weyl f (weyl g u) =
      Complex.exp (-Complex.I * ((⟪f, g⟫_ℂ).im : ℂ)) • weyl (f + g) u
  continuous : Continuous (fun p : Lp ℂ 2 μ × Fock μ => weyl p.1 p.2)
  finite_derivative : ∀ M u, FiniteNumberSupport μ M u → ∀ f,
    HasFDerivAt (fun h => weyl h u) (finiteWeylDerivative μ weyl M f u) f
  annihilation_shift : ∀ f g u v, AnnihilationGraph μ g u v →
    AnnihilationGraph μ g (weyl f u) (weyl f (v + ⟪g, f⟫_ℂ • u))
  field_shift : ∀ f g u v, SegalGraph μ g u v →
    SegalGraph μ g (weyl f u)
      (weyl f (v + ((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) • u))

/-- The permitted Weyl background is uniform over all scalar L2 models.
It is an explicit premise and introduces no axiom. -/
structure StandardConcreteWeylBackground : Prop where
  law : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ],
    Nonempty (ConcreteWeylLaw μ)

def StandardConcreteWeylBackground.on (B : StandardConcreteWeylBackground)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] : ConcreteWeylLaw μ :=
  Classical.choice (B.law Ω μ)

namespace ConcreteWeylLaw

variable (W : ConcreteWeylLaw μ)

/-- Strong continuity suffices for the product rule along a coordinate line.
There is no assumption of operator-norm continuity of the full Weyl family. -/
theorem hasDerivAt_apply {f : ℝ → Lp ℂ 2 μ} {z : ℝ → Fock μ}
    {df : Lp ℂ 2 μ} {dz : Fock μ} {t : ℝ}
    (hf : HasDerivAt f df t) (hz : HasDerivAt z dz t)
    (M : ℕ) (hM : FiniteNumberSupport μ M (z t)) :
    HasDerivAt (fun s => W.weyl (f s) (z s))
      (finiteWeylDerivative μ W.weyl M (f t) (z t) df + W.weyl (f t) dz) t := by
  have hfixed := (W.finite_derivative M (z t) hM (f t)).comp_hasDerivAt t hf
  have hmove := (W.continuous.tendsto (f t, dz)).comp
    ((hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds hz.tendsto_slope)
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hfixed.tendsto_slope.add hmove using 1
  funext s
  let A := (W.weyl (f s)).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  change (s - t)⁻¹ • (W.weyl (f s) (z s) - W.weyl (f t) (z t)) =
    (s - t)⁻¹ • (W.weyl (f s) (z t) - W.weyl (f t) (z t)) +
      A ((s - t)⁻¹ • (z s - z t))
  rw [map_smul, map_sub]
  change (s - t)⁻¹ • (W.weyl (f s) (z s) - W.weyl (f t) (z t)) =
    (s - t)⁻¹ • (W.weyl (f s) (z t) - W.weyl (f t) (z t)) +
      (s - t)⁻¹ • (W.weyl (f s) (z s) - W.weyl (f s) (z t))
  simp only [smul_sub]
  abel

end ConcreteWeylLaw

end GptLean.Representability
