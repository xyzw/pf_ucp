import GptLean.RemovalChannel
import GptLean.RemovalPhase

/-!
The conditional source is specified by actual product-space L² vectors.
Its phased hard derivative is constructed by subtracting the repair
velocity from the original conditioned covariant derivative. The shift
in the channel cancels this subtraction identically. Integrability,
normalization and source-energy equalities are derived from the L² data.
-/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Repair

variable {Q X J H F : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

structure ConditionedSource (μ : Measure Q) (ν : Measure X) (J H F : Type*)
    [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  source : ℕ → Lp H 2 (μ.prod ν)
  covariant : ℕ → J → Lp H 2 (μ.prod ν)
  rest : ℕ → Lp F 2 (μ.prod ν)
  normalized : HasSum (fun i => ‖source i‖ ^ 2) 1
  kinetic_summable : Summable (fun i => (1 / 2 : ℝ) * ∑ j, ‖covariant i j‖ ^ 2)
  rest_summable : Summable (fun i => ‖rest i‖ ^ 2)
  soft : ℕ → ℝ
  soft_nonneg : ∀ i, 0 ≤ soft i
  soft_summable : Summable soft

namespace ConditionedSource

variable (S : ConditionedSource μ ν J H F)

def input (i : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ‖S.covariant i j‖ ^ 2 + ‖S.rest i‖ ^ 2 + S.soft i

theorem input_summable : Summable S.input :=
  (S.kinetic_summable.add S.rest_summable).add S.soft_summable

def phasedSource (w : ℕ → Q × X → ℂ) (i : ℕ) (qx : Q × X) : H :=
  w i qx • S.source i qx

def phasedHardDerivative (w : ℕ → Q × X → ℂ)
    (s : ℕ → J → Q × X → ℝ) (i : ℕ) (j : J) (qx : Q × X) : H :=
  w i qx • (S.covariant i j qx - (s i j qx : ℂ) • S.source i qx)

def phasedRest (w : ℕ → Q × X → ℂ) (i : ℕ) (qx : Q × X) : F :=
  w i qx • S.rest i qx

theorem phasedSource_stronglyMeasurable (w : ℕ → Q × X → ℂ)
    (hw : ∀ i, StronglyMeasurable (w i)) (i : ℕ) :
    StronglyMeasurable (S.phasedSource w i) := (hw i).smul (Lp.stronglyMeasurable (S.source i))

theorem phasedHardDerivative_measurable (w : ℕ → Q × X → ℂ)
    (s : ℕ → J → Q × X → ℝ)
    (hw : ∀ i, StronglyMeasurable (w i))
    (hs : ∀ i j, AEStronglyMeasurable (s i j) (μ.prod ν)) (i : ℕ) (j : J) :
    AEStronglyMeasurable (S.phasedHardDerivative w s i j) (μ.prod ν) :=
  (hw i).aestronglyMeasurable.smul ((Lp.aestronglyMeasurable (S.covariant i j)).sub
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hs i j)).smul
      (Lp.aestronglyMeasurable (S.source i))))

theorem shifted_phasedHardDerivative (w : ℕ → Q × X → ℂ)
    (s : ℕ → J → Q × X → ℝ) (i : ℕ) (j : J) (qx : Q × X) :
    S.phasedHardDerivative w s i j qx + (s i j qx : ℂ) • S.phasedSource w i qx =
      w i qx • S.covariant i j qx := by
  simp only [phasedHardDerivative, phasedSource, smul_sub, smul_smul]
  rw [mul_comm (s i j qx : ℂ)]
  abel

theorem phased_mass (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1)
    (i : ℕ) (qx : Q × X) : ‖S.phasedSource w i qx‖ ^ 2 = ‖S.source i qx‖ ^ 2 := by
  simp only [phasedSource, norm_smul, hw, one_mul]

theorem phased_kinetic (w : ℕ → Q × X → ℂ)
    (s : ℕ → J → Q × X → ℝ) (hw : ∀ i qx, ‖w i qx‖ = 1)
    (i : ℕ) (qx : Q × X) :
    localShiftedKinetic (fun j => S.phasedHardDerivative w s i j qx)
      (S.phasedSource w i qx) (fun j => s i j qx) =
        (1 / 2 : ℝ) * ∑ j, ‖S.covariant i j qx‖ ^ 2 := by
  simp only [localShiftedKinetic, S.shifted_phasedHardDerivative, norm_smul, hw, one_mul]

theorem phased_rest_norm (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1)
    (i : ℕ) (qx : Q × X) : ‖S.phasedRest w i qx‖ ^ 2 = ‖S.rest i qx‖ ^ 2 := by
  simp only [phasedRest, norm_smul, hw, one_mul]

theorem lp_quadratic_integrable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (v : Lp K 2 (μ.prod ν)) : Integrable (fun qx => ‖v qx‖ ^ 2) (μ.prod ν) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)

theorem lp_quadratic_integral {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (v : Lp K 2 (μ.prod ν)) : (∫ q, ∫ x, ‖v (q, x)‖ ^ 2 ∂ν ∂μ) = ‖v‖ ^ 2 := by
  rw [← integral_prod _ (lp_quadratic_integrable v)]
  simpa only [Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp v)).symm

theorem phased_mass_integrable (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1)
    (i : ℕ) : Integrable (fun qx => ‖S.phasedSource w i qx‖ ^ 2) (μ.prod ν) := by
  simpa only [S.phased_mass w hw] using lp_quadratic_integrable (S.source i)

theorem phased_rest_integrable (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1)
    (i : ℕ) : Integrable (fun qx => ‖S.phasedRest w i qx‖ ^ 2) (μ.prod ν) := by
  simpa only [S.phased_rest_norm w hw] using lp_quadratic_integrable (S.rest i)

theorem phased_kinetic_integrable (w : ℕ → Q × X → ℂ)
    (s : ℕ → J → Q × X → ℝ) (hw : ∀ i qx, ‖w i qx‖ = 1) (i : ℕ) :
    Integrable (fun qx => localShiftedKinetic (fun j => S.phasedHardDerivative w s i j qx)
      (S.phasedSource w i qx) (fun j => s i j qx)) (μ.prod ν) := by
  simp only [S.phased_kinetic w s hw]
  exact (integrable_finsetSum Finset.univ
    (fun j _ => lp_quadratic_integrable (S.covariant i j))).const_mul (1 / 2 : ℝ)

theorem phased_normalized (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1) :
    HasSum (fun i => ∫ q, sourceMass (ν := ν) (S.phasedSource w i) q ∂μ) 1 := by
  simpa only [sourceMass, S.phased_mass w hw, lp_quadratic_integral] using S.normalized

/-- The source-energy premise of the channel is a conclusion for the
actual product-space source vectors and the constructed phased derivative. -/
theorem phased_source_energy (w : ℕ → Q × X → ℂ)
    (s : ℕ → J → Q × X → ℝ) (hw : ∀ i qx, ‖w i qx‖ = 1) (i : ℕ) :
    (∫ q, sourceKinetic (ν := ν) (S.phasedHardDerivative w s i) (S.phasedSource w i) (s i) q +
      sourceRest (ν := ν) (S.phasedRest w i) q ∂μ) = S.input i - S.soft i := by
  have hk := S.phased_kinetic_integrable w s hw i
  have hr := S.phased_rest_integrable w hw i
  simp only [sourceKinetic, sourceRest]
  rw [integral_add hk.integral_prod_left hr.integral_prod_left]
  simp only [sourceKinetic, sourceRest, S.phased_kinetic w s hw, S.phased_rest_norm w hw]
  have hi := (integrable_finsetSum Finset.univ
    (fun j _ => lp_quadratic_integrable (S.covariant i j))).const_mul (1 / 2 : ℝ)
  rw [← integral_prod _ hi, integral_const_mul,
    integral_finsetSum _ (fun j _ => lp_quadratic_integrable (S.covariant i j))]
  have hn (j : J) : (∫ qx, ‖S.covariant i j qx‖ ^ 2 ∂μ.prod ν) = ‖S.covariant i j‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp (S.covariant i j))).symm
  simp only [hn, lp_quadratic_integral, input]
  ring

end ConditionedSource

section Channel

open RemovalState

variable {V T : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [IsProbabilityMeasure μ] [IsSeparable ν] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Assemble the analytic channel directly from L² source vectors. The
source mass, source energy and their integrability are no longer fields
to be supplied to the channel constructor. -/
def ConditionedSource.channelData
    (S : ConditionedSource μ ν J H F)
    (basis : HilbertBasis ℕ ℂ V) (R : Gaussian.RankOneData (Lp H 2 ν) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr) (C CZ e k L a b : ℝ)
    (z : ℕ → Q × X → V) (dz : ℕ → J → Q × X → V)
    (w : ℕ → Q × X → ℂ) (s : ℕ → J → Q × X → ℝ)
    (hz : ∀ i, StronglyMeasurable (z i))
    (hdz : ∀ i j, AEStronglyMeasurable (dz i j) (μ.prod ν))
    (hw : ∀ i, StronglyMeasurable (w i)) (hwnorm : ∀ i qx, ‖w i qx‖ = 1)
    (hs : ∀ i j, AEStronglyMeasurable (s i j) (μ.prod ν))
    (hunit : ∀ i, ∀ᵐ qx ∂μ.prod ν, ‖z i qx‖ = 1)
    (hconnection : ∀ i j, ∀ᵐ qx ∂μ.prod ν,
      inner ℂ (z i qx) (dz i j qx) = Complex.I * s i j qx)
    (Z : ℕ → Q → ℝ) (hZ : ∀ i q, 0 ≤ Z i q)
    (hZm : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hmetric : ∀ i, ∀ᵐ qx ∂μ.prod ν, ∑ j, ‖dz i j qx‖ ^ 2 ≤
      2 * C * (e ^ 2 * L ^ 2 * Z i qx.1 ^ 2 + e * Z i qx.1))
    (hsecond : ∀ i, Integrable
      (fun q => sourceMass (ν := ν) (S.source i) q * Z i q ^ 2) μ)
    (hsecond_bound : ∀ i, (∫ q, sourceMass (ν := ν) (S.source i) q * Z i q ^ 2 ∂μ) ≤
      CZ * k ^ 2 * (a ^ 2 * S.soft i + b ^ 2 * ‖S.source i‖ ^ 2))
    (hform : ∀ i j, ∀ᵐ q ∂μ,
      E.expectation (R.rankOne (channelSection (ν := ν) basis (z i) (S.phasedSource w i) j q)) =
        ENNReal.ofReal ((∫ x, 1 / 2 * ∑ l,
          ‖channelDerivative basis (fun y => z i (q, y)) (fun y => dz i l (q, y))
            (fun y => S.phasedHardDerivative w s i l (q, y))
            (fun y => S.phasedSource w i (q, y)) j x‖ ^ 2 ∂ν) +
          (∫ x, ‖coordinate basis (z i (q, x)) j • S.phasedRest w i (q, x)‖ ^ 2 ∂ν)))
    (hpositive : R.positive ⊆ Tr.positive) (htrace : R.trace = Tr.trace) :
    ChannelData (J := J) (F := F) basis R Tr E μ C CZ e k L a b where
  z := z
  dz := dz
  u := S.phasedHardDerivative w s
  ψ := S.phasedSource w
  s := s
  rest := S.phasedRest w
  z_measurable := hz
  ψ_measurable := S.phasedSource_stronglyMeasurable w hw
  dz_measurable := hdz
  u_measurable := S.phasedHardDerivative_measurable w s hw hs
  s_measurable := hs
  rest_measurable i := (hw i).aestronglyMeasurable.smul (Lp.aestronglyMeasurable (S.rest i))
  unit := hunit
  connection := hconnection
  source_integrable := S.phased_kinetic_integrable w s hwnorm
  mass_integrable := S.phased_mass_integrable w hwnorm
  rest_integrable := S.phased_rest_integrable w hwnorm
  normalized := S.phased_normalized w hwnorm
  input := S.input
  soft := S.soft
  soft_nonneg := S.soft_nonneg
  input_summable := S.input_summable
  soft_summable := S.soft_summable
  source_energy := S.phased_source_energy w s hwnorm
  fieldSize := Z
  field_nonneg := hZ
  field_measurable := hZm
  metric := hmetric
  second_integrable i := by simpa only [sourceMass, S.phased_mass w hwnorm] using hsecond i
  second_bound i := by
    simpa only [sourceMass, S.phased_mass w hwnorm, ConditionedSource.lp_quadratic_integral]
      using hsecond_bound i
  rankOne_form := hform
  positive_compatible := hpositive
  trace_compatible := htrace

end Channel
end GptLean.RemovalEnergy
