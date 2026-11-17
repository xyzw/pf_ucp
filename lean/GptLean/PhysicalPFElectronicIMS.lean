import GptLean.PhysicalPFScalarMultiplier
import GptLean.PhysicalPFDomain
import GptLean.PhotonLocalizationEstimatesAssembly

/-! The spatial source for electronic IMS is derived from the actual PF
reference coordinates and their proved scalar product rules. -/

noncomputable section

namespace GptLean.PhysicalPFElectronicIMS

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms ElectronicH1Multiplier PhotonLocalization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem square_integrable {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} (u : Lp H 2 μ) :
    Integrable (fun x => ‖u x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)

private theorem square_integral {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X} (u : Lp H 2 μ) :
    (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  simpa only [Lp.toLp_coeFn] using (Repair.toL2_norm_sq (Lp.memLp u)).symm

private def density {X H J : Type*} [MeasurableSpace X] [Fintype J]
    [NormedAddCommGroup H] {μ : Measure X}
    (d : J → Lp H 2 μ) (r p : Lp H 2 μ) (x : X) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + (‖r x‖ ^ 2 + ‖p x‖ ^ 2)

private theorem density_integrable {X H J : Type*} [MeasurableSpace X] [Fintype J]
    [NormedAddCommGroup H] {μ : Measure X} (d : J → Lp H 2 μ) (r p : Lp H 2 μ) :
    Integrable (density d r p) μ :=
  ((integrable_finsetSum _ (fun i _ => square_integrable (d i))).const_mul (1 / 2)).add
    ((square_integrable r).add (square_integrable p))

private theorem density_integral {X H J : Type*} [MeasurableSpace X] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X} (d : J → Lp H 2 μ) (r p : Lp H 2 μ) :
    (∫ x, density d r p x ∂μ) = (1 / 2 : ℝ) * ∑ i, ‖d i‖ ^ 2 + ‖r‖ ^ 2 + ‖p‖ ^ 2 := by
  have hs : Integrable (fun x => ∑ i, ‖d i x‖ ^ 2) μ := by
    simpa only [Finset.sum_apply] using
      (integrable_finsetSum Finset.univ (fun i _ => square_integrable (d i)))
  have hrp : Integrable (fun x => ‖r x‖ ^ 2 + ‖p x‖ ^ 2) μ :=
    (square_integrable r).add (square_integrable p)
  change (∫ x, (1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + (‖r x‖ ^ 2 + ‖p x‖ ^ 2) ∂μ) = _
  rw [integral_add (hs.const_mul (1 / 2)) hrp,
    integral_const_mul, integral_finsetSum Finset.univ (fun i _ => square_integrable (d i)),
    integral_add (square_integrable r) (square_integrable p)]
  simp only [square_integral]
  ring

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def scalarDensity (u : Reference I V) (x : Position I) : ℝ :=
  ‖radiation I V u x‖ ^ 2 + ‖potential I V u x‖ ^ 2

theorem original_integrable (u : Reference I V) :
    Integrable (fun x => (1 / 2 : ℝ) * ∑ i, ‖covariant I V C κ hκ M hbound e i u x‖ ^ 2 +
      scalarDensity V u x) volume := density_integrable _ _ _

theorem original_form (u : Reference I V) :
    ((normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u))).toReal =
    ∫ x, (1 / 2 : ℝ) * ∑ i, ‖covariant I V C κ hκ M hbound e i u x‖ ^ 2 +
      scalarDensity V u x := by
  have h := congrArg ENNReal.toReal (normalEnergy_rankOne I V C κ hκ M hbound B S e u)
  exact h.trans ((ENNReal.toReal_ofReal (energy_nonneg I V C κ hκ M hbound e u)).trans
    (density_integral (fun i => covariant I V C κ hκ M hbound e i u)
      (radiation I V u) (potential I V u)).symm)

private theorem scalar_product_rule {H : Type*} [AddCommGroup H] [Module ℂ H]
    [Module ℝ H] [IsScalarTower ℝ ℂ H] (a b : ℝ) (d w : H) :
    a • d + (-Complex.I) • (b • w) = (a : ℂ) • d - Complex.I • (b : ℂ) • w := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), neg_smul, sub_eq_add_neg]
  rfl

private theorem product_derivative_ae (a : DifferentiableMultiplier I)
    (i : I) (w d z : WaveSpace I)
    (hz : z = a.multiplier d + (-Complex.I) • a.derivativeMultiplier i w) :
    z =ᵐ[volume] fun x => (a.weight x : ℂ) • d x -
      Complex.I • (a.gradient i x : ℂ) • w x := by
  have he := Filter.EventuallyEq.of_eq (l := ae volume) (congrArg (fun q : WaveSpace I => ⇑q) hz)
  filter_upwards [he, Lp.coeFn_add (a.multiplier d) ((-Complex.I) • a.derivativeMultiplier i w),
    Lp.coeFn_smul (-Complex.I) (a.derivativeMultiplier i w),
    realL2Multiplier_apply a.weight a.differentiable.continuous.aestronglyMeasurable
      a.bound (ae_of_all _ a.bounded) d,
    realL2Multiplier_apply (a.gradient i) (a.gradient_measurable i).aestronglyMeasurable
      a.derivativeBound (ae_of_all _ (a.derivative_bounded i)) w]
    with x hx ha hs hd hw
  exact (hx.trans (ha.trans (congrArg₂ (fun p q : PhotonFock => p + q) hd
    (hs.trans (congrArg (fun p : PhotonFock => (-Complex.I) • p) hw))))).trans
      (scalar_product_rule (a.weight x) (a.gradient i x) (d x) (w x))

private theorem multiply_ae (a : DifferentiableMultiplier I) (u : WaveSpace I) :
    a.multiplier u =ᵐ[volume] fun x => a.weight x • u x :=
  realL2Multiplier_apply a.weight a.differentiable.continuous.aestronglyMeasurable
    a.bound (ae_of_all _ a.bounded) u

theorem branch_density (a : DifferentiableMultiplier I) (u : Reference I V) :
    density (fun i => covariant I V C κ hκ M hbound e i (PhysicalPFScalarMultiplier.multiply V a u))
      (radiation I V (PhysicalPFScalarMultiplier.multiply V a u))
      (potential I V (PhysicalPFScalarMultiplier.multiply V a u)) =ᵐ[volume]
    fun x => (1 / 2 : ℝ) * ∑ i,
      ‖(a.weight x : ℂ) • covariant I V C κ hκ M hbound e i u x -
        Complex.I • (a.gradient i x : ℂ) • inclusion I V u x‖ ^ 2 +
      a.weight x ^ 2 * scalarDensity V u x := by
  have hd := ae_all_iff.mpr (fun i => product_derivative_ae a i _ _ _
    (PhysicalPFScalarMultiplier.covariant_multiply V a C κ hκ M hbound e u i))
  have hr := Filter.EventuallyEq.of_eq (l := ae volume) (congrArg (fun q : WaveSpace I => ⇑q)
    (PhysicalPFScalarMultiplier.radiation_multiply V a u))
  have hp := Filter.EventuallyEq.of_eq (l := ae volume) (congrArg (fun q : WaveSpace I => ⇑q)
    (PhysicalPFScalarMultiplier.potential_multiply V a u))
  filter_upwards [hd, hr, hp, multiply_ae a (radiation I V u), multiply_ae a (potential I V u)]
    with x hx hrx hpx hra hpa
  simp only [density, hx, hrx, hpx, hra, hpa, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, scalarDensity]
  ring

theorem branch_integrable (a : DifferentiableMultiplier I) (u : Reference I V) :
    Integrable (fun x => (1 / 2 : ℝ) * ∑ i,
      ‖(a.weight x : ℂ) • covariant I V C κ hκ M hbound e i u x -
        Complex.I • (a.gradient i x : ℂ) • inclusion I V u x‖ ^ 2 +
      a.weight x ^ 2 * scalarDensity V u x) volume :=
  (density_integrable _ _ _).congr (branch_density V C κ hκ M hbound e a u)

theorem branch_finite (a : DifferentiableMultiplier I) (u : Reference I V) :
    (normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (a.multiplier (inclusion I V u))) < ⊤ := by
  have h := normalEnergy_rankOne I V C κ hκ M hbound B S e (PhysicalPFScalarMultiplier.multiply V a u)
  have hv := PhysicalPFScalarMultiplier.value_multiply V a u
  exact (congrArg (fun w : WaveSpace I => (normalEnergy I V C κ hκ M hbound B S e).expectation
    ((B.realization (WaveSpace I)).rank.rankOne w)) hv).symm.trans h |>.trans_lt ENNReal.ofReal_lt_top

theorem branch_form (a : DifferentiableMultiplier I) (u : Reference I V) :
    ((normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (a.multiplier (inclusion I V u)))).toReal =
    ∫ x, (1 / 2 : ℝ) * ∑ i,
      ‖(a.weight x : ℂ) • covariant I V C κ hκ M hbound e i u x -
        Complex.I • (a.gradient i x : ℂ) • inclusion I V u x‖ ^ 2 +
      a.weight x ^ 2 * scalarDensity V u x := by
  have hv := PhysicalPFScalarMultiplier.value_multiply V a u
  exact (congrArg (fun w : WaveSpace I => ((normalEnergy I V C κ hκ M hbound B S e).expectation
    ((B.realization (WaveSpace I)).rank.rankOne w)).toReal) hv).symm.trans
      ((original_form V C κ hκ M hbound B S e (PhysicalPFScalarMultiplier.multiply V a u)).trans
        (integral_congr_ae (branch_density V C κ hκ M hbound e a u)))

def source {A : Type*} [Fintype A] (a : A → DifferentiableMultiplier I) (u : Reference I V) :
    ElectronicIMSSource (A := (B.realization (WaveSpace I)).rank) (K := PhotonFock)
      (normalEnergy I V C κ hκ M hbound B S e) volume (fun b => (a b).weight)
      (fun i => EuclideanSpace.single i 1) (fun b => (a b).multiplier) (inclusion I V u) where
  derivative i := covariant I V C κ hκ M hbound e i u
  wave := inclusion I V u
  scalar := scalarDensity V u
  branch_integrable b := branch_integrable V C κ hκ M hbound e (a b) u
  source_integrable := original_integrable V C κ hκ M hbound e u
  mass_integrable := square_integrable _
  mass_eq := square_integral _
  original_form := original_form V C κ hκ M hbound B S e u
  branch_finite b := branch_finite V C κ hκ M hbound B S e (a b) u
  branch_form b := branch_form V C κ hκ M hbound B S e (a b) u

end GptLean.PhysicalPFElectronicIMS
