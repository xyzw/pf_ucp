import GptLean.RemovalSourceIndex
import GptLean.RemovalSourceConditionedEnergy
import GptLean.RemovalSourceSupport
import GptLean.RemovalClusterPhase

/-!
The actual symmetric lattice partition on physical configuration space,
enumerated by natural numbers with zero padding. Its source, derivatives,
IMS constants and supporting lattice centres are all fixed by the original
one-particle partition. Empty particle configurations need no exception.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory Filter ElectronicLocalization SymmetricLift

variable {N : ℕ}

def configurationParticles : Configuration N →L[ℝ] (Fin N → LatticePartition.Position) :=
  ContinuousLinearMap.pi (fun i => (particleLinear i).toContinuousLinearMap)

theorem configurationParticles_single (j : Fin N × Fin 3) :
    configurationParticles (EuclideanSpace.single j 1) =
      Pi.single j.1 (EuclideanSpace.single j.2 1) := by
  classical
  funext i
  change particle (EuclideanSpace.single j 1) i = _
  by_cases hi : i = j.1
  · subst i
    simpa only [Pi.single_eq_same] using particle_single_same j.1 j.2
  · simp [Pi.single_eq_of_ne hi, particle_single_ne j.1 j.2 hi]

def latticeLabelMultiplier (R : ℝ) (α : Fin N → LatticePartition.Lattice)
    (x : Configuration N) : ℝ :=
  symmetricMultiplier (LatticePartition.multiplier R) α (configurationParticles x)

theorem latticeLabelMultiplier_nonneg (R : ℝ) (α : Fin N → LatticePartition.Lattice)
    (x : Configuration N) : 0 ≤ latticeLabelMultiplier R α x :=
  symmetricMultiplier_nonneg _ _ _

theorem latticeLabelMultiplier_differentiable (R : ℝ) (α : Fin N → LatticePartition.Lattice) :
    Differentiable ℝ (latticeLabelMultiplier R α) :=
  (symmetricMultiplier_differentiable _ (LatticePartition.multiplier_differentiable R)
    (LatticePartition.multiplier_nonneg R) α).comp configurationParticles.differentiable

theorem latticeLabelMultiplier_partition (R : ℝ) (x : Configuration N) :
    HasSum (fun α : Fin N → LatticePartition.Lattice => latticeLabelMultiplier R α x ^ 2) 1 :=
  symmetricMultiplier_hasSum_sq _ (LatticePartition.multiplier_locallyFinite R)
    (LatticePartition.multiplier_hasSum_sq R) _

theorem latticeLabelMultiplier_locallyFinite (R : ℝ) :
    LocallyFinite (fun α : Fin N → LatticePartition.Lattice =>
      Function.support (latticeLabelMultiplier R α)) :=
  (symmetricMultiplier_locallyFinite _ (LatticePartition.multiplier_locallyFinite R)).preimage_continuous
    configurationParticles.continuous

theorem latticeLabelMultiplier_fderiv (R : ℝ) (α : Fin N → LatticePartition.Lattice)
    (x : Configuration N) (j : Fin N × Fin 3) :
    fderiv ℝ (latticeLabelMultiplier R α) x (EuclideanSpace.single j 1) =
      fderiv ℝ (symmetricMultiplier (LatticePartition.multiplier R) α)
        (configurationParticles x) (Pi.single j.1 (EuclideanSpace.single j.2 1)) := by
  have h := ((symmetricMultiplier_differentiable _
    (LatticePartition.multiplier_differentiable R)
    (LatticePartition.multiplier_nonneg R) α) (configurationParticles x)).hasFDerivAt.comp x
      configurationParticles.hasFDerivAt
  change fderiv ℝ (symmetricMultiplier (LatticePartition.multiplier R) α ∘
    configurationParticles) x (EuclideanSpace.single j 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, configurationParticles_single]

def latticeIndex (N : ℕ) : (Fin N → LatticePartition.Lattice) ↪ ℕ :=
  countableIndex _

def latticeMultiplier (R : ℝ) : ℕ → Configuration N → ℝ :=
  zeroPad (latticeIndex N) (latticeLabelMultiplier R)

theorem latticeMultiplier_nonneg (R : ℝ) (n : ℕ) (x : Configuration N) :
    0 ≤ latticeMultiplier R n x :=
  zeroPad_nonneg _ _ (latticeLabelMultiplier_nonneg R) n x

theorem latticeMultiplier_partition (R : ℝ) (x : Configuration N) :
    HasSum (fun n => latticeMultiplier R n x ^ 2) 1 :=
  zeroPad_partition _ _ (latticeLabelMultiplier_partition R) x

theorem latticeMultiplier_locallyFinite (R : ℝ) :
    LocallyFinite (fun n => Function.support (latticeMultiplier (N := N) R n)) :=
  zeroPad_locallyFinite _ _ (latticeLabelMultiplier_locallyFinite R)

theorem latticeMultiplier_differentiable (R : ℝ) (n : ℕ) :
    Differentiable ℝ (latticeMultiplier (N := N) R n) :=
  zeroPad_differentiable _ _ (latticeLabelMultiplier_differentiable R) n

theorem latticeMultiplier_measurable (R : ℝ) (n : ℕ) :
    AEStronglyMeasurable (latticeMultiplier (N := N) R n) volume :=
  (latticeMultiplier_differentiable R n).continuous.aestronglyMeasurable

theorem latticeMultiplier_derivative_measurable (R : ℝ) (n : ℕ) (j : Fin N × Fin 3) :
    AEStronglyMeasurable (fun x =>
      fderiv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1)) volume := by
  have he : (fun x => lineDeriv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1)) =
      (fun x => fderiv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1)) := by
    funext x
    exact ((latticeMultiplier_differentiable R n) x).hasFDerivAt.hasLineDerivAt _ |>.lineDeriv
  rw [← he]
  exact aestronglyMeasurable_lineDeriv (latticeMultiplier_differentiable R n).continuous volume

theorem latticeMultiplier_coordinate_metric (R : ℝ) (hR : 0 < R)
    (j : Fin N × Fin 3) (x : Configuration N) :
    (∑' n, fderiv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1) ^ 2) ≤
      LatticePartition.metricConstant / R ^ 2 := by
  rw [latticeMultiplier, zeroPad_metric]
  simp_rw [latticeLabelMultiplier_fderiv]
  apply (symmetricMultiplier_single_metric_le _
    (LatticePartition.multiplier_locallyFinite R) (LatticePartition.multiplier_differentiable R)
    (LatticePartition.multiplier_nonneg R) (LatticePartition.multiplier_hasSum_sq R)
    (configurationParticles x) j.1 (EuclideanSpace.single j.2 1)).trans
  exact (Finset.single_le_sum (fun k _ => tsum_nonneg (fun a => sq_nonneg
    (fderiv ℝ (LatticePartition.multiplier R a) (configurationParticles x j.1)
      (EuclideanSpace.single k 1)))) (Finset.mem_univ j.2)).trans
        (LatticePartition.multiplier_metric_le R hR (configurationParticles x j.1))

theorem latticeMultiplier_total_metric (R : ℝ) (hR : 0 < R) (x : Configuration N) :
    (∑ j : Fin N × Fin 3, ∑' n,
      fderiv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1) ^ 2) ≤
      N * LatticePartition.metricConstant / R ^ 2 := by
  simp_rw [latticeMultiplier, zeroPad_metric, latticeLabelMultiplier_fderiv]
  rw [Fintype.sum_prod_type]
  simpa only [mul_div_assoc] using LatticePartition.symmetric_metric_le R hR (configurationParticles x)

/-- A definite lattice label for every natural index. Off the embedding's
range the multiplier is zero and this harmless fallback is never used on
its support. The function exists also for an empty particle type. -/
def latticeLabel (N n : ℕ) : Fin N → LatticePartition.Lattice := by
  classical
  exact if h : ∃ α, latticeIndex N α = n then Classical.choose h else fun _ => 0

theorem latticeLabel_index (α : Fin N → LatticePartition.Lattice) :
    latticeLabel N (latticeIndex N α) = α := by
  unfold latticeLabel
  rw [dite_eq_left ⟨α, rfl⟩]
  exact (latticeIndex N).injective (Classical.choose_spec (show ∃ β, latticeIndex N β = latticeIndex N α from ⟨α, rfl⟩))

def latticeCentre (R : ℝ) (n : ℕ) : Fin N → LatticePartition.Position :=
  fun i => LatticePartition.centre R (latticeLabel N n i)

def sourceLatticeCentre (R : ℝ) (i : ℕ) : Fin N → LatticePartition.Position :=
  latticeCentre R (Nat.unpair i).2

theorem latticeMultiplier_tsupport_near_centre (R : ℝ) (hR : 0 < R)
    (n : ℕ) (x : Configuration N) (hx : x ∈ tsupport (latticeMultiplier R n))
    (j : Fin N) : ∃ i : Fin N, dist (particle x j) (latticeCentre R n i) ≤ 4 * R := by
  classical
  by_cases hn : ∃ α, latticeIndex N α = n
  · rcases hn with ⟨α, rfl⟩
    have hxe : x ∈ tsupport (latticeLabelMultiplier R α) := by
      simpa only [latticeMultiplier, zeroPad_apply] using hx
    simpa only [latticeCentre, latticeLabel_index] using
      RemovalGeometry.symmetricLocalization_tsupport_near_centre α hR x hxe j
  · have hz : latticeMultiplier (N := N) R n = 0 := zeroPad_off_range _ _ hn
    simp only [hz, tsupport_zero, Set.mem_empty_iff_false] at hx

section Source

variable {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

/-- The source constructor now has no localization, IMS or source-series
hypotheses. Its only series inputs are the original spectral energies. -/
def latticeConditionedSource
    (U : Lp H 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ] Lp K 2 (μ.prod (volume : Measure (Configuration N))))
    (Ur : Lp Hr 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ] Lp Kr 2 (μ.prod (volume : Measure (Configuration N))))
    (R : ℝ) (hR : 0 < R)
    (ψ : ℕ → Lp H 2 (volume : Measure (Configuration N)))
    (dψ : ℕ → (Fin N × Fin 3) → Lp H 2 (volume : Measure (Configuration N)))
    (rest : ℕ → Lp Hr 2 (volume : Measure (Configuration N)))
    (soft : ℕ → Lp Hs 2 (volume : Measure (Configuration N)))
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1)
    (hkinetic : ∀ j, Summable (fun n => ‖dψ n j‖ ^ 2))
    (hrest : Summable (fun n => ‖rest n‖ ^ 2))
    (hsoft : Summable (fun n => ‖soft n‖ ^ 2)) :
    RemovalEnergy.ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) K Kr :=
  localizedConditionedSource U Ur (latticeMultiplier R) (latticeMultiplier_locallyFinite R)
    (latticeMultiplier_differentiable R) (latticeMultiplier_nonneg R)
    (latticeMultiplier_partition R) (latticeMultiplier_measurable R)
    ψ dψ rest soft (fun j => EuclideanSpace.single j 1)
    (latticeMultiplier_derivative_measurable R) (fun _ => LatticePartition.metricConstant / R ^ 2)
    (latticeMultiplier_coordinate_metric R hR) hmass hkinetic hrest hsoft

theorem localizedLatticeFiber_support
    (U : Lp H 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ] Lp K 2 (μ.prod (volume : Measure (Configuration N))))
    (R : ℝ) (hR : 0 < R)
    (hcommute : ∀ (u : Lp H 2 (volume : Measure (Configuration N))) n,
      U (localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) u n) =
      productLocalizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (U u) n)
    (ψ : ℕ → Lp H 2 (volume : Measure (Configuration N))) (n : ℕ) :
    ∀ᵐ qx ∂μ.prod volume,
      localizedFiber U (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) ψ n qx ≠ 0 →
      ∀ j : Fin N, ∃ i : Fin N, dist (particle qx.2 j) (sourceLatticeCentre R n i) ≤ 4 * R := by
  filter_upwards [localizedFiber_product_support U (latticeMultiplier R)
    (latticeMultiplier_partition R) (latticeMultiplier_measurable R) hcommute ψ n] with qx hqx
  intro hn j
  have hx : qx.2 ∈ tsupport (latticeMultiplier R (Nat.unpair n).2) := by
    by_contra hx
    exact hn (hqx hx)
  exact latticeMultiplier_tsupport_near_centre R hR _ _ hx j

/-- Original spectral data and the ordinary WIS unitaries. All localized
series are constructed by `conditioned`. -/
structure LatticeSourceData (N : ℕ) (μ : Measure Q) (H K Hr Kr Hs : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
    [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] where
  U : Lp H 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ] Lp K 2 (μ.prod (volume : Measure (Configuration N)))
  Ur : Lp Hr 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ] Lp Kr 2 (μ.prod (volume : Measure (Configuration N)))
  ψ : ℕ → Lp H 2 (volume : Measure (Configuration N))
  dψ : ℕ → (Fin N × Fin 3) → Lp H 2 (volume : Measure (Configuration N))
  rest : ℕ → Lp Hr 2 (volume : Measure (Configuration N))
  soft : ℕ → Lp Hs 2 (volume : Measure (Configuration N))
  mass : HasSum (fun n => ‖ψ n‖ ^ 2) 1
  kinetic_summable : ∀ j, Summable (fun n => ‖dψ n j‖ ^ 2)
  rest_summable : Summable (fun n => ‖rest n‖ ^ 2)
  soft_summable : Summable (fun n => ‖soft n‖ ^ 2)

def latticeIMSConstant (N : ℕ) : ℝ :=
  (3 * (N : ℝ) / 2) * LatticePartition.metricConstant

namespace LatticeSourceData

variable (D : LatticeSourceData N μ H K Hr Kr Hs)

def conditioned (R : ℝ) (hR : 0 < R) :
    RemovalEnergy.ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) K Kr :=
  latticeConditionedSource D.U D.Ur R hR D.ψ D.dψ D.rest D.soft D.mass
    D.kinetic_summable D.rest_summable D.soft_summable

def inputEnergy : ℝ :=
  ((1 / 2 : ℝ) * ∑ j, ∑' n, ‖D.dψ n j‖ ^ 2) +
    (∑' n, ‖D.rest n‖ ^ 2) + ∑' n, ‖D.soft n‖ ^ 2

theorem source_eq_U_localized (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (D.conditioned R hR).source n =
      D.U (localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (D.ψ (Nat.unpair n).1) (Nat.unpair n).2) := rfl

theorem rest_eq_Ur_localized (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (D.conditioned R hR).rest n =
      D.Ur (localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (D.rest (Nat.unpair n).1) (Nat.unpair n).2) := rfl

theorem source_eq_mul (R : ℝ) (hR : 0 < R)
    (hcommute : ∀ (u : Lp H 2 (volume : Measure (Configuration N))) n,
      D.U (localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) u n) =
      productLocalizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (D.U u) n) (n : ℕ) :
    ((D.conditioned R hR).source n : Q × Configuration N → K) =ᵐ[μ.prod volume]
      (fun qx => (latticeMultiplier R (Nat.unpair n).2 qx.2 : ℂ) • D.U (D.ψ (Nat.unpair n).1) qx) :=
  localizedFiber_product_eq_mul D.U (latticeMultiplier R) (latticeMultiplier_partition R)
    (latticeMultiplier_measurable R) hcommute D.ψ n

theorem rest_eq_mul (R : ℝ) (hR : 0 < R)
    (hcommute : ∀ (u : Lp Hr 2 (volume : Measure (Configuration N))) n,
      D.Ur (localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) u n) =
      productLocalizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (D.Ur u) n) (n : ℕ) :
    ((D.conditioned R hR).rest n : Q × Configuration N → Kr) =ᵐ[μ.prod volume]
      (fun qx => (latticeMultiplier R (Nat.unpair n).2 qx.2 : ℂ) • D.Ur (D.rest (Nat.unpair n).1) qx) :=
  localizedFiber_product_eq_mul D.Ur (latticeMultiplier R) (latticeMultiplier_partition R)
    (latticeMultiplier_measurable R) hcommute D.rest n

theorem soft_total (R : ℝ) (hR : 0 < R) :
    (∑' n, (D.conditioned R hR).soft n) = ∑' n, ‖D.soft n‖ ^ 2 :=
  (localizedConditionedSource_soft_hasSum D.U D.Ur (latticeMultiplier R)
    (latticeMultiplier_locallyFinite R) (latticeMultiplier_differentiable R)
    (latticeMultiplier_nonneg R) (latticeMultiplier_partition R) (latticeMultiplier_measurable R)
    D.ψ D.dψ D.rest D.soft (fun j => EuclideanSpace.single j 1)
    (latticeMultiplier_derivative_measurable R)
    (fun _ => LatticePartition.metricConstant / R ^ 2)
    (latticeMultiplier_coordinate_metric R hR) D.mass D.kinetic_summable
    D.rest_summable D.soft_summable D.soft_summable.hasSum).tsum_eq

theorem input_total_le (R : ℝ) (hR : 0 < R) :
    (∑' n, (D.conditioned R hR).input n) ≤ D.inputEnergy + latticeIMSConstant N / R ^ 2 := by
  have h := localizedConditionedSource_input_bound D.U D.Ur (latticeMultiplier R)
    (latticeMultiplier_locallyFinite R) (latticeMultiplier_differentiable R)
    (latticeMultiplier_nonneg R) (latticeMultiplier_partition R) (latticeMultiplier_measurable R)
    D.ψ D.dψ D.rest D.soft (fun j => EuclideanSpace.single j 1)
    (latticeMultiplier_derivative_measurable R)
    (fun _ => LatticePartition.metricConstant / R ^ 2)
    (latticeMultiplier_coordinate_metric R hR) D.mass D.kinetic_summable
    D.rest_summable D.soft_summable
  change (∑' n, (D.conditioned R hR).input n) ≤ D.inputEnergy + _ at h
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, latticeIMSConstant]
  ring

theorem source_support (R : ℝ) (hR : 0 < R)
    (hcommute : ∀ (u : Lp H 2 (volume : Measure (Configuration N))) n,
      D.U (localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) u n) =
      productLocalizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (D.U u) n) (n : ℕ) :
    ∀ᵐ qx ∂μ.prod volume, (D.conditioned R hR).source n qx ≠ 0 →
      ∀ j : Fin N, ∃ i : Fin N, dist (particle qx.2 j) (sourceLatticeCentre R n i) ≤ 4 * R :=
  localizedLatticeFiber_support D.U R hR hcommute D.ψ n

end LatticeSourceData

end Source
end GptLean.RemovalSource
