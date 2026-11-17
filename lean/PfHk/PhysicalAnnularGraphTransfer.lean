import PfHk.PhysicalOperatorDomain
import PfHk.PhysicalCoreSpatialIntegrability
import PfHk.CarlemanWeightedL2
import PfHk.AnnularSupportGeometry
import PfHk.PhysicalSupportedGraphLimits

/-! Passage from the proved free PF core inequality to every annularly
supported vector in the actual free operator graph. -/

noncomputable section
namespace PfHk.PhysicalAnnularGraphTransfer

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference PfHk.PhysicalPolarDensity
  PfHk.CarlemanSpatialDensity PfHk.PhysicalCarlemanInput
open scoped Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

local instance annularGraphPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.covariant
  PhysicalPFReference.radiation PhysicalPFReference.referenceSubspace SmoothCore.reference
  FreeGraph AnnularCoreApproximation.approximants AnnularCoreApproximation.sources

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (O : Configuration N)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

private theorem density_congr_at {I : Type*} [Fintype I] [DecidableEq I]
    (τ α : ℝ) (M D Q M' D' Q' : PfHk.PolarCalculus.Position I → ℝ)
    (X : PfHk.PolarCalculus.Position I) (hM : M X = M' X) (hD : D X = D' X)
    (hQ : Q X = Q' X) : density τ α M D Q X = density τ α M' D' Q' X := by
  unfold density
  rw [hM, hD, hQ]

def operatorDensity (τ α : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Configuration N → ℝ :=
  density τ α (fun X => ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2)
    (fun X => ∑ j, ‖covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e j u X‖ ^ 2)
    (fun X => ‖PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2)

theorem compactSource_supported {s : Set (Configuration N)}
    {f : WaveSpace (Fin N × Fin 3)} (g : CompactSource s f) :
    ∀ᵐ X ∂volume, X ∉ s → f X = 0 := by
  filter_upwards [g.agrees] with X hX hs
  exact hX.trans (image_eq_zero_of_notMem_tsupport (fun h => hs (g.support h)))

theorem core_density_ae {s : Set (Configuration N)} (a : SmoothCore s) (τ α : ℝ) :
    operatorDensity F χ O C e τ α a.reference =ᵐ[volume]
      density τ α (mass a.rootWave) (kinetic F χ e O C a.rootWave) (PhysicalPolarDensity.radiation a.rootWave) := by
  have hv : inclusion (Fin N × Fin 3) (fun _ => 0) a.reference =ᵐ[volume]
      PfHk.CenteredRadialGauge.coreValue a.rootWave := a.reference_value_ae
  filter_upwards [hv, Filter.eventually_all.mpr (core_reference_covariant_ae a F χ e O C),
    core_reference_radiation_ae a] with X hX hD hR
  exact density_congr_at τ α _ _ _ _ _ _ X
    (congrArg (fun q : PhotonFock => ‖q‖ ^ 2) hX)
    (Finset.sum_congr rfl fun j _ => congrArg (fun q : PhotonFock => ‖q‖ ^ 2) (hD j))
    (congrArg (fun q : PhotonFock => ‖q‖ ^ 2) hR)

/-- Fixed-annulus graph transfer for the actual physical form coordinates.
The only estimate premise is the separate core theorem to be transferred. -/
theorem global_estimate_of_core
    (hcore : AnnularCoreApproximation C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e)
    {τ α ρ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hρ : 0 < ρ) (hR : R < 1)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    {K s : Set (Configuration N)}
    (hu : FreeGraph C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e u f)
    (hK : IsCompact K) (hs : IsOpen s) (hKs : K ⊆ s) (hsA : s ⊆ annulus ρ R)
    (hsupp : ∀ᵐ X ∂volume, X ∉ K → inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0)
    (hest : ∀ a : SmoothCore s, ∀ g : WaveSpace (Fin N × Fin 3), CompactSource s g →
      FreeGraph C (profile F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e a.reference g →
      (∫ X, operatorDensity F χ O C e τ α a.reference X) ≤
        64 * ∫ X, source τ α (fun Y => ‖g Y‖ ^ 2) X) :
    (∫ X, operatorDensity F χ O C e τ α u X) ≤
      64 * ∫ X, source τ α (fun Y => ‖f Y‖ ^ 2) X := by
  let a := hcore.approximants C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e hu hK hs hKs hsupp
  let g := hcore.sources C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e hu hK hs hKs hsupp
  have hg := hcore.properties C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e hu hK hs hKs hsupp
  have hform := freeGraph_form_convergence C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e
    (u := fun n => (a n).reference) (v := u) (f := g) (g := f)
    hg.1 hu hg.2.2.1 hg.2.2.2
  exact CarlemanWeightedL2.estimate_limit (I := Fin N × Fin 3) (H := PhotonFock) hτ hα hρ hR 64
    (m := fun n => inclusion (Fin N × Fin 3) (fun _ => 0) (a n).reference)
    (r := fun n => PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) (a n).reference)
    (f := g)
    (D := fun n j => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e j (a n).reference)
    (m₀ := inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (r₀ := PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) u) (f₀ := f)
    (D₀ := fun j => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e j u)
    hg.2.2.1 hform.2 hg.2.2.2 hform.1
    (fun n => (a n).supported.mono fun X hX hnot => hX (fun h => hnot (hsA h)))
    (fun n => (core_radiation_supported (a n)).mono fun X hX hnot => hX (fun h => hnot (hsA h)))
    (fun n => (compactSource_supported (hg.2.1 n).some).mono fun X hX hnot => hX (fun h => hnot (hsA h)))
    (fun n j => (core_covariant_supported (a n) F χ e O C j).mono
      fun X hX hnot => hX (fun h => hnot (hsA h)))
    (fun n => hest (a n) (g n) (hg.2.1 n).some (hg.1 n))

/-- The full-domain global estimate needs only annular support of the
electronic vector. The approximation supplies support of all other coordinates. -/
theorem annular_global_estimate
    (hcore : AnnularCoreApproximation C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e)
    {τ α r₀ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hr₀ : r₀ < 1) (hR : R ≤ r₀)
    (hest : ∀ s : Set (Configuration N), IsOpen s → ∀ ρ R' : ℝ,
      0 < ρ → R' < r₀ → s ⊆ annulus ρ R' →
      ∀ a : SmoothCore s, ∀ g : WaveSpace (Fin N × Fin 3), CompactSource s g →
      FreeGraph C (profile F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e a.reference g →
      (∫ X, operatorDensity F χ O C e τ α a.reference X) ≤
        64 * ∫ X, source τ α (fun Y => ‖g Y‖ ^ 2) X)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    (hu : FreeGraph C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e u f)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) 0 R) :
    (∫ X, operatorDensity F χ O C e τ α u X) ≤
      64 * ∫ X, source τ α (fun Y => ‖f Y‖ ^ 2) X := by
  let ψ := inclusion (Fin N × Fin 3) (fun _ => 0) u
  let ρ := AnnularSupportGeometry.innerRadius ψ R hsupp
  let R' := AnnularSupportGeometry.outerRadius ψ R hsupp
  have hh := AnnularSupportGeometry.radii_spec ψ R hsupp
  have hR' : R' < R := hh.2.2.1
  apply global_estimate_of_core F χ O C e hcore hτ hα (half_pos hh.1)
    (show (R' + R) / 2 < 1 by linarith only [hR', hR, hr₀])
    hu (annulus_compact ρ R') (AnnularSupportGeometry.buffer_open ρ R' R)
    (AnnularSupportGeometry.annulus_subset_buffer hh.1 hh.2.2.1)
    (AnnularSupportGeometry.buffer_subset_annulus ρ R' R)
    (AnnularSupportGeometry.supported_annulus ψ R hsupp)
  exact hest _ (AnnularSupportGeometry.buffer_open ρ R' R) (ρ / 2) ((R' + R) / 2)
    (half_pos hh.1) (by linarith only [hR', hR])
    (AnnularSupportGeometry.buffer_subset_annulus ρ R' R)

theorem global_integrals_eq_ball
    (hcore : AnnularCoreApproximation C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)} {R : ℝ}
    (hu : FreeGraph C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e u f)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) 0 R) (τ α : ℝ) :
    (∫ X, operatorDensity F χ O C e τ α u X) =
      (∫ X in Metric.ball 0 R, operatorDensity F χ O C e τ α u X) ∧
    (∫ X, source τ α (fun Y => ‖f Y‖ ^ 2) X) =
      (∫ X in Metric.ball 0 R, source τ α (fun Y => ‖f Y‖ ^ 2) X) := by
  let ψ := inclusion (Fin N × Fin 3) (fun _ => 0) u
  let ρ := AnnularSupportGeometry.innerRadius ψ R hsupp
  let R' := AnnularSupportGeometry.outerRadius ψ R hsupp
  have hh := AnnularSupportGeometry.radii_spec ψ R hsupp
  have hKs := AnnularSupportGeometry.annulus_subset_buffer (I := Fin N × Fin 3) hh.1 hh.2.2.1
  have hsB := AnnularSupportGeometry.buffer_subset_ball (I := Fin N × Fin 3) (ρ := ρ) hh.2.2.1
  have hψ := AnnularSupportGeometry.supported_annulus ψ R hsupp
  have hcoord := centered_freeGraph_supported F χ O C e hcore hu (annulus_compact ρ R')
    (AnnularSupportGeometry.buffer_open ρ R' R) hKs hψ
  constructor
  · symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hψ, Filter.eventually_all.mpr hcoord.1, hcoord.2.1] with X hX hD hrad hnot
    have hn : X ∉ AnnularSupportGeometry.buffer ρ R' R := fun h => hnot (hsB h)
    have hm : ψ X = 0 := hX (fun h => hn (hKs h))
    have hD0 (j : Fin N × Fin 3) := hD j hn
    unfold operatorDensity density
    change Real.exp _ * (_ * ‖ψ X‖ ^ 2 + _ * (∑ j, ‖_‖ ^ 2) + _ * ‖_‖ ^ 2) = 0
    simp only [hm, hD0, hrad hn, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, zero_add]
  · symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hcoord.2.2] with X hX hnot
    unfold source
    dsimp only
    rw [hX (fun h => hnot (hsB h)), norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- The same constants apply to every smaller ball and every operator
vector with annular electronic support. -/
theorem annular_estimate
    (hcore : AnnularCoreApproximation C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e)
    {τ α r₀ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hr₀ : r₀ < 1) (hR : R ≤ r₀)
    (hest : ∀ s : Set (Configuration N), IsOpen s → ∀ ρ R' : ℝ,
      0 < ρ → R' < r₀ → s ⊆ annulus ρ R' →
      ∀ a : SmoothCore s, ∀ g : WaveSpace (Fin N × Fin 3), CompactSource s g →
      FreeGraph C (profile F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e a.reference g →
      (∫ X, operatorDensity F χ O C e τ α a.reference X) ≤
        64 * ∫ X, source τ α (fun Y => ‖g Y‖ ^ 2) X)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    (hu : FreeGraph C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e u f)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) 0 R) :
    (∫ X in Metric.ball 0 R, operatorDensity F χ O C e τ α u X) ≤
      64 * ∫ X in Metric.ball 0 R, source τ α (fun Y => ‖f Y‖ ^ 2) X := by
  have he := global_integrals_eq_ball F χ O C e hcore hu hsupp τ α
  rw [← he.1, ← he.2]
  exact annular_global_estimate F χ O C e hcore hτ hα hr₀ hR hest hu hsupp

end PfHk.PhysicalAnnularGraphTransfer
