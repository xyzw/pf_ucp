import PfHk.PhysicalOpenRegularity
import PfHk.PauliLocalizedEigenstateDomain

/-! Open-set one-body regularity gives every local physical Pauli
coefficient bound at a configuration away from collisions. The Coulomb
bound follows from the actual pair potential. -/

noncomputable section
namespace PfHk.PauliPhysicalLocalRegularity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.PhysicalPairDuality PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PauliLocalEnergy PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference PfHk.SmoothCutoffBounds
  PfHk.FriedrichsDivergenceBackground PfHk.KatoRellichBackground
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion

/-- The paper's local one-body assumptions, with distributional curl
and divergence tested only inside the given open set. -/
structure RegularityOn (A : VectorPotential) (v : ScalarPotential)
    (Ω : Set PhysicalSourceCoordinates.Position)
    extends PhysicalOpenUCPCoefficients.RegularityOn A v Ω where
  magnetic : Fin 3 → PhysicalSourceCoordinates.Position → ℝ
  magnetic_local : ∀ k (K : Set PhysicalSourceCoordinates.Position),
    IsCompact K → K ⊆ Ω → MemLp (magnetic k) (ENNReal.ofReal exponent) (volume.restrict K)
  weak_curl : ∀ k, PauliClassicalCurl.WeakCurlPairOn Ω
    (fun j x => A.val x j) (k + 1) (k + 2) (magnetic k)

private theorem common_radius {J : Type*} [Fintype J]
    (r : J → ℝ) (hr : ∀ j, 0 < r j) {R : ℝ} (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ j, ρ ≤ r j := by
  classical
  have hfinite : ∀ s : Finset J, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ j ∈ s, ρ ≤ r j := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨R, hR, le_rfl, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨ρ, hρ, hρR, hρr⟩ := ih
      refine ⟨min ρ (r j), lt_min hρ (hr j), (min_le_left _ _).trans hρR, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hρr k hk)
  obtain ⟨ρ, hρ, hρR, hρr⟩ := hfinite Finset.univ
  exact ⟨ρ, hρ, hρR, fun j => hρr j (Finset.mem_univ j)⟩

private theorem closed_ball_inside {Ω : Set PhysicalSourceCoordinates.Position}
    (hΩ : IsOpen Ω) {o : PhysicalSourceCoordinates.Position} (ho : o ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall o r ⊆ Ω := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hΩ o ho
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx
  apply hball
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))

variable {N : ℕ} {A : VectorPotential} {v : ScalarPotential}
  {Ω : Set PhysicalSourceCoordinates.Position} {O : Configuration N}

/-- Local Coulomb boundedness is a conclusion of the off-collision
condition. No Lp bounds near the complement of Ω are needed. -/
theorem RegularityOn.exists_physicalRegularity (a : RegularityOn A v Ω)
    (hΩ : IsOpen Ω) (hcoords : ∀ n, (PhysicalSourceCoordinates.split n O).1 ∈ Ω)
    (hcoll : O ∈ distinctConfigurations N) (c : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (PauliLocalDomain.PhysicalRegularity A v c O ρ) := by
  have hballs : ∀ n : Fin N, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (PhysicalSourceCoordinates.split n O).1 r ⊆ Ω :=
    fun n => closed_ball_inside hΩ (hcoords n)
  choose r hr hball using hballs
  obtain ⟨R, hR, hB⟩ := PhysicalCoulombLocalBound.scaled_potential_local_memLp c hcoll
  obtain ⟨ρ, hρ, hρR, hρr⟩ := common_radius r hr hR
  have hsub (n : Fin N) : Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ ⊆
      Metric.closedBall (PhysicalSourceCoordinates.split n O).1 (r n) :=
    (Metric.ball_subset_ball (hρr n)).trans Metric.ball_subset_closedBall
  refine ⟨ρ, hρ, ⟨{
    exponent := a.exponent
    exponent_gt_two := a.exponent_gt_two
    divergence := a.divergence
    magnetic := a.magnetic
    vector_memLp := ?_
    divergence_memLp := ?_
    scalar_memLp := ?_
    coulomb_memLp := ?_
    weakDivergence := ?_
    magnetic_memLp := ?_
    weakCurl := ?_ }⟩⟩
  · intro n j
    exact (a.vector_local j _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · intro n
    exact (a.divergence_local _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · intro n
    exact (a.scalar_local _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · exact hB.mono_measure (Measure.restrict_mono (Metric.ball_subset_ball hρR) le_rfl)
  · intro n φ hφ hφs hφsub
    exact a.weak_divergence φ hφ hφs (hφsub.trans ((hsub n).trans (hball n)))
  · intro n k
    exact (a.magnetic_local k _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · intro n k φ hφ hφs hφsub
    exact a.weak_curl k φ hφ hφs (hφsub.trans ((hsub n).trans (hball n)))

/-- Every regular configuration admits a common radius on which all
buffered localizations of a weak eigenstate lie in the comparison
operator domain, directly from the open-set coefficient assumptions. -/
theorem RegularityOn.localized_eigenstate_comparison_domain
    (a : RegularityOn A v Ω) (hΩ : IsOpen Ω)
    (hcoords : ∀ n, (PhysicalSourceCoordinates.split n O).1 ∈ Ω)
    (hcoll : O ∈ distinctConfigurations N) (c : ℝ) (hc : 0 ≤ c)
    (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (friedrichs : StandardFriedrichsDivergence) (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (G : StandardWeylGraphC1 W)
    (D : StandardWeylFormCoreDensity W G) (KR : StandardKatoRellich)
    (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e)
    (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C
      (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e))
    (E : ℝ) (u : PauliReference.Ref N)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (family : BufferedFamily O) (r : ℝ),
      0 < r → r ≤ ρ / 32 →
      ∀ s, ComparisonDomain (fun _ => 0) (localize (family.cutoff r).scalar u s) := by
  obtain ⟨ρ, hρ, ⟨areg⟩⟩ := a.exists_physicalRegularity hΩ hcoords hcoll c
  refine ⟨ρ, hρ, ?_⟩
  intro family r hr hrρ
  exact PauliLocalDomain.physical_localized_eigenstate_comparison_domain
    hρ C F χ e S spectral joint friedrichs hUV W G D KR hD hG hSA
    areg hc family hr hrρ E u heigen

end PfHk.PauliPhysicalLocalRegularity

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
