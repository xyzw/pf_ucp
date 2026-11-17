import GptLean.PhysicalGaussianRadiationOutput
import GptLean.PhysicalGaussianProduct
import GptLean.PhysicalSoftSpatialEnergy
import GptLean.RemovalSourceLattice

/-!
The original lattice source is constructed from an actual finite-energy
normal spectral source. Its rest term uses the recovered hard radiation
operator and the original potential graph. The total input energy and
removed soft energy are exact identities for the original normal state.
-/

noncomputable section
namespace GptLean.PhysicalPFSource

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGaussianCoordinates RemovalSource SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem pair_isometry_norm_sq {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : WithLp 2 (E × F) →ₗᵢ[ℂ] G) (u : E) (v : F) :
    ‖L (WithLp.toLp 2 (u, v))‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  (congrArg (fun t : ℝ => t ^ 2) (L.norm_map (WithLp.toLp 2 (u, v)))).trans
    (WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (u, v)))

private theorem energy_partition_of_equalities (a b c d e f : ℝ)
    (hb : b = d + e) (hf : f = e + c) : a + b + c = a + f + d := by
  rw [hb, hf]
  ring

private theorem l2_norm_sq_partition {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (u v w : Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 = ‖v x‖ ^ 2 + ‖w x‖ ^ 2) :
    ‖u‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hi (f : Lp H 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral, ← integral_add (hi v) (hi w)]
  exact integral_congr_ae h

variable {N : ℕ} (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (k : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hb : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)
  (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

def hardReference : Reference (Fin N × Fin 3) V →L[ℂ] WaveSpace (Fin N × Fin 3) :=
  ((hardGaussianRoot B.normal (B.realization PhotonFock).functional BF C κ W).compLpL 2 volume).comp
    (radiationSource (Fin N × Fin 3) V)

def gaussianRestReference : Reference (Fin N × Fin 3) V →L[ℂ]
    Lp (WithLp 2 (PhotonFock × PhotonFock)) 2 (volume : Measure (Position (Fin N × Fin 3))) :=
  (pairL2Isometry (H := PhotonFock) (K := PhotonFock) volume).toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ (WaveSpace (Fin N × Fin 3))
      (WaveSpace (Fin N × Fin 3))).symm.toContinuousLinearMap.comp
        ((hardReference V C B BF κ W).prod (potential (Fin N × Fin 3) V)))

theorem gaussianRestReference_norm_sq (u : Reference (Fin N × Fin 3) V) :
    ‖gaussianRestReference V C B BF κ W u‖ ^ 2 =
      ‖hardReference V C B BF κ W u‖ ^ 2 + ‖potential (Fin N × Fin 3) V u‖ ^ 2 := by
  change ‖pairL2Isometry (H := PhotonFock) (K := PhotonFock) volume (WithLp.toLp 2
    (hardReference V C B BF κ W u, potential (Fin N × Fin 3) V u))‖ ^ 2 = _
  exact pair_isometry_norm_sq
    (pairL2Isometry (H := PhotonFock) (K := PhotonFock) volume)
    (hardReference V C B BF κ W u) (potential (Fin N × Fin 3) V u)

theorem radiation_reference_partition (u : Reference (Fin N × Fin 3) V) :
    ‖radiation (Fin N × Fin 3) V u‖ ^ 2 =
      ‖softReference (Fin N × Fin 3) V κ u‖ ^ 2 + ‖hardReference V C B BF κ W u‖ ^ 2 := by
  have he := hardGaussianRoot_spatial_norm_sq B.normal (B.realization PhotonFock).functional
    BF C κ W volume (radiationSource (Fin N × Fin 3) V u)
  change ‖hardReference V C B BF κ W u‖ ^ 2 = _ at he
  let q := radiationSource (Fin N × Fin 3) V u
  have hp : ‖radiationGraphDerivative.compLpL 2 volume q‖ ^ 2 =
      ‖(softRadiationRoot κ).compLpL 2 volume q‖ ^ 2 +
        ‖(hardRadiationRoot κ).compLpL 2 volume q‖ ^ 2 := by
    apply l2_norm_sq_partition volume (radiationGraphDerivative.compLpL 2 volume q)
      ((softRadiationRoot κ).compLpL 2 volume q)
      ((hardRadiationRoot κ).compLpL 2 volume q)
    filter_upwards [radiationGraphDerivative.coeFn_compLpL q,
      (softRadiationRoot κ).coeFn_compLpL q, (hardRadiationRoot κ).coeFn_compLpL q]
      with x hr hs hh
    exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hr).trans
      ((radiationRoot_norm_partition κ (q x)).trans
        (congrArg₂ (fun v w : PhotonFock => ‖v‖ ^ 2 + ‖w‖ ^ 2) hs hh).symm)
  exact hp.trans (congrArg
    (fun t : ℝ => ‖softReference (Fin N × Fin 3) V κ u‖ ^ 2 + t) he.symm)

theorem gaussianReference_energy (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C k hk M hb e u =
      (1 / 2 : ℝ) * ∑ j, ‖covariant (Fin N × Fin 3) V C k hk M hb e j u‖ ^ 2 +
        ‖gaussianRestReference V C B BF κ W u‖ ^ 2 +
        ‖softReference (Fin N × Fin 3) V κ u‖ ^ 2 := by
  exact energy_partition_of_equalities
    ((1 / 2 : ℝ) * ∑ j, ‖covariant (Fin N × Fin 3) V C k hk M hb e j u‖ ^ 2)
    (‖radiation (Fin N × Fin 3) V u‖ ^ 2) (‖potential (Fin N × Fin 3) V u‖ ^ 2)
    (‖softReference (Fin N × Fin 3) V κ u‖ ^ 2) (‖hardReference V C B BF κ W u‖ ^ 2)
    (‖gaussianRestReference V C B BF κ W u‖ ^ 2)
    (radiation_reference_partition V C B BF κ W u)
    (gaussianRestReference_norm_sq V C B BF κ W u)

variable {V B}
variable {x : B.Trace (WaveSpace (Fin N × Fin 3))}
  (s : Source (Fin N × Fin 3) V B x)
  (he : (normalEnergy (Fin N × Fin 3) V C k hk M hb B S e).expectation x < ⊤)
  (hm : (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace x = 1)

section LatticeConstructor

-- Align inherited scalar parents with the concrete photon unitaries.
local instance pfSourcePhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance pfSourceHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

attribute [local irreducible] photonGaussianSource photonGaussianUnitary productSource productUnitary

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
/-- All vectors and square summability come from the same normal source. -/
def Source.gaussianLattice : LatticeSourceData N W.space.measure PhotonFock (HardPhotonFock κ)
    (WithLp 2 (PhotonFock × PhotonFock)) (WithLp 2 (HardPhotonFock κ × HardPhotonFock κ)) PhotonFock where
  U := photonGaussianSource BF κ W N
  Ur := productSource (X := Configuration N) (Q := W.space.Q)
    (H := WithLp 2 (PhotonFock × PhotonFock))
    (K := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ)) volume W.space.measure
    (productUnitary (H := PhotonFock) (K := HardPhotonFock κ)
      W.space.measure (photonGaussianUnitary BF κ W))
  ψ n := inclusion (Fin N × Fin 3) V (s.vector n)
  dψ n j := covariant (Fin N × Fin 3) V C k hk M hb e j (s.vector n)
  rest n := gaussianRestReference V C B BF κ W (s.vector n)
  soft n := softReference (Fin N × Fin 3) V κ (s.vector n)
  mass := (congrArg (fun t : ℝ =>
    HasSum (fun n => ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2) t) hm).mp s.mass_hasSum
  kinetic_summable j := s.operator_summable C k hk M hb S e he
    (covariant (Fin N × Fin 3) V C k hk M hb e j)
  rest_summable := s.operator_summable C k hk M hb S e he (gaussianRestReference V C B BF κ W)
  soft_summable := s.operator_summable C k hk M hb S e he (softReference (Fin N × Fin 3) V κ)

end LatticeConstructor

theorem Source.gaussianLattice_energy :
    (s.gaussianLattice C k hk M hb S e BF κ W he hm).inputEnergy =
      ((normalEnergy (Fin N × Fin 3) V C k hk M hb B S e).expectation x).toReal := by
  let src := s.gaussianLattice C k hk M hb S e BF κ W he hm
  have hkin := hasSum_sum (s := Finset.univ) (fun j _ => (src.kinetic_summable j).hasSum)
  have hs := ((hkin.mul_left (1 / 2 : ℝ)).add src.rest_summable.hasSum).add
    src.soft_summable.hasSum
  have htotal : HasSum (fun n => energy (Fin N × Fin 3) V C k hk M hb e (s.vector n))
      src.inputEnergy := by
    apply hs.congr_fun
    intro n
    exact gaussianReference_energy V C k hk M hb B e BF κ W (s.vector n)
  exact htotal.unique (s.energy_hasSum C k hk M hb S e he)

theorem Source.gaussianLattice_soft :
    (PhysicalPhotonMarginal.fullMomentumForm B (volume : Measure (Position (Fin N × Fin 3)))
      (NormalPhoton.softWeight κ) (NormalPhoton.softWeight_measurable κ)).expectation x =
      ENNReal.ofReal (∑' n, ‖(s.gaussianLattice C k hk M hb S e BF κ W he hm).soft n‖ ^ 2) :=
  s.soft_expectation (Fin N × Fin 3) V C k hk M hb B S e κ he

end GptLean.PhysicalPFSource
