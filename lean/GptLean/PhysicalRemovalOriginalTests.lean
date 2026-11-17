import GptLean.PhysicalGaussianScalarTests
import GptLean.PhysicalPhotonGaussian
import GptLean.PhysicalPFCurrentEvaluation

/-!
The original Gaussian density and current tests come from the actual
normal spectral source. Their operators and spatial weights are fixed
before localization. These are the density and current components of
OriginalSourceTests for Source.gaussianLattice.
-/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGaussianCoordinates PhysicalGaussianScalarTests
  PhysicalPFCurrentEvaluation PhotonLocalization RemovalSource
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {V : Position (Fin N × Fin 3) → ℝ}
  {B : StandardNormalTraceBackground} {x : B.Trace (WaveSpace (Fin N × Fin 3))}
  (s : Source (Fin N × Fin 3) V B x)
  (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

-- Use the direct normed-space parents of the constructed photon unitary.
local instance originalTestsPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance originalTestsHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

set_option backward.isDefEq.respectTransparency.types true in
/-- Any physical bounded density weight, including N times an electron test. -/
def Source.gaussianDensityTest
    (a : Position (Fin N × Fin 3) → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ z, |a z| ≤ A) :
    ProductDensityTest (X := Position (Fin N × Fin 3)) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ) (photonGaussianSource BF κ W N)
      (fun n => inclusion (Fin N × Fin 3) V (s.vector n))
      (boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
        (realL2Multiplier a ha A (ae_of_all _ hb)) x) := by
  have hs := (boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
    (realL2Multiplier a ha A (ae_of_all _ hb))).hasSum s.hasSum
  have hd : HasSum (fun n => ∫ z, a z * ‖inclusion (Fin N × Fin 3) V (s.vector n) z‖ ^ 2)
      (boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
        (realL2Multiplier a ha A (ae_of_all _ hb)) x) :=
    hs.congr_fun (fun n => (boundedTrace_multiplier_rankOne
      (B.realization (WaveSpace (Fin N × Fin 3))).functional a ha A (ae_of_all _ hb)
      (inclusion (Fin N × Fin 3) V (s.vector n))).symm)
  exact densityTest (X := Position (Fin N × Fin 3)) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ) a ha A hb (photonGaussianSource BF κ W N)
    (productSource_scalar (X := Position (Fin N × Fin 3)) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ) volume W.space.measure
        (photonGaussianUnitary BF κ W))
    (fun n => inclusion (Fin N × Fin 3) V (s.vector n)) _ hA hd

variable (C : CanonicalSectorCCR photonMeasure)
  (k : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ z ∂volume, ‖k i z‖ ≤ M)
  (S : StandardClosedFormBackground) (e : ℝ)

set_option backward.isDefEq.respectTransparency.types true in
/-- The current uses exactly the source covariant derivative in gaussianLattice. -/
def Source.gaussianCurrentTest
    (he : (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e).expectation x < ⊤)
    (a : Position (Fin N × Fin 3) → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hb : ∀ z, |a z| ≤ A) (i : Fin N × Fin 3) :
    ProductCurrentData (X := Position (Fin N × Fin 3)) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ) (photonGaussianSource BF κ W N)
      (fun n => inclusion (Fin N × Fin 3) V (s.vector n))
      (fun n => covariant (Fin N × Fin 3) V C k hk M hM e i (s.vector n))
      ((testedCurrent (Fin N × Fin 3) V C k hk M hM B S e a ha A (ae_of_all _ hb) i).value x) := by
  have hs := testedCurrent_source_hasSum (Fin N × Fin 3) V C k hk M hM B S e
    s he a ha A (ae_of_all _ hb) i
  exact currentTest (X := Position (Fin N × Fin 3)) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ) a ha A hb (photonGaussianSource BF κ W N)
    (productSource_scalar (X := Position (Fin N × Fin 3)) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ) volume W.space.measure
        (photonGaussianUnitary BF κ W))
    (fun n => inclusion (Fin N × Fin 3) V (s.vector n))
    (fun n => covariant (Fin N × Fin 3) V C k hk M hM e i (s.vector n)) _ hs

end GptLean.PhysicalPFSource
