import PfHk.PauliCurrentPhysicalCorrection
import PfHk.PauliMagnetizationMarginal
import PfHk.PauliPairCovariance
import PfHk.PauliExternalEnergyPairing

/-! The actual one-body Pauli current is the orbital combined current
plus one half of the distributional curl of spin magnetization. All
quantities are electronic marginals of the physical spin--photon state. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCurrentMagnetization

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalSourceCoordinates
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.CenteredPhysicalReference
  PfHk.PauliCurrentCorrection PfHk.PauliMagnetizationMarginal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion covariant ordinary
  PauliCurrent.wave PauliCurrent.pauliVelocity PauliGroundState.data
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.value
  ElectronicH1Complex.derivative

private theorem integral_half_difference {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {f g h : Y → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ y, f y + (1 / 2 : ℝ) * (g y - h y) ∂μ) =
      (∫ y, f y ∂μ) + (1 / 2 : ℝ) * ((∫ y, g y ∂μ) - ∫ y, h y ∂μ) := by
  have hd : Integrable (fun y => g y - h y) μ := hg.sub hh
  have hm : Integrable (fun y => (1 / 2 : ℝ) * (g y - h y)) μ := hd.const_mul _
  exact (integral_add hf hm).trans
    (congrArg (fun r : ℝ => (∫ y, f y ∂μ) + r)
      ((integral_const_mul (1 / 2 : ℝ) (fun y => g y - h y)).trans
        (congrArg (fun r : ℝ => (1 / 2 : ℝ) * r) (integral_sub hg hh))))

private theorem sum_curl {S : Type*} [Fintype S]
    (g : S → Fin 3 → Fin 3 → ℝ) (a : Fin 3) :
    (∑ n, ![g n 1 2 - g n 2 1, g n 2 0 - g n 0 2,
      g n 0 1 - g n 1 0] a) =
    ![(∑ n, g n 1 2) - ∑ n, g n 2 1,
      (∑ n, g n 2 0) - ∑ n, g n 0 2,
      (∑ n, g n 0 1) - ∑ n, g n 1 0] a := by
  fin_cases a
  · change (∑ n : S, (g n 1 2 - g n 2 1)) =
      (∑ n : S, g n 1 2) - (∑ n : S, g n 2 1)
    simp only [Finset.sum_sub_distrib]
  · change (∑ n : S, (g n 2 0 - g n 0 2)) =
      (∑ n : S, g n 2 0) - (∑ n : S, g n 0 2)
    simp only [Finset.sum_sub_distrib]
  · change (∑ n : S, (g n 0 1 - g n 1 0)) =
      (∑ n : S, g n 0 1) - (∑ n : S, g n 1 0)
    simp only [Finset.sum_sub_distrib]

def components (u : Ref N) : PauliCurrent.Components (N := N) :=
  fun s => electronic (Fin N × Fin 3) (fun _ => 0) (u s)

theorem components_value (u : Ref N) (s : SpinIndex N) :
    ElectronicH1Complex.value (E := PhotonFock) (I := Fin N × Fin 3) (components u s) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) := by
  unfold components inclusion
  rfl

def orbitalConfiguration (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (u : Ref N) (n : Fin N) (a : Fin 3)
    (X : Configuration N) : ℝ :=
  orbitalCurrent (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
    (fun b s => covariants C e F χ u (n,b) s X) a

def orbital (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (u : Ref N) (a : Fin 3) (x : Position) : ℝ :=
  ∑ n, marginal n (orbitalConfiguration C e F χ u n a) x

def curl (u : Ref N) (a : Fin 3) (x : Position) : ℝ :=
  ![weakGradient (components u) 1 2 x - weakGradient (components u) 2 1 x,
    weakGradient (components u) 2 0 x - weakGradient (components u) 0 2 x,
    weakGradient (components u) 0 1 x - weakGradient (components u) 1 0 x] a

theorem orbitalConfiguration_integrable (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (u : Ref N) (n : Fin N) (a : Fin 3) :
    Integrable (orbitalConfiguration C e F χ u n a) volume :=
  (integrable_finsetSum Finset.univ (fun s _ => L2.integrable_inner (𝕜 := ℂ)
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (covariants C e F χ u (n,a) s))).re

theorem orbital_integrable (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (u : Ref N) (a : Fin 3) :
    Integrable (orbital C e F χ u a) volume :=
  integrable_finsetSum Finset.univ (fun n _ => marginal_integrable n _
    (orbitalConfiguration_integrable C e F χ u n a))

theorem curl_integrable (u : Ref N) (a : Fin 3) : Integrable (curl u a) volume := by
  fin_cases a <;> exact (weakGradient_integrable (components u) _ _).sub
    (weakGradient_integrable (components u) _ _)

private theorem gradient_configuration (u : Ref N) (n : Fin N) (b k : Fin 3)
    (X : Configuration N) :
    PauliMagnetizationDistribution.weakGradient n (components u) (n,b) k X =
      magnetizationDerivative n
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun j s => ordinary (Fin N × Fin 3) (fun _ => 0) (n,j) (u s) X) b k := by
  unfold PauliMagnetizationDistribution.weakGradient PauliMagnetizationLp.pointPair
    magnetizationDerivative components inclusion ordinary
  rfl

theorem current_eq_orbital_add_half_curl (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (hN : 0 < N) (u : Ref N) (a : Fin 3) :
    (fun x => PhysicalPairSpace.currentL1 (data C e F χ u) x a) =ᵐ[volume]
      fun x => orbital C e F χ u a x + (1 / 2 : ℝ) * curl u a x := by
  let v := components u
  let d := covariants C e F χ u
  have hc (n : Fin N) :
      (fun X => (inner ℂ (PauliCurrent.wave v X) (PauliCurrent.pauliVelocity d n a X)).re) =ᵐ[volume]
      fun X => orbitalConfiguration C e F χ u n a X + (1 / 2 : ℝ) *
        magnetizationCurl n
          (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun b s => ordinary (Fin N × Fin 3) (fun _ => 0) (n,b) (u s) X) a := by
    have hvalues (X : Configuration N) :
        (fun s => ElectronicH1Complex.value (E := PhotonFock) (I := Fin N × Fin 3) (v s) X) =
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) :=
      funext fun s => congrArg (fun w : WaveSpace (Fin N × Fin 3) => w X) (components_value u s)
    have hv : (fun X => PauliCurrentAlgebra.current n
        (fun s => ElectronicH1Complex.value (E := PhotonFock) (I := Fin N × Fin 3) (v s) X)
        (fun b s => d (n,b) s X) a) =ᵐ[volume]
        fun X => PauliCurrentAlgebra.current n
          (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun b s => d (n,b) s X) a :=
      Filter.Eventually.of_forall fun X => congrArg
        (fun w : SpinIndex N → PhotonFock => PauliCurrentAlgebra.current n w
          (fun b s => d (n,b) s X) a) (hvalues X)
    exact (PauliExternalEnergy.current_ae n v d a).trans
      (hv.trans
        (PauliCurrentPhysicalCorrection.current_correction_ae C (profile F χ 0)
          (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e u n a))
  have hp (n : Fin N) := Measure.ae_ae_of_ae_prod
    ((split_symm_measurePreserving n).quasiMeasurePreserving.ae (hc n))
  have hj (n : Fin N) := ((split_symm_measurePreserving n).integrable_comp_of_integrable
    (L2.integrable_inner (𝕜 := ℂ) (PauliCurrent.wave v) (PauliCurrent.pauliVelocity d n a))).prod_right_ae
  have ho (n : Fin N) := ((split_symm_measurePreserving n).integrable_comp_of_integrable
    (orbitalConfiguration_integrable C e F χ u n a)).prod_right_ae
  have hg (n : Fin N) (b k : Fin 3) :=
    ((split_symm_measurePreserving n).integrable_comp_of_integrable
      (PauliMagnetizationDistribution.weakGradient_integrable n v (n,b) k)).prod_right_ae
  filter_upwards [PauliPairCovariance.pair_current_ae hN v d a,
    ae_all_iff.mpr hp, ae_all_iff.mpr hj, ae_all_iff.mpr ho,
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun b => ae_all_iff.mpr (hg n b)))]
    with x hx hpx hjx hox hgx
  have he (n : Fin N) :
      (∫ y, inner ℂ (PauliCurrent.wave v ((split n).symm (x,y)))
        (PauliCurrent.pauliVelocity d n a ((split n).symm (x,y)))).re =
      marginal n (orbitalConfiguration C e F χ u n a) x + (1 / 2 : ℝ) *
        ![marginal n (PauliMagnetizationDistribution.weakGradient n v (n,1) 2) x -
            marginal n (PauliMagnetizationDistribution.weakGradient n v (n,2) 1) x,
          marginal n (PauliMagnetizationDistribution.weakGradient n v (n,2) 0) x -
            marginal n (PauliMagnetizationDistribution.weakGradient n v (n,0) 2) x,
          marginal n (PauliMagnetizationDistribution.weakGradient n v (n,0) 1) x -
            marginal n (PauliMagnetizationDistribution.weakGradient n v (n,1) 0) x] a := by
    have hjn : Integrable (fun y : Spectator n =>
        inner ℂ (PauliCurrent.wave v ((split n).symm (x,y)))
          (PauliCurrent.pauliVelocity d n a ((split n).symm (x,y)))) volume := hjx n
    refine ((integral_re hjn).symm.trans (integral_congr_ae (hpx n))).trans ?_
    simp only [magnetizationCurl]
    simp_rw [← gradient_configuration]
    fin_cases a <;> exact integral_half_difference (hox n) (hgx n _ _) (hgx n _ _)
  unfold PauliGroundState.data
  change PhysicalPairSpace.currentL1 (PauliCurrent.pair v d) x a = _
  rw [hx]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  simpa only [orbital, curl, weakGradient] using
    congrArg (fun r : ℝ => orbital C e F χ u a x + (1 / 2 : ℝ) * r)
      (sum_curl (fun n b k => marginal n
        (PauliMagnetizationDistribution.weakGradient n v (n,b) k) x) a)

end PfHk.PauliCurrentMagnetization

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
