import PfHk.PauliClassicalCurlForm
import PfHk.PhysicalDivergenceApproximation

/-! Friedrichs approximation is passed through a sesquilinear divergence
form. The divergence is never multiplied into an H1 vector as an L2 source. -/

noncomputable section
namespace PfHk.PauliClassicalCurlApproximation

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy PfHk.CoordinateSobolev
  PfHk.FriedrichsDivergenceBackground PfHk.PauliClassicalCurlForm
  PfHk.PhysicalOperatorDomain
open scoped ENNReal Topology InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 50000

section FormLimit

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem divergence_pairing_eq
    (S : CoordinateSobolev.Data H N)
    (A : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (d : Fin N → GptLean.PhysicalSourceCoordinates.Position → ℝ) (p : ℝ) (hp : 2 < p)
    (a : Approximation A d p)
    (hd : ∀ n, MemLp (d n) (ENNReal.ofReal p) volume)
    (u v : ElectronicH1Space.L2 H (Fin N × Fin 3))
    (uB vB : Fin N → ElectronicH1Space.L2 H (Fin N × Fin 3))
    (huB : ∀ n, BesselPair n (3 / (2 * p)) u (uB n))
    (hvB : ∀ n, BesselPair n (3 / (2 * p)) v (vB n)) (k : ℕ) :
    inner ℂ v (∑ i, (a.coefficient k i).derivativeMultiplier i u) =
      (∑ n, pairing n (d n) v u) +
        ∑ n, pairing n (a.divergenceError k n) v u := by
  have hid (n : Fin N) := (coordinate_bound S hp n (d n) (hd n)
    v u (vB n) (uB n) (hvB n) (huB n)).1
  have hie (n : Fin N) := (coordinate_bound S hp n (a.divergenceError k n)
    (a.divergence_memLp k n) v u (vB n) (uB n) (hvB n) (huB n)).1
  have hrep : (fun x => inner ℂ (v x)
      ((∑ i, (a.coefficient k i).derivativeMultiplier i u) x)) =ᵐ[volume]
      fun x => (∑ n, weightedInner (coordinateCoefficient n (d n)) v u x) +
        ∑ n, weightedInner (coordinateCoefficient n (a.divergenceError k n)) v u x := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun i => (a.coefficient k i).derivativeMultiplier i u),
      ae_all_iff.mpr (fun i => CoordinateDivergenceApproximation.derivative_ae
        (a.coefficient k i) u i)] with x hs hder
    rw [hs]
    simp only [hder, ← Finset.sum_smul, inner_smul_right_eq_smul,
      RCLike.real_smul_eq_coe_mul]
    have hgrad : (∑ i, (a.coefficient k i).gradient i x) =
        configurationDivergence d x + ∑ n, coordinateCoefficient n (a.divergenceError k n) x :=
      (sub_eq_iff_eq_add.mp (a.divergence_identity k x)).trans (add_comm _ _)
    rw [hgrad]
    simp only [configurationDivergence, RCLike.ofReal_add, RCLike.ofReal_sum,
      add_mul, Finset.sum_mul, weightedInner, RCLike.ofReal_eq_complex_ofReal]
  calc
    _ = ∫ x, inner ℂ (v x) ((∑ i, (a.coefficient k i).derivativeMultiplier i u) x) :=
      L2.inner_def v _
    _ = _ := integral_congr_ae hrep
    _ = _ := by
      rw [integral_add (integrable_finsetSum _ (fun n _ => hid n))
        (integrable_finsetSum _ (fun n _ => hie n)),
        integral_finsetSum _ (fun n _ => hid n), integral_finsetSum _ (fun n _ => hie n)]
      rfl

theorem divergence_pairing_tendsto
    (S : CoordinateSobolev.Data H N)
    (A : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (d : Fin N → GptLean.PhysicalSourceCoordinates.Position → ℝ) (p : ℝ) (hp : 2 < p)
    (a : Approximation A d p)
    (hd : ∀ n, MemLp (d n) (ENNReal.ofReal p) volume)
    (u v : ElectronicH1Space.L2 H (Fin N × Fin 3))
    (uB vB : Fin N → ElectronicH1Space.L2 H (Fin N × Fin 3))
    (huB : ∀ n, BesselPair n (3 / (2 * p)) u (uB n))
    (hvB : ∀ n, BesselPair n (3 / (2 * p)) v (vB n)) :
    Tendsto (fun k => inner ℂ v (∑ i, (a.coefficient k i).derivativeMultiplier i u))
      atTop (𝓝 (∑ n, pairing n (d n) v u)) := by
  have he (n : Fin N) := pairing_tendsto_zero S hp n (fun k => a.divergenceError k n)
    (fun k => a.divergence_memLp k n) (a.divergence_tendsto n)
    v u (vB n) (uB n) (hvB n) (huB n)
  have ht : Tendsto (fun k => ∑ n, pairing n (a.divergenceError k n) v u) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun n _ => he n)
  have hs := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑ n, pairing n (d n) v u)
    atTop (𝓝 (∑ n, pairing n (d n) v u))).add ht
  exact Filter.Tendsto.congr (fun k =>
    (divergence_pairing_eq S A d p hp a hd u v uB vB huB hvB k).symm)
      (by simpa only [add_zero] using hs)

end FormLimit

section Physical

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] PhysicalPFReference.referenceSubspace inclusion ordinary
  PhysicalPFReference.covariant PhysicalPFReference.field roughMultiply HasMultiplier

variable {N : ℕ}

/-- Distributional divergence enters only as an integrable form, so the
identity holds on the reference form domain without an operator-domain premise. -/
theorem covariant_divergence_form_pair
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (friedrichs : StandardFriedrichsDivergence)
    (A : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (d : Fin N → GptLean.PhysicalSourceCoordinates.Position → ℝ) (p : ℝ) (hp : 2 < p)
    (hA : ∀ n i, MemLp (A n i) 6 volume)
    (hd : ∀ n, MemLp (d n) (ENNReal.ofReal p) volume)
    (hdiv : ∀ n, WeakDivergence (A n) (d n))
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0))
    (hau : ∀ i, HasMultiplier (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hav : ∀ i, HasMultiplier (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) v)) :
    (∑ i, inner ℂ (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i v)
      (roughMultiply (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hau i))) =
    (∑ i, inner ℂ (roughMultiply (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) v) (hav i))
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i u)) -
      Complex.I * ∑ n, pairing n (d n)
        (inclusion (Fin N × Fin 3) (fun _ => 0) v)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  let a := friedrichs.resolve N A d p hp hA hd hdiv
  have hBu (n : Fin N) := joint.form_value n (1 / 2) (by norm_num) (by norm_num) u
  have hBv (n : Fin N) := joint.form_value n (1 / 2) (by norm_num) (by norm_num) v
  have hAu (i : Fin N × Fin 3) := CoordinateDivergenceApproximation.value_tendsto
    S A d p a (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (fun i => roughMultiply (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hau i))
    (fun i => roughMultiply_ae _ _ (hau i))
    (fun n => ⟨Classical.choose (hBu n), (Classical.choose_spec (hBu n)).1⟩) i
  have hAv (i : Fin N × Fin 3) := CoordinateDivergenceApproximation.value_tendsto
    S A d p a (inclusion (Fin N × Fin 3) (fun _ => 0) v)
    (fun i => roughMultiply (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) v) (hav i))
    (fun i => roughMultiply_ae _ _ (hav i))
    (fun n => ⟨Classical.choose (hBv n), (Classical.choose_spec (hBv n)).1⟩) i
  have hp0 : 0 < p := by linarith
  have hs0 : 0 ≤ 3 / (2 * p) := by positivity
  have hs1 : 3 / (2 * p) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hFu (n : Fin N) := joint.form_value n (3 / (2 * p)) hs0 hs1 u
  have hFv (n : Fin N) := joint.form_value n (3 / (2 * p)) hs0 hs1 v
  have hform := divergence_pairing_tendsto S A d p hp a hd
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (inclusion (Fin N × Fin 3) (fun _ => 0) v)
    (fun n => Classical.choose (hFu n)) (fun n => Classical.choose (hFv n))
    (fun n => (Classical.choose_spec (hFu n)).1)
    (fun n => (Classical.choose_spec (hFv n)).1)
  have hleft := tendsto_finsetSum Finset.univ (fun i _ =>
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i v) atTop
        (𝓝 (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i v))).inner
          (𝕜 := ℂ) (hAu i)))
  have hright := (tendsto_finsetSum Finset.univ (fun i _ =>
    (hAv i).inner (𝕜 := ℂ) (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i u) atTop
        (𝓝 (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i u))))).sub
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Complex.I) atTop (𝓝 Complex.I)).mul hform)
  apply tendsto_nhds_unique hleft
  exact Filter.Tendsto.congr (fun k =>
    (PhysicalExternalOperator.smooth_covariant_divergence_pair (fun _ => 0)
      C κ hκ M hM e (a.coefficient k) u v).symm) hright

end Physical

end PfHk.PauliClassicalCurlApproximation

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
