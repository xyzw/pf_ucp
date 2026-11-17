import PfHk.PauliClassicalCurlLocal
import PfHk.PauliClassicalCurlRotationAlgebra

/-! The localized scalar covariant commutator with distributional curl.
A rotated vector field reduces the curl to the ordinary Friedrichs
weak-divergence identity. Local Lp curl coefficients with p greater than
two enter as integrable forms on the actual reference vectors. Coordinate
support localizes the argument without imposing individual derivatives
of the vector potential or an L2 classical magnetic source. -/

noncomputable section
namespace PfHk.PauliClassicalCurl

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Space GptLean.SymmetricLift PfHk.CoordinateSobolev PfHk.PauliClassicalCurlForm
  PfHk.PhysicalOperatorDomain PfHk.FriedrichsDivergenceBackground PfHk.PhysicalLocalEnergy
  PfHk.PauliClassicalCurlRotationAlgebra
open scoped ENNReal Topology InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}

def selectedVector (n : Fin N) (F : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (m : Fin N) (j : Fin 3) (x : GptLean.PhysicalSourceCoordinates.Position) : ℝ :=
  if m = n then F j x else 0

def selectedScalar (n : Fin N) (b : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (m : Fin N) (x : GptLean.PhysicalSourceCoordinates.Position) : ℝ :=
  if m = n then b x else 0

theorem selectedVector_self (n : Fin N)
    (F : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ) :
    selectedVector n F n = F := by
  funext j x
  simp [selectedVector]

theorem selectedVector_ne (n m : Fin N) (hm : m ≠ n)
    (F : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ) :
    selectedVector n F m = fun _ _ => 0 := by
  funext j x
  simp [selectedVector, hm]

theorem selectedScalar_self (n : Fin N)
    (b : GptLean.PhysicalSourceCoordinates.Position → ℝ) :
    selectedScalar n b n = b := by
  funext x
  simp [selectedScalar]

theorem selectedScalar_ne (n m : Fin N) (hm : m ≠ n)
    (b : GptLean.PhysicalSourceCoordinates.Position → ℝ) :
    selectedScalar n b m = fun _ => 0 := by
  funext x
  simp [selectedScalar, hm]

theorem rearrange (a b c d t : ℂ)
    (h : a - b = (c - d) - Complex.I * t) :
    (a - c) - (b - d) = -Complex.I * t := by
  linear_combination h

section Representative

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem localized_rotation_ae (n : Fin N) (o : GptLean.PhysicalSourceCoordinates.Position)
    {ρ : ℝ} (hρ : 0 < ρ) (a b : Fin 3) (hab : a ≠ b)
    (A : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (u : L2 H (Fin N × Fin 3)) (au : Fin 3 → L2 H (Fin N × Fin 3))
    (hau : ∀ j, au j =ᵐ[volume] fun X => coordinateCoefficient n (A j) X • u X)
    (hu : SupportedInCoordinate n (Metric.ball o (ρ / 2)) u) (i : Fin N × Fin 3) :
    (fun X => (singleRotation n a b au i : L2 H (Fin N × Fin 3)) X) =ᵐ[volume] fun X =>
      configurationVector (selectedVector n (localizedVector o ρ hρ a b A)) i X • u X := by
  rcases i with ⟨m,j⟩
  by_cases hmn : m = n
  · subst m
    by_cases hja : j = a
    · subst j
      have ht := coefficient_product_congr n (Metric.ball o (ρ / 2))
        (A b) (localizedVector o ρ hρ a b A a)
        (fun x hx => by simpa only [rotated, ite_true] using
          (localized_vector_eq o hρ a b A a hx).symm) u hu
      simpa only [singleRotation, selectedVector, ite_true, configurationVector,
        coordinateCoefficient] using (hau b).trans ht
    · by_cases hjb : j = b
      · subst j
        have hn : (-au a : L2 H (Fin N × Fin 3)) =ᵐ[volume]
            fun X => coordinateCoefficient n (fun x => -A a x) X • u X := by
          filter_upwards [Lp.coeFn_neg (au a), hau a] with X hx hy
          simpa only [Pi.neg_apply, hy, coordinateCoefficient, neg_smul] using hx
        have ht := coefficient_product_congr n (Metric.ball o (ρ / 2))
          (fun x => -A a x) (localizedVector o ρ hρ a b A b)
          (fun x hx => by simpa only [rotated, ite_eq_right (Ne.symm hab), ite_true] using
            (localized_vector_eq o hρ a b A b hx).symm) u hu
        simpa only [singleRotation, selectedVector, ite_true, ite_eq_right (Ne.symm hab),
          configurationVector, coordinateCoefficient] using hn.trans ht
      · filter_upwards [Lp.coeFn_zero H 2 (volume : Measure (Configuration N))] with X hx
        simpa only [singleRotation, selectedVector, ite_true, ite_eq_right hja, ite_eq_right hjb,
          configurationVector, coordinateCoefficient, localizedVector, truncatedVector,
          rotated, mul_zero, zero_smul, Pi.zero_apply] using hx
  · filter_upwards [Lp.coeFn_zero H 2 (volume : Measure (Configuration N))] with X hx
    simpa only [singleRotation, selectedVector, ite_eq_right hmn, configurationVector,
      coordinateCoefficient, zero_smul, Pi.zero_apply] using hx

theorem pairing_selected (n : Fin N) (d : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (u v : L2 H (Fin N × Fin 3)) :
    (∑ m, pairing m (selectedScalar n d m) v u) = pairing n d v u := by
  have he (m : Fin N) : pairing m (selectedScalar n d m) v u =
      if m = n then pairing n d v u else 0 := by
    by_cases hm : m = n
    · subst m
      simp only [pairing, weightedInner, coordinateCoefficient, selectedScalar, ite_true]
    · simp only [pairing, weightedInner, coordinateCoefficient, selectedScalar, ite_eq_right hm,
        Complex.ofReal_zero, zero_mul, integral_zero]
  simp only [he]
  exact sum_single n _

end Representative

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] PhysicalPFReference.referenceSubspace inclusion
  PhysicalPFReference.covariant roughMultiply HasMultiplier

/-- The scalar part of the local weak Pauli commutator. Only the
distributional curl is assumed, and it is paired as a form. -/
theorem local_cross_pair
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral) (friedrichs : StandardFriedrichsDivergence)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hM : ∀ i, ∀ᵐ X ∂volume, ‖κ i X‖ ≤ M) (e : ℝ)
    (n : Fin N) (o : GptLean.PhysicalSourceCoordinates.Position)
    {ρ p : ℝ} (hρ : 0 < ρ) (hp : 2 < p) (a b : Fin 3) (hab : a ≠ b)
    (A : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (curl : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hA : ∀ j, MemLp (A j) 6 (volume.restrict (Metric.ball o ρ)))
    (hcurlLp : MemLp curl (ENNReal.ofReal p) (volume.restrict (Metric.ball o ρ)))
    (hcurl : WeakCurlPairOn (Metric.ball o ρ) A a b curl)
    (u z : Reference (Fin N × Fin 3) (fun _ => 0))
    (hAu : ∀ j, HasMultiplier (coordinateCoefficient n (A j))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hAz : ∀ j, HasMultiplier (coordinateCoefficient n (A j))
      (inclusion (Fin N × Fin 3) (fun _ => 0) z))
    (hus : SupportedInCoordinate n (Metric.ball o (ρ / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hzs : SupportedInCoordinate n (Metric.ball o (ρ / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) z)) :
    (inner ℂ (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,a) z)
      (roughMultiply (coordinateCoefficient n (A b)) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hAu b)) -
      inner ℂ (roughMultiply (coordinateCoefficient n (A b)) (inclusion (Fin N × Fin 3) (fun _ => 0) z) (hAz b))
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,a) u)) -
    (inner ℂ (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,b) z)
      (roughMultiply (coordinateCoefficient n (A a)) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hAu a)) -
      inner ℂ (roughMultiply (coordinateCoefficient n (A a)) (inclusion (Fin N × Fin 3) (fun _ => 0) z) (hAz a))
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,b) u)) =
      -Complex.I * pairing n curl
        (inclusion (Fin N × Fin 3) (fun _ => 0) z)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  let F := selectedVector n (localizedVector o ρ hρ a b A)
  let d := selectedScalar n (localizedCurl o ρ hρ a b A curl)
  let q := min p 6
  have hq : 2 < q := SmoothVectorTruncation.divergence_exponent hp
  have hF (m : Fin N) (j : Fin 3) : MemLp (F m j) 6 volume := by
    by_cases hm : m = n
    · subst m
      simpa only [F, selectedVector_self] using
        localized_vector_memLp o hρ a b A hA j
    · simpa only [F, selectedVector_ne n m hm] using
        (MemLp.zero' : MemLp (fun _ : GptLean.PhysicalSourceCoordinates.Position => (0 : ℝ)) 6 volume)
  have hd (m : Fin N) : MemLp (d m) (ENNReal.ofReal q) volume := by
    by_cases hm : m = n
    · subst m
      simpa only [d, q, selectedScalar_self] using
        localized_curl_memLp o hρ a b A curl hA hcurlLp
    · simpa only [d, selectedScalar_ne n m hm] using
        (MemLp.zero' : MemLp (fun _ : GptLean.PhysicalSourceCoordinates.Position => (0 : ℝ))
          (ENNReal.ofReal q) volume)
  have hdiv (m : Fin N) : WeakDivergence (F m) (d m) := by
    by_cases hm : m = n
    · subst m
      simpa only [F, d, selectedVector_self, selectedScalar_self] using
        localized_weakDivergence o hρ hp a b hab A curl hA hcurlLp hcurl
    · intro φ hφ hφc
      simp only [F, d, selectedVector_ne n m hm, selectedScalar_ne n m hm,
        zero_mul, integral_zero, Finset.sum_const_zero, neg_zero]
  let au (j : Fin 3) := roughMultiply (coordinateCoefficient n (A j))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hAu j)
  let az (j : Fin 3) := roughMultiply (coordinateCoefficient n (A j))
    (inclusion (Fin N × Fin 3) (fun _ => 0) z) (hAz j)
  have hru (i : Fin N × Fin 3) := localized_rotation_ae (H := PhotonFock) (N := N) n o hρ a b hab A
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) au (fun j => roughMultiply_ae _ _ (hAu j)) hus i
  have hrz (i : Fin N × Fin 3) := localized_rotation_ae (H := PhotonFock) (N := N) n o hρ a b hab A
    (inclusion (Fin N × Fin 3) (fun _ => 0) z) az (fun j => roughMultiply_ae _ _ (hAz j)) hzs i
  have hFu (i : Fin N × Fin 3) : HasMultiplier (configurationVector F i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
    unfold HasMultiplier
    exact (Lp.memLp (singleRotation n a b au i)).ae_eq (hru i)
  have hFz (i : Fin N × Fin 3) : HasMultiplier (configurationVector F i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) z) := by
    unfold HasMultiplier
    exact (Lp.memLp (singleRotation n a b az i)).ae_eq (hrz i)
  have heu (i : Fin N × Fin 3) : roughMultiply (configurationVector F i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hFu i) = singleRotation n a b au i :=
    Lp.ext ((roughMultiply_ae _ _ (hFu i)).trans (hru i).symm)
  have hez (i : Fin N × Fin 3) : roughMultiply (configurationVector F i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) z) (hFz i) = singleRotation n a b az i :=
    Lp.ext ((roughMultiply_ae _ _ (hFz i)).trans (hrz i).symm)
  have hf := PauliClassicalCurlApproximation.covariant_divergence_form_pair
    S spectral joint friedrichs F d q hq hF hd hdiv C κ hκ M hM e u z hFu hFz
  have hl : (∑ i, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i z)
      (roughMultiply (configurationVector F i)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hFu i))) =
      inner ℂ (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,a) z) (au b) -
        inner ℂ (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,b) z) (au a) :=
    (Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
      congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
        inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i z) w) (heu i))).trans
      (inner_singleRotation_right n a b hab
        (fun i => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i z) au)
  have hr : (∑ i, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (roughMultiply (configurationVector F i)
        (inclusion (Fin N × Fin 3) (fun _ => 0) z) (hFz i))
      (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i u)) =
      inner ℂ (az b) (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,a) u) -
        inner ℂ (az a) (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e (n,b) u) :=
    (Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
      congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
        inner ℂ (E := WaveSpace (Fin N × Fin 3)) w
          (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i u)) (hez i))).trans
      (inner_singleRotation_left n a b hab
        (fun i => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hM e i u) az)
  have hdform := (pairing_selected (H := PhotonFock) (N := N) n (localizedCurl o ρ hρ a b A curl)
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)).trans
      (pairing_congr (H := PhotonFock) (N := N) n (Metric.ball o (ρ / 2)) (localizedCurl o ρ hρ a b A curl) curl
        (fun x hx => localized_curl_eq o hρ a b A curl hx)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u)
        (inclusion (Fin N × Fin 3) (fun _ => 0) z) hus)
  exact rearrange _ _ _ _ _
    (hl.symm.trans (hf.trans (congrArg₂ (fun x y : ℂ => x - Complex.I * y) hr hdform)))

end PfHk.PauliClassicalCurl

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
