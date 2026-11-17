import PfHk.PhysicalExternalCoefficients
import PfHk.PhysicalDyadicCoordinatePerturbation
import PfHk.PhysicalDyadicKineticPerturbation
import PfHk.FiniteWeightedSource

/-! The actual Hamiltonian error is a finite sum of coordinate products.
Its weighted source bound is derived from the proved scalar and magnetic
localizations and ordinary coefficient Lp hypotheses. -/

noncomputable section
namespace PfHk.PhysicalExternalSource

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain
  PfHk.PhysicalExternalCoefficients PfHk.PhysicalCoordinateMultipliers
  PfHk.PhysicalDyadicCoordinatePerturbation PfHk.PhysicalDyadicScalarPerturbation
  PfHk.PhysicalDyadicMagneticPerturbation PfHk.PhysicalDyadicKineticPerturbation
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalDyadicPartition PfHk.PhysicalCarlemanInput
  PfHk.CoordinateSobolev PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant roughMultiply HasMultiplier
  PhysicalFractionalCarleman.MixedEstimate PhysicalEnlargedFractionalCarleman.MixedEstimate
  ScalarFractionalMultiplier CovariantFractionalMultiplier

abbrev Term (N : ℕ) := (Fin N × Fin 3) ⊕ ((Fin N × Fin 3) ⊕ (Fin N ⊕ (Fin N ⊕ Unit)))

variable {N : ℕ}

theorem card_term : Fintype.card (Term N) = 8 * N + 1 := by
  simp only [Term, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  omega

def scalarOrder (q : ℝ) : ℝ := 3 / q

def radiusExponent (a : PfHk.PhysicalExternalCoefficients.Data N) : Term N → ℝ
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr (.inl _)) => 4 - 2 * scalarOrder a.divergenceExponent
  | .inr (.inr (.inr (.inl _))) => 4 - 2 * scalarOrder a.scalarExponent
  | .inr (.inr (.inr (.inr _))) => 4

def parameterExponent (a : PfHk.PhysicalExternalCoefficients.Data N) : Term N → ℝ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 3 - 2 * scalarOrder a.divergenceExponent
  | .inr (.inr (.inr (.inl _))) => 3 - 2 * scalarOrder a.scalarExponent
  | .inr (.inr (.inr (.inr _))) => 3

def coefficient : Term N → ℂ
  | .inl _ => 1
  | .inr (.inl _) => 1 / 2
  | .inr (.inr (.inl _)) => -Complex.I / 2
  | .inr (.inr (.inr _)) => 1

theorem coefficient_norm (t : Term N) : ‖coefficient t‖ ≤ 1 := by
  rcases t with i | i | n | n | t <;> norm_num [coefficient, norm_div]

private theorem order_bounds {q : ℝ} (hq : 2 < q) : 0 < scalarOrder q ∧ scalarOrder q < 3 / 2 := by
  have hq0 : 0 < q := by linarith only [hq]
  exact ⟨div_pos (by norm_num) hq0, (div_lt_iff₀ hq0).mpr (by nlinarith only [hq])⟩

theorem radiusExponent_pos (a : PfHk.PhysicalExternalCoefficients.Data N) (t : Term N) : 0 < radiusExponent a t := by
  have hd := (order_bounds a.divergenceExponent_gt_two).2
  have hp := (order_bounds a.scalarExponent_gt_two).2
  rcases t with i | i | n | n | t <;> dsimp [radiusExponent] <;> linarith only [hd, hp]

theorem parameterExponent_nonneg (a : PfHk.PhysicalExternalCoefficients.Data N) (t : Term N) : 0 ≤ parameterExponent a t := by
  have hd := (order_bounds a.divergenceExponent_gt_two).2
  have hp := (order_bounds a.scalarExponent_gt_two).2
  rcases t with i | i | n | n | t <;> dsimp [parameterExponent] <;> linarith only [hd, hp]

def mixedConstant (C₂ s : ℝ) : ℝ := (s / 2) * C₂ + (1 - s / 2) * 6144

private theorem mixedConstant_nonneg {C₂ s : ℝ} (hC : 0 ≤ C₂) (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    0 ≤ mixedConstant C₂ s := by
  have hh : 0 ≤ 1 - s / 2 := by linarith only [hs2]
  unfold mixedConstant
  positivity

def componentConstant (a : PfHk.PhysicalExternalCoefficients.Data N) (S : CoordinateSobolev.Data PhotonFock N)
    (C₂ C₂e G e M : ℝ) : Term N → ℝ
  | .inl i => 24 * (((2 + 20 * e ^ 2 * (max M 0) ^ 2) *
      coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2)) * ((3 / 4) * C₂e + 10240) +
      G ^ 2 * coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2) * ((1 / 4) * C₂e + 30720))
  | .inr (.inl i) => 12 * coefficientNormSq S 3 (fun x => a.vectorCoefficient i.1 i.2 x ^ 2) *
      mixedConstant C₂ 1
  | .inr (.inr (.inl n)) => 12 * coefficientNormSq S a.divergenceExponent (a.divergenceCoefficient n) *
      mixedConstant C₂ (scalarOrder a.divergenceExponent)
  | .inr (.inr (.inr (.inl n))) => 12 * coefficientNormSq S a.scalarExponent (a.scalarCoefficient n) *
      mixedConstant C₂ (scalarOrder a.scalarExponent)
  | .inr (.inr (.inr (.inr _))) => 12 * (eLpNorm a.boundedCoefficient ∞ volume).toReal ^ 2 *
      mixedConstant C₂ 0

def sourceConstant (a : PfHk.PhysicalExternalCoefficients.Data N) (S : CoordinateSobolev.Data PhotonFock N)
    (C₂ C₂e G e M : ℝ) (t : Term N) : ℝ :=
  (Fintype.card (Term N) : ℝ) * componentConstant a S C₂ C₂e G e M t

theorem sourceConstant_nonneg (a : PfHk.PhysicalExternalCoefficients.Data N) (S : CoordinateSobolev.Data PhotonFock N)
    {C₂ C₂e G e M : ℝ} (hC : 0 ≤ C₂) (hCe : 0 ≤ C₂e) (t : Term N) :
    0 ≤ sourceConstant a S C₂ C₂e G e M t := by
  apply mul_nonneg (by positivity)
  have hd := order_bounds a.divergenceExponent_gt_two
  have hp := order_bounds a.scalarExponent_gt_two
  have hmd := mixedConstant_nonneg hC hd.1.le (by linarith only [hd.2])
  have hmp := mixedConstant_nonneg hC hp.1.le (by linarith only [hp.2])
  have hm1 := mixedConstant_nonneg hC (s := 1) (by norm_num) (by norm_num)
  have hm0 := mixedConstant_nonneg hC (s := 0) (by norm_num) (by norm_num)
  rcases t with i | i | n | n | t <;> dsimp only [componentConstant]
  · unfold coefficientNormSq
    positivity
  · exact mul_nonneg (mul_nonneg (by norm_num) (coefficientNormSq_nonneg S _ _)) hm1
  · exact mul_nonneg (mul_nonneg (by norm_num) (coefficientNormSq_nonneg S _ _)) hmd
  · exact mul_nonneg (mul_nonneg (by norm_num) (coefficientNormSq_nonneg S _ _)) hmp
  · positivity

variable (a : PfHk.PhysicalExternalCoefficients.Data N) (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M)
  (e : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0))

/-- Ordinary multiplication domains, all derived below from the coordinate
Sobolev and spectral inputs. There is no weighted estimate in this record. -/
structure Products : Prop where
  vector : ∀ i, HasMultiplier (a.vector i) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  first : ∀ i, HasMultiplier (a.vector i) (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u)
  square : ∀ i, HasMultiplier (fun x => a.vector i x ^ 2) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  divergence : ∀ n, HasMultiplier (coordinateCoefficient n (a.divergenceCoefficient n)) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  scalar : ∀ n, HasMultiplier (coordinateCoefficient n (a.scalarCoefficient n)) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  bounded : HasMultiplier a.boundedCoefficient (inclusion (Fin N × Fin 3) (fun _ => 0) u)

theorem products_of_comparison (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral) (hu : ComparisonDomain (fun _ => 0) u) :
    Products a C κ hκ M hbound e u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Classical.choose (scalar_multiplier S spectral joint (by norm_num : (2 : ℝ) < 6)
      i.1 (a.vectorCoefficient i.1 i.2) (by simpa using a.vector_memLp i.1 i.2) u hu)
  · intro i
    exact Classical.choose (covariant_coordinate_multiplier S spectral joint C κ hκ M hbound e
      i.1 i (a.vectorCoefficient i.1 i.2) (a.vector_memLp i.1 i.2) u hu)
  · intro i
    exact Classical.choose (scalar_multiplier S spectral joint (by norm_num : (2 : ℝ) < 3)
      i.1 (fun x => a.vectorCoefficient i.1 i.2 x ^ 2)
      (by simpa using square_memLp_three (a.vector_memLp i.1 i.2)) u hu)
  · intro n
    exact Classical.choose (scalar_multiplier S spectral joint a.divergenceExponent_gt_two
      n _ (a.divergence_memLp n) u hu)
  · intro n
    exact Classical.choose (scalar_multiplier S spectral joint a.scalarExponent_gt_two
      n _ (a.scalar_memLp n) u hu)
  · exact Classical.choose (bounded_multiplier _ a.bounded_memLp (inclusion (Fin N × Fin 3) (fun _ => 0) u))

def term (P : Products a C κ hκ M hbound e u) : Term N → WaveSpace (Fin N × Fin 3)
  | .inl i => roughMultiply (a.vector i) (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) (P.first i)
  | .inr (.inl i) => roughMultiply (fun x => a.vector i x ^ 2) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.square i)
  | .inr (.inr (.inl n)) => roughMultiply (coordinateCoefficient n (a.divergenceCoefficient n))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.divergence n)
  | .inr (.inr (.inr (.inl n))) => roughMultiply (coordinateCoefficient n (a.scalarCoefficient n))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.scalar n)
  | .inr (.inr (.inr (.inr _))) => roughMultiply a.boundedCoefficient
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) P.bounded

def total (P : Products a C κ hκ M hbound e u) : WaveSpace (Fin N × Fin 3) :=
  ∑ t, coefficient t • term a C κ hκ M hbound e u P t

private theorem finite_sum_ae {J X H : Type*} [Fintype J] [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (μ : Measure X)
    (c : J → ℂ) (v : J → Lp H 2 μ) :
    ((∑ j, c j • v j : Lp H 2 μ) : X → H) =ᵐ[μ]
      fun x => ∑ j, c j • v j x := by
  have h := (Lp.coeFn_finsetSum Finset.univ (fun j => c j • v j)).trans
    (eventuallyEq_sum fun j _ => Lp.coeFn_smul (c j) (v j))
  filter_upwards [h] with x hx
  simpa only [Finset.sum_apply, Pi.smul_apply] using hx

theorem total_ae (P : Products a C κ hκ M hbound e u) :
    (total a C κ hκ M hbound e u P : Configuration N → PhotonFock) =ᵐ[volume]
      fun X => ∑ t, coefficient t • term a C κ hκ M hbound e u P t X :=
  finite_sum_ae volume coefficient (term a C κ hκ M hbound e u P)

attribute [local irreducible] term

theorem term_annularSupport (P : Products a C κ hκ M hbound e u)
    {O : Configuration N} {R : ℝ}
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hsuppD : ∀ i, AnnularSupport (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) O R)
    (t : Term N) : AnnularSupport (term a C κ hκ M hbound e u P t) O R := by
  rcases t with i | i | n | n | t <;> simp only [term]
  · exact roughMultiply_annularSupport _ _ _ (hsuppD i)
  · exact roughMultiply_annularSupport _ _ _ hsupp
  · exact roughMultiply_annularSupport _ _ _ hsupp
  · exact roughMultiply_annularSupport _ _ _ hsupp
  · exact roughMultiply_annularSupport _ _ _ hsupp

theorem annularSupport_supported_ball {O : Configuration N} {R : ℝ}
    (g : WaveSpace (Fin N × Fin 3)) (hsupp : AnnularSupport g O R) :
    ∀ᵐ X ∂volume, X ∉ Metric.ball O R → g X = 0 := by
  obtain ⟨ρ, R', hρ, hρR, hR, hs⟩ := hsupp
  filter_upwards [hs] with X hx hnot
  exact hx (Or.inr (hR.trans_le (not_lt.mp hnot)))

theorem total_supported_ball (P : Products a C κ hκ M hbound e u)
    {O : Configuration N} {R : ℝ}
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hsuppD : ∀ i, AnnularSupport (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) O R) :
    ∀ᵐ X ∂volume, X ∉ Metric.ball O R → total a C κ hκ M hbound e u P X = 0 := by
  have hs : ∀ᵐ X ∂volume, ∀ t : Term N,
      X ∉ Metric.ball O R → term a C κ hκ M hbound e u P t X = 0 :=
    ae_all_iff.mpr fun t => annularSupport_supported_ball _
      (term_annularSupport a C κ hκ M hbound e u P hsupp hsuppD t)
  filter_upwards [total_ae a C κ hκ M hbound e u P, hs] with X hx hsx hnot
  exact hx.trans (Finset.sum_eq_zero fun t _ =>
    (congrArg (fun v : PhotonFock => coefficient t • v) (hsx t hnot)).trans (smul_zero _))

theorem component_source_bound
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (P : Products a C κ hκ M hbound e u)
    {O : Configuration N} (family : BufferedFamily O) {R τ α C₂ C₂e G : ℝ}
    (hR : 0 < R) (hsmall : 4 * R ≤ Real.exp (-2)) (hτ : 1 ≤ τ)
    (hα : 0 < α) (hG : Enlarged.firstWeightConstant family = G)
    (f : WaveSpace (Fin N × Fin 3))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hsuppD : ∀ i, AnnularSupport (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) O R)
    (hmixed : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂)
    (henlarged : PhysicalEnlargedFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂e)
    (σ : Term N → ℝ) (hσ : ∀ t, 0 ≤ σ t)
    (hratio : ∀ t j, radius R j ^ radiusExponent a t / dyadicBeta α R j ≤ σ t)
    (t : Term N) :
    Integrable (sourceEnergy O τ α (term a C κ hκ M hbound e u P t)) ∧
      (∫ X, sourceEnergy O τ α (term a C κ hκ M hbound e u P t) X) ≤
        (componentConstant a S C₂ C₂e G e M t * σ t * τ ^ (-parameterExponent a t)) *
          ∫ X, sourceEnergy O τ α f X := by
  have hsmall2 : 2 * R ≤ Real.exp (-2) := by linarith only [hsmall, hR]
  have hτ0 : 0 < τ := by linarith only [hτ]
  rcases t with i | i | n | n | t <;> simp only [term]
  · have hb := magnetic_source_bound C κ hκ M hbound e spectral family hR hsmall hτ hα
      (mul_nonneg (by positivity) (coefficientNormSq_nonneg S 6 (a.vectorCoefficient i.1 i.2)))
      (coefficientNormSq_nonneg S 6 (a.vectorCoefficient i.1 i.2)) (hσ (.inl i)) (a.vector i) i
      (coordinate_high_endpoint S spectral joint C κ hκ M hbound e i.1 i _ (a.vector_memLp i.1 i.2))
      (coordinate_low_endpoint S spectral joint i.1 _ (a.vector_memLp i.1 i.2))
      u f (P.first i) (hsuppD i) henlarged
      (fun j => by simpa only [radiusExponent, Real.rpow_one] using hratio (.inl i) j)
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    have hconstant := congrArg (fun z : ℝ =>
      (24 * σ (.inl i) *
        (((2 + 20 * e ^ 2 * (max M 0) ^ 2) * coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2)) *
          ((3 / 4) * C₂e + 10240) +
          z ^ 2 * coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2) * ((1 / 4) * C₂e + 30720))) *
        ∫ X, sourceEnergy O τ α f X) hG
    exact hconstant.trans (by
      simp only [componentConstant, parameterExponent, neg_zero, Real.rpow_zero, mul_one]
      ring)
  · have hep := coordinate_scalar_endpoint S spectral joint (by norm_num : (2 : ℝ) < 3) i.1
      (fun x => a.vectorCoefficient i.1 i.2 x ^ 2)
      (by simpa using square_memLp_three (a.vector_memLp i.1 i.2))
    have hep1 := (congrArg (fun s : ℝ => ScalarFractionalMultiplier spectral
      (coordinateCoefficient i.1 (fun x => a.vectorCoefficient i.1 i.2 x ^ 2)) s
      (coefficientNormSq S 3 (fun x => a.vectorCoefficient i.1 i.2 x ^ 2)))
      (show (3 : ℝ) / 3 = 1 by norm_num)).mp hep
    have hb := scalar_source_bound spectral family hR hsmall2 hτ0 hα (s := 1)
      (by norm_num) (by norm_num) (coefficientNormSq_nonneg S 3 _) (hσ (.inr (.inl i)))
      (fun x => a.vector i x ^ 2) hep1 u f (P.square i) hsupp hmixed
      (fun j => by simpa only [radiusExponent, show (4 : ℝ) - 2 * 1 = 2 by norm_num] using hratio (.inr (.inl i)) j)
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    simp only [componentConstant, parameterExponent, mixedConstant]
    norm_num only
    ring
  · have hs := order_bounds a.divergenceExponent_gt_two
    have hb := scalar_source_bound spectral family hR hsmall2 hτ0 hα hs.1.le
      (by linarith only [hs.2]) (coefficientNormSq_nonneg S _ _) (hσ (.inr (.inr (.inl n))))
      (coordinateCoefficient n (a.divergenceCoefficient n))
      (coordinate_scalar_endpoint S spectral joint a.divergenceExponent_gt_two n _ (a.divergence_memLp n))
      u f (P.divergence n) hsupp hmixed (hratio (.inr (.inr (.inl n))))
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    simp only [componentConstant, parameterExponent, mixedConstant, scalarOrder]
    ring
  · have hs := order_bounds a.scalarExponent_gt_two
    have hb := scalar_source_bound spectral family hR hsmall2 hτ0 hα hs.1.le
      (by linarith only [hs.2]) (coefficientNormSq_nonneg S _ _) (hσ (.inr (.inr (.inr (.inl n)))))
      (coordinateCoefficient n (a.scalarCoefficient n))
      (coordinate_scalar_endpoint S spectral joint a.scalarExponent_gt_two n _ (a.scalar_memLp n))
      u f (P.scalar n) hsupp hmixed (hratio (.inr (.inr (.inr (.inl n)))))
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    simp only [componentConstant, parameterExponent, mixedConstant, scalarOrder]
    ring
  · have hb := scalar_source_bound spectral family hR hsmall2 hτ0 hα (s := 0)
      (by norm_num) (by norm_num) (sq_nonneg _) (hσ (.inr (.inr (.inr (.inr t)))))
      a.boundedCoefficient (bounded_endpoint spectral _ a.bounded_memLp)
      u f P.bounded hsupp hmixed
      (fun j => by simpa only [radiusExponent, mul_zero, sub_zero] using hratio (.inr (.inr (.inr (.inr t)))) j)
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    simp only [componentConstant, parameterExponent, mixedConstant]
    norm_num only
    ring

theorem source_bound
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (P : Products a C κ hκ M hbound e u)
    {O : Configuration N} (family : BufferedFamily O) {R τ α C₂ C₂e G : ℝ}
    (hR : 0 < R) (hsmall : 4 * R ≤ Real.exp (-2)) (hτ : 1 ≤ τ)
    (hα : 0 < α) (hG : Enlarged.firstWeightConstant family = G)
    (f g : WaveSpace (Fin N × Fin 3))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hsuppD : ∀ i, AnnularSupport (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) O R)
    (hmixed : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂)
    (henlarged : PhysicalEnlargedFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂e)
    (σ : Term N → ℝ) (hσ : ∀ t, 0 ≤ σ t)
    (hratio : ∀ t j, radius R j ^ radiusExponent a t / dyadicBeta α R j ≤ σ t)
    (hoperator : (g : Configuration N → PhotonFock) =ᵐ[volume]
      fun X => ∑ t, coefficient t • term a C κ hκ M hbound e u P t X) :
    Integrable (sourceEnergy O τ α g) ∧
      (∫ X, sourceEnergy O τ α g X) ≤
        (∑ t, sourceConstant a S C₂ C₂e G e M t * σ t * τ ^ (-parameterExponent a t)) *
          ∫ X, sourceEnergy O τ α f X := by
  have hc := component_source_bound a C κ hκ M hbound e u S spectral joint P family
    hR hsmall hτ hα hG f hsupp hsuppD hmixed henlarged σ hσ hratio
  have hw : Measurable (centeredSourceWeight O τ α) := by
    unfold centeredSourceWeight CarlemanSpatialDensity.sourceWeight CarlemanWeights.weight
    fun_prop
  have hm : Integrable (sourceEnergy O τ α g) ∧
      (∫ X, sourceEnergy O τ α g X) ≤ (Fintype.card (Term N) : ℝ) *
        ∑ t, ∫ X, sourceEnergy O τ α (term a C κ hκ M hbound e u P t) X :=
    FiniteWeightedSource.source_sum_bound (μ := volume) Finset.univ coefficient
      (fun t X => term a C κ hκ M hbound e u P t X) g (centeredSourceWeight O τ α)
      (fun t _ => coefficient_norm t)
      (ae_of_all _ fun X => by unfold centeredSourceWeight CarlemanSpatialDensity.sourceWeight; positivity)
      hoperator (hw.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable g).norm.pow 2))
      (fun t _ => (hc t).1)
  have hsum : (∑ t, ∫ X, sourceEnergy O τ α (term a C κ hκ M hbound e u P t) X) ≤
      ∑ t, (componentConstant a S C₂ C₂e G e M t * σ t * τ ^ (-parameterExponent a t)) *
        ∫ X, sourceEnergy O τ α f X :=
    Finset.sum_le_sum fun t _ => (hc t).2
  refine ⟨hm.1, hm.2.trans ?_⟩
  calc
    _ ≤ (Fintype.card (Term N) : ℝ) * ∑ t,
        (componentConstant a S C₂ C₂e G e M t * σ t * τ ^ (-parameterExponent a t)) *
          ∫ X, sourceEnergy O τ α f X := by
      exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (Fintype.card (Term N)))
    _ = _ := by
      simp only [sourceConstant, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      ring

def vectorError (P : Products a C κ hκ M hbound e u) (i : Fin N × Fin 3) :
    WaveSpace (Fin N × Fin 3) :=
  roughMultiply (a.vector i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.vector i)

def kineticConstant (S : CoordinateSobolev.Data PhotonFock N) (C₂ : ℝ) : ℝ :=
  24 * (∑ i : Fin N × Fin 3, coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2)) *
    ((1 / 4) * C₂ + 4608)

theorem kineticConstant_nonneg (S : CoordinateSobolev.Data PhotonFock N) {C₂ : ℝ}
    (hC : 0 ≤ C₂) : 0 ≤ kineticConstant a S C₂ := by
  unfold kineticConstant
  have hs : 0 ≤ ∑ i : Fin N × Fin 3, coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2) :=
    Finset.sum_nonneg fun i _ => coefficientNormSq_nonneg S _ _
  positivity

theorem kinetic_components_integrable
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (P : Products a C κ hκ M hbound e u)
    {O : Configuration N} (family : BufferedFamily O) {R τ α C₂ : ℝ}
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (f : WaveSpace (Fin N × Fin 3))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hmixed : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂)
    (i : Fin N × Fin 3) :
    Integrable (fun X => positiveKineticWeight O τ α X *
      ‖vectorError a C κ hκ M hbound e u P i X‖ ^ 2) :=
  (scalar_kinetic_bound spectral family hR hsmall hτ hα hαR
    (coefficientNormSq_nonneg S 6 (a.vectorCoefficient i.1 i.2)) (a.vector i)
    (coordinate_low_endpoint S spectral joint i.1 _ (a.vector_memLp i.1 i.2))
    u f (P.vector i) hsupp hmixed).1

theorem kinetic_bound
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (P : Products a C κ hκ M hbound e u)
    {O : Configuration N} (family : BufferedFamily O) {R τ α C₂ : ℝ}
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (f : WaveSpace (Fin N × Fin 3))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hmixed : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂) :
    Integrable (fun X => positiveKineticWeight O τ α X *
      ∑ i, ‖vectorError a C κ hκ M hbound e u P i X‖ ^ 2) ∧
      (∫ X, positiveKineticWeight O τ α X *
        ∑ i, ‖vectorError a C κ hκ M hbound e u P i X‖ ^ 2) ≤
      (kineticConstant a S C₂ * (R / τ)) * ∫ X, sourceEnergy O τ α f X := by
  have hb (i : Fin N × Fin 3) := scalar_kinetic_bound spectral family hR hsmall hτ hα hαR
    (coefficientNormSq_nonneg S 6 (a.vectorCoefficient i.1 i.2)) (a.vector i)
    (coordinate_low_endpoint S spectral joint i.1 _ (a.vector_memLp i.1 i.2))
    u f (P.vector i) hsupp hmixed
  have heq : (fun X => positiveKineticWeight O τ α X *
      ∑ i, ‖vectorError a C κ hκ M hbound e u P i X‖ ^ 2) =
      fun X => ∑ i, kineticFieldEnergy O τ α (vectorError a C κ hκ M hbound e u P i) X := by
    funext X
    simp only [kineticFieldEnergy, Finset.mul_sum]
  rw [heq]
  have hi (i : Fin N × Fin 3) :
      Integrable (kineticFieldEnergy O τ α (vectorError a C κ hκ M hbound e u P i)) := (hb i).1
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hi i), ?_⟩
  calc
    _ = ∑ i : Fin N × Fin 3,
        ∫ X, kineticFieldEnergy O τ α (vectorError a C κ hκ M hbound e u P i) X :=
      integral_finsetSum Finset.univ (fun i _ => hi i)
    _ ≤ ∑ i : Fin N × Fin 3,
        (24 * coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2) * (R / τ) *
          ((1 / 4) * C₂ + 4608)) * ∫ X, sourceEnergy O τ α f X :=
      Finset.sum_le_sum fun i _ => (hb i).2
    _ = _ := by
      simp only [kineticConstant, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end PfHk.PhysicalExternalSource
