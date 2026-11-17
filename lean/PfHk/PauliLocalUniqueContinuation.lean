import PfHk.PauliCutoffCarlemanPassage
import PfHk.PauliEnergyInfiniteOrder
import PfHk.PhysicalCutoffCommutatorLimit

/-! Local unique continuation for the actual Pauli spinor. The finite
spin sum combines the orbital cutoff errors, while the weak equation
and Carleman estimate remain coupled. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliOperatorCarleman

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference
  PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds
  PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCarlemanInput PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace GptLean.PhysicalPFReference.inclusion
  PhysicalPFScalarMultiplier.multiply externalCovariant

variable {N : ℕ} [Nonempty (Fin N × Fin 3)]
variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

/-- Infinite-order decay of the spin-summed mass forces local vanishing.
The Caccioppoli estimate supplies all inner-error decay. -/
theorem flat_implies_zero_ball {E R α τ₀ K : ℝ} {O : Configuration N}
    (hCarleman : CarlemanAt F χ C e A v c hc E O R α τ₀ K)
    (hα : 0 < α) (hR : 0 < R)
    (hRsmall : R ≤ Real.exp (-2)) (hK : 0 ≤ K)
    (hcoef : ∀ r, 0 < r → r ≤ R / 4 →
      1 ≤ CarlemanWeights.beta α (-Real.log r) * r ^ (-2 : ℝ))
    {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    (hflat : InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O)) :
    ∀ᵐ X ∂volume.restrict (Metric.ball O (R / 4)), PauliReference.wave u X = 0 := by
  classical
  let family := Classical.choice (exists_buffered_family O)
  let a := family.cutoff (R / 2)
  let G := (Fintype.card (Fin N × Fin 3) : ℝ) * family.firstBound ^ 2
  let L := ((Fintype.card (Fin N × Fin 3) : ℝ) * family.secondBound) ^ 2
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ L := sq_nonneg _
  have hg (r : ℝ) (hr : 0 < r) (X : Configuration N) :
      (∑ i, (family.cutoff r).scalar.gradient i X ^ 2) ≤ G / r ^ 2 :=
    sum_gradient_sq_bound _ family.first_nonneg hr (family.first r hr) X
  have hl (r : ℝ) (hr : 0 < r) (X : Configuration N) :
      laplacian (family.cutoff r) X ^ 2 ≤ L / r ^ 4 :=
    sum_second_gradient_sq_bound _ family.second_nonneg hr (family.second r hr) X
  have hsg (r : ℝ) (hr : 0 < r) (X : Configuration N)
      (hX : X ∉ Metric.ball O (2 * r) \ Metric.ball O r) :
      ∀ i, (family.cutoff r).scalar.gradient i X = 0 :=
    (buffered_derivatives_supported _ hr (family.weight r hr) X hX).1
  have hsl (r : ℝ) (hr : 0 < r) (X : Configuration N)
      (hX : X ∉ Metric.ball O (2 * r) \ Metric.ball O r) :
      laplacian (family.cutoff r) X = 0 :=
    Finset.sum_eq_zero fun i _ =>
      (buffered_derivatives_supported _ hr (family.weight r hr) X hX).2 i i
  let ε : ℕ → ℝ := fun n => (R / 4) / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεR (n : ℕ) : ε n ≤ R / 4 := by
    exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; nlinarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R / 4)
  have hεgt : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε⟩
  let b := fun n => family.cutoff (ε n)
  let D := physicalDomain A v c hc u
  let comp := fun η => PauliLocalCutoffRules.commutator C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    (vector A) (positive v c) (negative v c) η u D
  let Gout := G / (R / 2) ^ 2
  let Lout := L / (R / 2) ^ 4
  have hdouble : 2 * (R / 2) = R := by ring
  let Bout := fun s : SpinIndex N => R ^ 2 *
    (2 * Gout * (∑ i, massOn (Metric.ball O R)
      (externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
        (negative v c) (u s) (D s) i)) +
      (1 / 2 : ℝ) * Lout * massOn (Metric.ball O R)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
  have hGout : 0 ≤ Gout := div_nonneg hG (sq_nonneg _)
  have hLout : 0 ≤ Lout := div_nonneg hL (pow_nonneg (half_pos hR).le _)
  have hBout (s : SpinIndex N) : 0 ≤ Bout s := by
    dsimp only [Bout]
    exact mul_nonneg (sq_nonneg _) (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hGout)
        (Finset.sum_nonneg fun _ _ => massOn_nonneg _ _))
      (mul_nonneg (mul_nonneg (by norm_num) hLout) (massOn_nonneg _ _)))
  have hsga : ∀ X, X ∉ Metric.ball O R \ Metric.ball O (R / 2) →
      ∀ i, a.scalar.gradient i X = 0 := by
    simpa only [hdouble] using hsg (R / 2) (half_pos hR)
  have hsla : ∀ X, X ∉ Metric.ball O R \ Metric.ball O (R / 2) → laplacian a X = 0 := by
    simpa only [hdouble] using hsl (R / 2) (half_pos hR)
  have hremoved (τ : ℝ) (hτ : max τ₀ 1 ≤ τ) :
      (∫⁻ X in Metric.ball O (R / 4), ENNReal.ofReal
        (UniqueContinuation.radialMassIntegrand (fun X => dist X O) (PauliReference.wave u) α τ X)) ≤
      ENNReal.ofReal ((2 * K * ∑ s, Bout s) * Real.exp
        (2 * τ * CarlemanWeights.weight α (-Real.log (R / 2)))) := by
    have hτ0 : 0 ≤ τ := zero_le_one.trans ((le_max_right _ _).trans hτ)
    let w := fun X : Configuration N =>
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist X O))) * dist X O ^ 2
    have hoi (s : SpinIndex N) : Integrable (fun X => w X * ‖comp a s X‖ ^ 2) :=
      annular_commutator_integrable (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        (vector A) (positive v c) (negative v c) a (u s) (D s) O
        hα hτ0 (half_pos hR) (by simpa only [hdouble] using hRsmall) hGout hLout
        (hg (R / 2) (half_pos hR)) (hl (R / 2) (half_pos hR))
        (hsg (R / 2) (half_pos hR)) (hsl (R / 2) (half_pos hR))
    have hii (n : ℕ) (s : SpinIndex N) : Integrable (fun X => w X * ‖comp (b n) s X‖ ^ 2) :=
      annular_commutator_integrable (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        (vector A) (positive v c) (negative v c) (b n) (u s) (D s) O
        hα hτ0 (hε n) (by linarith [hεR n])
        (G := G / ε n ^ 2) (L := L / ε n ^ 4) (by positivity) (by positivity)
        (hg (ε n) (hε n)) (hl (ε n) (hε n))
        (hsg (ε n) (hε n)) (hsl (ε n) (hε n))
    have hob (s : SpinIndex N) : (∫ X, w X * ‖comp a s X‖ ^ 2) ≤
        Bout s * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (R / 2))) :=
      outer_annulus_commutator_bound (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        (vector A) (positive v c) (negative v c) a (u s) (D s) O
        hα hτ0 hR hRsmall hGout hLout
        (hg (R / 2) (half_pos hR)) (hl (R / 2) (half_pos hR)) hsga hsla
    have hlim (s : SpinIndex N) : Tendsto (fun n => ∫ X, w X * ‖comp (b n) s X‖ ^ 2)
        atTop (𝓝 0) :=
      (inner_commutator_tendsto (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        (vector A) (positive v c) (negative v c) family.cutoff (u s) (D s) O
        hα hτ0 hG hL (half_pos hR) (by simpa only [hdouble] using hRsmall)
        (fun r hr _ => hg r hr) (fun r hr _ => hl r hr)
        (fun r hr _ => hsg r hr) (fun r hr _ => hsl r hr)
        (PauliInfiniteOrder.component_mass_flat_of_mass_flat hflat s)
        (PauliInfiniteOrder.component_covariant_energy_flat_of_mass_flat
          C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
          (profile_bound F χ 0) e A v c hc heigen hflat s)).comp hεgt
    have hsumlim : Tendsto (fun n => ∑ s, ∫ X, w X * ‖comp (b n) s X‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun s _ => hlim s)
    have hbundledlim : Tendsto (fun n => ∫ X, sourceIntegrand O α τ
        (commutator F χ C e A v c hc (b n) u) X) atTop (𝓝 0) :=
      hsumlim.congr' (Eventually.of_forall fun n => (weighted_bundle_integral w (comp (b n)) (hii n)).symm)
    have hbundledbound : (∫ X, sourceIntegrand O α τ
        (commutator F χ C e A v c hc a u) X) ≤
        (∑ s, Bout s) * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (R / 2))) :=
      (weighted_bundle_integral w (comp a) hoi).le.trans
        ((Finset.sum_le_sum (fun s _ => hob s)).trans_eq (Finset.sum_mul _ _ _).symm)
    have hh := remove_annular_cutoff F χ C e A v c hc hCarleman hK
      ((le_max_left _ _).trans hτ) hR family ε hε hεR hεlim heigen
      (weighted_bundle_integrable w (comp a) hoi)
      (fun n => weighted_bundle_integrable w (comp (b n)) (hii n))
      hbundledbound hbundledlim
    exact hh.trans_eq (congrArg ENNReal.ofReal (by ring))
  apply UniqueContinuation.ae_zero_of_radial_lintegral_outer_error hα
    (by positivity : 0 < R / 4) (by linarith : R / 4 < R / 2)
    (by linarith : R / 2 ≤ Real.exp (-2))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK)
      (Finset.sum_nonneg (fun s _ => hBout s)))
    (r := fun X => dist X O) (τ₀ := τ₀)
  · have hnot : ∀ᵐ X : Configuration N ∂volume, X ≠ O := by
      simpa only [Set.mem_singleton_iff] using
        (measure_eq_zero_iff_ae_notMem.mp (measure_singleton O))
    filter_upwards [ae_restrict_of_ae hnot,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with X hX hXB
    exact ⟨dist_pos.mpr hX, hXB⟩
  · exact hcoef
  · exact (Lp.memLp (PauliReference.wave u)).norm.integrable_sq.integrableOn
  · intro τ _
    exact (UniqueContinuation.radialMassIntegrand_measurable
      (Lp.stronglyMeasurable (PauliReference.wave u)).norm.measurable
      (continuous_id.dist continuous_const).measurable α τ).aestronglyMeasurable
  · exact hremoved

end PfHk.PauliOperatorCarleman
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
