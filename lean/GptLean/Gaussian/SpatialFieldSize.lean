import GptLean.Gaussian.SpatialFieldMoments

/-! A measurable local field size and its deterministic Sobolev bound.
The size is the Euclidean sum of gradient component suprema over cluster
balls. Countable dense samples make the definition measurable for every
sample, including the exceptional set where spatial smoothness is absent. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

private instance unitBall_nonempty : Nonempty ↥(Metric.closedBall (0 : FieldSpace) 1) :=
  ⟨⟨0, by simp⟩⟩

/-- Fixed dense samples of the closed unit ball. -/
def unitBallSample (n : ℕ) : FieldSpace :=
  (TopologicalSpace.denseSeq ↥(Metric.closedBall (0 : FieldSpace) 1) n).val

/-- The local supremum, defined by countably many dense samples. -/
def localScalarSup (f : FieldSpace → ℝ) (centre : FieldSpace) (R : ℝ) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal |f (centre + R • unitBallSample n)|).toReal

theorem measurable_localScalarSup {Q : Type*} [MeasurableSpace Q]
    (f : FieldSpace → Q → ℝ) (hm : Measurable (Function.uncurry f))
    (centre : FieldSpace) (R : ℝ) :
    Measurable (fun q => localScalarSup (fun x => f x q) centre R) := by
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro n
  simpa only [Real.norm_eq_abs, Function.comp_def, Function.uncurry, id_eq] using
    ((hm.comp ((measurable_const (a := centre + R • unitBallSample n)).prodMk measurable_id)).norm).ennreal_ofReal

/-- For a continuous spatial function the countable supremum controls every
point of the closed ball in its unit-ball parameterization. -/
theorem abs_le_localScalarSup (f : FieldSpace → ℝ) (hf : Continuous f)
    (centre : FieldSpace) (R : ℝ) (z : ↥(Metric.closedBall (0 : FieldSpace) 1)) :
    |f (centre + R • z.val)| ≤ localScalarSup f centre R := by
  let h : FieldSpace → ℝ := fun y => |f (centre + R • y)|
  have hc : Continuous (fun y : FieldSpace => centre + R • y) :=
    continuous_const.add (continuous_id.const_smul R)
  have hh : Continuous h := (hf.comp hc).abs
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FieldSpace) 1).bddAbove_image hh.continuousOn
  have hfinite : (⨆ n : ℕ, ENNReal.ofReal (h (unitBallSample n))) ≠ (∞ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    exact hC ⟨unitBallSample n, (TopologicalSpace.denseSeq ↥(Metric.closedBall (0 : FieldSpace) 1) n).property, rfl⟩
  have hclosed : IsClosed {y : ↥(Metric.closedBall (0 : FieldSpace) 1) |
      h y.val ≤ localScalarSup f centre R} :=
    isClosed_le (hh.comp continuous_subtype_val) continuous_const
  apply hclosed.closure_subset_iff.mpr _ (TopologicalSpace.denseRange_denseSeq _ z)
  rintro _ ⟨n, rfl⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
  exact le_iSup (fun n => ENNReal.ofReal (h (unitBallSample n))) n

theorem abs_le_localScalarSup_of_mem_closedBall
    (f : FieldSpace → ℝ) (hf : Continuous f) (centre : FieldSpace)
    {R : ℝ} (hR : 0 < R) (x : FieldSpace) (hx : x ∈ Metric.closedBall centre R) :
    |f x| ≤ localScalarSup f centre R := by
  have hnorm : ‖x - centre‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  let z : FieldSpace := R⁻¹ • (x - centre)
  have hz : z ∈ Metric.closedBall (0 : FieldSpace) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, z, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    calc
      _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have he : centre + R • z = x := by
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    abel
  simpa only [he] using abs_le_localScalarSup f hf centre R ⟨z, hz⟩

/-- Multi-indices of orders zero through two for the local H² estimate. -/
abbrev LocalSobolevIndex := (m : Fin 3) × (Fin m.val → Fin 3)

def localSobolevList (t : LocalSobolevIndex) : List (Fin 3) := List.ofFn t.2

@[simp] theorem length_localSobolevList (t : LocalSobolevIndex) :
    (localSobolevList t).length = t.1.val := by simp [localSobolevList]

@[simp] theorem card_localSobolevIndex : Fintype.card LocalSobolevIndex = 13 := by
  decide

theorem localSobolev_term_card {I : Type*} [Fintype I] :
    Fintype.card (I × Fin 3 × LocalSobolevIndex) = 39 * Fintype.card I := by
  simp only [Fintype.card_prod, Fintype.card_fin, card_localSobolevIndex]
  omega

/-- The universal deterministic scaled local H²-to-supremum inequality
for gradients in three dimensions. This background statement contains no
Gaussian data, source state, conditional density or random moment. -/
def ScaledGradientSobolevBackground (L C : ℝ) : Prop :=
  ∀ f : List (Fin 3) → FieldSpace → ℝ,
    (∀ ds, ContDiff ℝ ∞ (f ds)) →
    (∀ ds j x, HasLineDerivAt ℝ (f ds) (f (j :: ds) x) x (EuclideanSpace.single j 1)) →
    ∀ (centre : FieldSpace) (R : ℝ), 0 < R →
      (∑ j : Fin 3, localScalarSup (f [j]) centre (L * R) ^ 2) ≤
        C * ∑ j : Fin 3, ∑ t : LocalSobolevIndex,
          R ^ (2 * (t.1.val : ℤ) - 3) *
            (∫ x in Metric.ball centre (L * R), f (localSobolevList t ++ [j]) x ^ 2)

/-- The square root of the sum of squared component suprema over the
finite cluster family. -/
def localFieldSize {I Q : Type*} [Fintype I]
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : I → FieldSpace) (R : ℝ) (q : Q) : ℝ :=
  Real.sqrt (∑ i, ∑ j : Fin 3, localScalarSup (fun x => field i [j] x q) (centre i) R ^ 2)

theorem measurable_localFieldSize {I Q : Type*} [Fintype I] [MeasurableSpace Q]
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (centre : I → FieldSpace) (R : ℝ) : Measurable (localFieldSize field centre R) := by
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (measurable_localScalarSup (field i [j]) (hm i [j]) (centre i) R).pow_const 2

theorem localFieldSize_nonneg {I Q : Type*} [Fintype I]
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : I → FieldSpace) (R : ℝ) (q : Q) :
    0 ≤ localFieldSize field centre R q := Real.sqrt_nonneg _

/-- Every gradient component on every cluster ball is controlled by the
same measurable field size. -/
theorem localScalarSup_le_localFieldSize {I Q : Type*} [Fintype I]
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : I → FieldSpace) (R : ℝ) (q : Q) (i : I) (j : Fin 3) :
    localScalarSup (fun x => field i [j] x q) (centre i) R ≤
      localFieldSize field centre R q := by
  classical
  have h1 := Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    sq_nonneg (localScalarSup (fun x => field i [a] x q) (centre i) R)) (Finset.mem_univ j)
  have h2 := Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset I)) =>
    Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
      sq_nonneg (localScalarSup (fun x => field a [b] x q) (centre a) R))) (Finset.mem_univ i)
  have hz : localFieldSize field centre R q ^ 2 =
      ∑ a, ∑ b : Fin 3, localScalarSup (fun x => field a [b] x q) (centre a) R ^ 2 := by
    apply Real.sq_sqrt
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hn : 0 ≤ localScalarSup (fun x => field i [j] x q) (centre i) R :=
    ENNReal.toReal_nonneg
  have hZ := localFieldSize_nonneg field centre R q
  nlinarith [h1.trans h2]

theorem localFieldSize_controls_component {I Q : Type*} [Fintype I]
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : I → FieldSpace) (R : ℝ) (q : Q) (i : I) (j : Fin 3)
    (hf : Continuous (fun x => field i [j] x q))
    (z : ↥(Metric.closedBall (0 : FieldSpace) 1)) :
    |field i [j] (centre i + R • z.val) q| ≤ localFieldSize field centre R q :=
  (abs_le_localScalarSup _ hf (centre i) R z).trans
    (localScalarSup_le_localFieldSize field centre R q i j)

theorem localFieldSize_controls_component_on_ball {I Q : Type*} [Fintype I]
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (centre : I → FieldSpace) {R : ℝ} (hR : 0 < R) (q : Q) (i : I) (j : Fin 3)
    (hf : Continuous (fun x => field i [j] x q))
    (x : FieldSpace) (hx : x ∈ Metric.closedBall (centre i) R) :
    |field i [j] x q| ≤ localFieldSize field centre R q :=
  (abs_le_localScalarSup_of_mem_closedBall _ hf (centre i) hR x hx).trans
    (localScalarSup_le_localFieldSize field centre R q i j)

/-- Applying the deterministic inequality to the actual smooth paths gives
the source-weighted Sobolev inequality. The source mass is arbitrary here,
so this step assumes no conditional field estimate. -/
theorem weighted_localFieldSize_sobolev {I Q : Type*} [Fintype I]
    [MeasurableSpace Q] {μ : Measure Q}
    {L C R : ℝ} (sobolev : ScaledGradientSobolevBackground L C) (hR : 0 < R)
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (hsmooth : ∀ᵐ q ∂μ, ∀ i,
      (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
        (field i (j :: ds) x q) x (EuclideanSpace.single j 1)))
    (centre : I → FieldSpace) (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q) :
    ∀ᵐ q ∂μ, p q * localFieldSize field centre (L * R) q ^ 2 ≤
      C * ∑ i, ∑ j : Fin 3, ∑ t : LocalSobolevIndex,
        R ^ (2 * (t.1.val : ℤ) - 3) *
          (∫ x in Metric.ball (centre i) (L * R),
            p q * field i (localSobolevList t ++ [j]) x q ^ 2) := by
  classical
  filter_upwards [hsmooth] with q hq
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    sobolev (fun ds x => field i ds x q) (hq i).1 (hq i).2 (centre i) R hR)
  have hz : localFieldSize field centre (L * R) q ^ 2 =
      ∑ i, ∑ j : Fin 3, localScalarSup (fun x => field i [j] x q) (centre i) (L * R) ^ 2 := by
    apply Real.sq_sqrt
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [hz]
  have h := mul_le_mul_of_nonneg_left hsum (hp q)
  simp_rw [integral_const_mul]
  simpa only [← Finset.mul_sum, mul_left_comm, mul_assoc] using h

namespace KernelFieldData

variable {I Q H K G Ω : Type*} [Fintype I]
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

omit [SFinite μ] in
/-- Uniform cutoff norm bounds give a source coefficient depending only
on the radiation energy and total source mass. -/
theorem cutoffSourceCoefficient_le_uniform
    (momentum : Ω → FieldSpace) (k a b : ℝ) (base : Ω → ℂ) (ψ : ℕ → H)
    (hA : (∫ y, w y * ‖softBase momentum k base y‖ ^ 2 ∂ν) ≤ a ^ 2)
    (hB : (∫ y, ‖softBase momentum k base y‖ ^ 2 ∂ν) ≤ b ^ 2) :
    D.cutoffSourceCoefficient momentum k base ψ ≤
      8 * (a ^ 2 * (∑' n, ‖D.radiation (ψ n)‖ ^ 2) +
        b ^ 2 * (∑' n, ‖ψ n‖ ^ 2)) := by
  have hE : 0 ≤ ∑' n, ‖D.radiation (ψ n)‖ ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  have hP : 0 ≤ ∑' n, ‖ψ n‖ ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  unfold cutoffSourceCoefficient
  have h1 := mul_le_mul_of_nonneg_right hA hE
  have h2 := mul_le_mul_of_nonneg_right hB hP
  have hb := mul_nonneg (sq_nonneg b) hP
  nlinarith

/-- The actual measurable local supremum has its conditional second moment
bound from kernels, WIS source moments, and a universal deterministic local
Sobolev inequality. No source-weighted Sobolev or integrated-moment estimate
is an input. The smooth-path and modification conclusions are supplied by
`exists_smooth_soft_field`. -/
theorem localFieldSize_moment_from_kernels
    (momentum : Ω → FieldSpace) {k L R C : ℝ}
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hR : 0 < R) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (sobolev : ScaledGradientSobolevBackground L C)
    (centre : I → FieldSpace) (base : I → Ω → ℂ)
    (label : I → List (Fin 3) → FieldSpace → G)
    (hkernel : ∀ i ds x,
      D.kernel (label i ds x) = softDerivativeKernel momentum ds k x (base i))
    (hbaseA : ∀ i, Integrable (fun y => w y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hbaseB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hmA : ∀ i ds x, AEStronglyMeasurable
      (fun y => w y * ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hmB : ∀ i ds x, AEStronglyMeasurable
      (fun y => ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (heq : ∀ i ds x, field i ds x =ᵐ[μ] W.coordinate (label i ds x))
    (hsmooth : ∀ᵐ q ∂μ, ∀ i,
      (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
        (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) :
    Integrable (fun q => W.sourceMass ψ q * localFieldSize field centre (L * R) q ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * localFieldSize field centre (L * R) q ^ 2 ∂μ) ≤
      C * (Fintype.card (I × Fin 3 × LocalSobolevIndex) : ℝ) * k ^ 2 *
        ((Real.pi * 4 / 3) * L ^ 3 *
          ∑ a : I × Fin 3 × LocalSobolevIndex,
            D.cutoffSourceCoefficient momentum k (base a.1) ψ) := by
  classical
  let ord := fun a : I × Fin 3 × LocalSobolevIndex => a.2.2.1.val
  let ds := fun a : I × Fin 3 × LocalSobolevIndex => localSobolevList a.2.2 ++ [a.2.1]
  let A : ℝ := (Real.pi * 4 / 3) * L ^ 3
  let B : ℝ := A * ∑ a : I × Fin 3 × LocalSobolevIndex,
    D.cutoffSourceCoefficient momentum k (base a.1) ψ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoef := fun i => D.cutoffSourceCoefficient_nonneg momentum k (base i) ψ
  have hB : 0 ≤ B := mul_nonneg hA (Finset.sum_nonneg (fun a _ => hcoef a.1))
  have hball (a : I × Fin 3 × LocalSobolevIndex) :=
    D.derivative_ball_moment_of_modification momentum (ds a) hk hL hR.le (centre a.1)
      (base a.1) (label a.1 (ds a)) (hkernel a.1 (ds a)) (hbaseA a.1) (hbaseB a.1)
      (hmA a.1 (ds a)) (hmB a.1 (ds a)) ψ hdom hE hP
      (field a.1 (ds a)) (hm a.1 (ds a)) (heq a.1 (ds a))
  apply integrated_scaled_sobolev ord
    (fun a q => ∫ x in Metric.ball (centre a.1) (L * R),
      W.sourceMass ψ q * field a.1 (ds a) x q ^ 2)
    hC hR hB (mul_nonneg hk hR.le) hkR
    ((W.sourceMass_integrable hP).aestronglyMeasurable.mul
      ((measurable_localFieldSize field hm centre (L * R)).stronglyMeasurable.aestronglyMeasurable.pow 2))
    (Eventually.of_forall (fun q => mul_nonneg (W.sourceMass_nonneg ψ q) (sq_nonneg _)))
    (fun a => (hball a).1)
  · have hs := weighted_localFieldSize_sobolev sobolev hR field hsmooth
      centre (W.sourceMass ψ) (W.sourceMass_nonneg ψ)
    simpa only [Fintype.sum_prod_type, ord, ds, Pi.mul_apply, Pi.pow_apply] using hs
  · intro a
    have hterm : D.cutoffSourceCoefficient momentum k (base a.1) ψ ≤
        ∑ b : I × Fin 3 × LocalSobolevIndex,
          D.cutoffSourceCoefficient momentum k (base b.1) ψ :=
      Finset.single_le_sum (fun b _ => hcoef b.1) (Finset.mem_univ a)
    have hbound := (hball a).2
    have hord : (ds a).length = ord a + 1 := by simp [ds, ord]
    rw [hord, show 2 * (ord a + 1) = 2 * ord a + 2 by omega] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hterm hA)
      (mul_nonneg (zpow_nonneg hR.le _) (pow_nonneg hk _)))

/-- A cardinal cap makes the local field moment constant uniform over
localization cells. The constant depends only on the cap and deterministic
Sobolev/ball constants, while the state enters through its actual radiation
energy and mass. -/
theorem localFieldSize_uniform_moment_from_kernels
    (momentum : Ω → FieldSpace) {k L R C : ℝ}
    (a b : ℝ) (M : ℕ)
    (hcard : Fintype.card (I × Fin 3 × LocalSobolevIndex) ≤ M)
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hR : 0 < R) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (sobolev : ScaledGradientSobolevBackground L C)
    (centre : I → FieldSpace) (base : I → Ω → ℂ)
    (label : I → List (Fin 3) → FieldSpace → G)
    (hkernel : ∀ i ds x,
      D.kernel (label i ds x) = softDerivativeKernel momentum ds k x (base i))
    (hbaseA : ∀ i, Integrable (fun y => w y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hbaseB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hmA : ∀ i ds x, AEStronglyMeasurable
      (fun y => w y * ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hmB : ∀ i ds x, AEStronglyMeasurable
      (fun y => ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hcutA : ∀ i, (∫ y, w y * ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ a ^ 2)
    (hcutB : ∀ i, (∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ b ^ 2)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (heq : ∀ i ds x, field i ds x =ᵐ[μ] W.coordinate (label i ds x))
    (hsmooth : ∀ᵐ q ∂μ, ∀ i,
      (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
        (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) :
    Integrable (fun q => W.sourceMass ψ q * localFieldSize field centre (L * R) q ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * localFieldSize field centre (L * R) q ^ 2 ∂μ) ≤
      (8 * C * (M : ℝ) ^ 2 * ((Real.pi * 4 / 3) * L ^ 3)) * k ^ 2 *
        (a ^ 2 * (∑' n, ‖D.radiation (ψ n)‖ ^ 2) + b ^ 2 * (∑' n, ‖ψ n‖ ^ 2)) := by
  classical
  obtain ⟨hi, hb⟩ := D.localFieldSize_moment_from_kernels momentum hk hL hR hC hkR
    sobolev centre base label hkernel hbaseA hbaseB hmA hmB ψ hdom hE hP field hm heq hsmooth
  refine ⟨hi, hb.trans ?_⟩
  let A : ℝ := (Real.pi * 4 / 3) * L ^ 3
  let B : ℝ := a ^ 2 * (∑' n, ‖D.radiation (ψ n)‖ ^ 2) + b ^ 2 * (∑' n, ‖ψ n‖ ^ 2)
  let n : ℝ := Fintype.card (I × Fin 3 × LocalSobolevIndex)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hnc : n ≤ (M : ℝ) := by
    dsimp [n]
    exact_mod_cast hcard
  have hs : (∑ z : I × Fin 3 × LocalSobolevIndex,
      D.cutoffSourceCoefficient momentum k (base z.1) ψ) ≤ n * (8 * B) := by
    calc
      _ ≤ ∑ _z : I × Fin 3 × LocalSobolevIndex, 8 * B :=
        Finset.sum_le_sum (fun z _ => D.cutoffSourceCoefficient_le_uniform
          momentum k a b (base z.1) ψ (hcutA z.1) (hcutB z.1))
      _ = _ := by simp [n]
  change C * n * k ^ 2 * (A * _) ≤ (8 * C * (M : ℝ) ^ 2 * A) * k ^ 2 * B
  calc
    _ ≤ C * n * k ^ 2 * (A * (n * (8 * B))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hA)
        (mul_nonneg (mul_nonneg hC hn) (sq_nonneg k))
    _ = (8 * C * A * k ^ 2 * B) * n ^ 2 := by ring
    _ ≤ (8 * C * A * k ^ 2 * B) * (M : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hnc 2) (by positivity)
    _ = _ := by ring

end KernelFieldData

end GptLean.Gaussian
