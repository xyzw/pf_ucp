import PfHk.HydrogenOrbital
import GptLean.ElectronicH1Complex
import GptLean.ElectronicH1Reindex
import GptLean.Repair.CovariantProduct
import GptLean.SymmetricLift.SobolevRemovability
import GptLean.SymmetricLift.MetricGeometry

/-! The hydrogen orbital belongs to the actual weak H1 graph. The point
singularity in its classical derivative creates no distributional term,
because almost every coordinate line avoids the origin. -/

noncomputable section
namespace PfHk.HydrogenOrbital

open MeasureTheory Filter Set GptLean GptLean.SymmetricLift
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def derivative (Z : ℝ) (j : Fin 3) (x : Space) : ℝ :=
  (-Z * x j / ‖x‖) * orbital Z x

private theorem norm_hasFDerivAt {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (Real.hasDerivAt_sqrt (pow_ne_zero 2 hn)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  convert h using 1 <;> try rfl
  · funext y
    exact (Real.sqrt_sq (norm_nonneg y)).symm
  · ext y
    simp only [smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]
    field_simp [hn]
    simp [two_smul, mul_two]

theorem hasLineDerivAt_orbital (Z : ℝ) (j : Fin 3) {x : Space} (hx : x ≠ 0) :
    HasLineDerivAt ℝ (orbital Z) (derivative Z j x) x (EuclideanSpace.single j 1) := by
  have h := (((norm_hasFDerivAt hx).const_mul (-Z)).exp.const_mul
    (Real.sqrt (Z ^ 3 / Real.pi))).hasLineDerivAt (EuclideanSpace.single j 1)
  convert h using 1 <;> try rfl
  simp only [smul_apply, smul_eq_mul,
    EuclideanSpace.inner_single_right, innerSL_apply_apply, conj_trivial, one_mul]
  unfold derivative orbital
  ring

theorem derivative_bound {Z : ℝ} (hZ : 0 < Z) (j : Fin 3) (x : Space) :
    ‖derivative Z j x‖ ≤ Z * ‖orbital Z x‖ := by
  rw [derivative, norm_mul, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
    abs_of_pos hZ, abs_of_nonneg (norm_nonneg x)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    Z * |x j| / ‖x‖ = Z * (|x j| / ‖x‖) := by ring
    _ ≤ Z * 1 := mul_le_mul_of_nonneg_left
      (div_le_one_of_le₀ (PiLp.norm_apply_le x j) (norm_nonneg x)) hZ.le
    _ = Z := mul_one _

theorem derivative_measurable (Z : ℝ) (j : Fin 3) : Measurable (derivative Z j) := by
  unfold derivative orbital
  fun_prop

theorem derivative_memLp {Z : ℝ} (hZ : 0 < Z) (j : Fin 3) :
    MemLp (derivative Z j) 2 volume :=
  (orbital_memLp hZ).of_le_mul (derivative_measurable Z j).aestronglyMeasurable
    (ae_of_all _ (derivative_bound hZ j))

theorem sum_derivative_sq {Z : ℝ} (hZ : 0 < Z) {x : Space} (hx : x ≠ 0) :
    (∑ j : Fin 3, derivative Z j x ^ 2) = Z ^ 2 * density Z x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : (∑ j : Fin 3, x j ^ 2) = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  calc
    _ = (Z ^ 2 * orbital Z x ^ 2 / ‖x‖ ^ 2) * ∑ j : Fin 3, x j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold derivative
      ring
    _ = Z ^ 2 * density Z x := by
      rw [hnorm, div_mul_cancel₀ _ (pow_ne_zero 2 hn), orbital_sq hZ.le]

theorem integral_sum_derivative_sq {Z : ℝ} (hZ : 0 < Z) :
    (∫ x, ∑ j : Fin 3, derivative Z j x ^ 2) = Z ^ 2 := by
  calc
    _ = ∫ x, Z ^ 2 * density Z x := by
      apply integral_congr_ae
      filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
      exact sum_derivative_sq hZ hx
    _ = Z ^ 2 := by rw [integral_const_mul, integral_density hZ, mul_one]

private theorem ae_regular_coordinate_line (i : Fin 3) :
    ∀ᵐ x : Space ∂volume,
      regularLine ({0}ᶜ : Set Space) (EuclideanSpace.single i 1) x := by
  obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := exists_ne i
  have hj : ∀ᵐ x : Space ∂volume, x j ≠ 0 :=
    (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) j 0)
  filter_upwards [hj] with x hx
  intro t
  change x + t • EuclideanSpace.single i 1 ≠ 0
  intro h
  have hh := congrArg (fun y : Space => y j) h
  apply hx
  simpa [PiLp.add_apply, PiLp.smul_apply, hji] using hh

theorem weakH1 {Z : ℝ} (hZ : 0 < Z) :
    HasWeakH1Local (orbital Z) (derivative Z) := by
  refine ⟨fun K _ => (orbital_memLp hZ).restrict K,
    fun j K _ => (derivative_memLp hZ j).restrict K, ?_⟩
  intro j φ hφ hs
  have hφmem : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have hdφmem : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ _)
  apply integral_smul_lineDeriv_eq_neg_of_ae_regularLine (ae_regular_coordinate_line j)
  · intro x hx
    exact hasLineDerivAt_orbital Z j (by simpa using hx)
  · intro x
    exact ((hφ.differentiable (by simp) x).hasFDerivAt).hasLineDerivAt _
  · exact hdφmem.integrable_mul (orbital_memLp hZ)
  · exact hφmem.integrable_mul (derivative_memLp hZ j)
  · exact hφmem.integrable_mul (orbital_memLp hZ)

def scalarH1 (Z : ℝ) (hZ : 0 < Z) : ElectronicH1Complex.ComplexH1 ℂ (Fin 3) :=
  ElectronicH1Complex.realEquiv.symm
    (ElectronicH1Space.ofFunctions (fun x => (orbital Z x : ℂ))
      (fun j x => (derivative Z j x : ℂ))
      (Complex.ofRealCLM.comp_memLp' (orbital_memLp hZ))
      (fun j => Complex.ofRealCLM.comp_memLp' (derivative_memLp hZ j))
      (Repair.weakH1Local_map Complex.ofRealCLM (weakH1 hZ)))

theorem scalarH1_value (Z : ℝ) (hZ : 0 < Z) :
    (ElectronicH1Complex.value (scalarH1 Z hZ) : Space → ℂ) =ᵐ[volume]
      fun x => (orbital Z x : ℂ) :=
  (Complex.ofRealCLM.comp_memLp' (orbital_memLp hZ)).coeFn_toLp

theorem scalarH1_derivative (Z : ℝ) (hZ : 0 < Z) (j : Fin 3) :
    (ElectronicH1Complex.derivative j (scalarH1 Z hZ) : Space → ℂ) =ᵐ[volume]
      fun x => (derivative Z j x : ℂ) :=
  (Complex.ofRealCLM.comp_memLp' (derivative_memLp hZ j)).coeFn_toLp

theorem scalarH1_value_norm (Z : ℝ) (hZ : 0 < Z) :
    ‖ElectronicH1Complex.value (scalarH1 Z hZ)‖ = 1 := by
  let v := ElectronicH1Complex.value (scalarH1 Z hZ)
  have hs : ‖v‖ ^ 2 = 1 := by
    calc
      _ = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
      _ = ∫ x, inner ℝ (v x) (v x) := L2.inner_def _ _
      _ = ∫ x, orbital Z x ^ 2 := by
        apply integral_congr_ae
        filter_upwards [scalarH1_value Z hZ] with x hx
        rw [show v x = (orbital Z x : ℂ) from hx, real_inner_self_eq_norm_sq]
        simp
      _ = 1 := integral_orbital_sq hZ
  nlinarith [norm_nonneg v]

theorem scalarH1_derivative_norm_sq (Z : ℝ) (hZ : 0 < Z) (j : Fin 3) :
    ‖ElectronicH1Complex.derivative j (scalarH1 Z hZ)‖ ^ 2 =
      ∫ x, derivative Z j x ^ 2 := by
  let v := ElectronicH1Complex.derivative j (scalarH1 Z hZ)
  calc
    _ = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
    _ = ∫ x, inner ℝ (v x) (v x) := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [scalarH1_derivative Z hZ j] with x hx
      rw [show v x = (derivative Z j x : ℂ) from hx, real_inner_self_eq_norm_sq]
      simp

theorem scalarH1_kinetic_norms (Z : ℝ) (hZ : 0 < Z) :
    (∑ j : Fin 3, ‖ElectronicH1Complex.derivative j (scalarH1 Z hZ)‖ ^ 2) = Z ^ 2 := by
  simp_rw [scalarH1_derivative_norm_sq]
  rw [← integral_finsetSum _ (fun j _ => (derivative_memLp hZ j).integrable_sq)]
  exact integral_sum_derivative_sq hZ

theorem paramagnetic_current_zero (Z : ℝ) (j : Fin 3) (x : Space) :
    (starRingEnd ℂ (orbital Z x : ℂ) * (derivative Z j x : ℂ)).im = 0 := by
  simp

def oneParticleIndex : Fin 3 ≃ (Fin 1 × Fin 3) where
  toFun j := (0, j)
  invFun j := j.2
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨i, j⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

theorem oneParticle_coordinates (X : Configuration 1) :
    (ElectronicH1Reindex.coordinates oneParticleIndex).symm X = particle X 0 := by
  ext j
  rfl

def oneParticleH1 (Z : ℝ) (hZ : 0 < Z) :
    ElectronicH1Complex.ComplexH1 ℂ (Fin 1 × Fin 3) :=
  ElectronicH1Complex.realEquiv.symm
    (ElectronicH1Reindex.reindex oneParticleIndex
      (ElectronicH1Complex.realEquiv (scalarH1 Z hZ)))

theorem oneParticleH1_value (Z : ℝ) (hZ : 0 < Z) :
    (ElectronicH1Complex.value (oneParticleH1 Z hZ) : Configuration 1 → ℂ) =ᵐ[volume]
      fun X => (orbital Z (particle X 0) : ℂ) := by
  have hv := (ElectronicH1Reindex.coordinates oneParticleIndex).symm.measurePreserving
    |>.quasiMeasurePreserving.ae (scalarH1_value Z hZ)
  filter_upwards [ElectronicH1Reindex.pull_ae oneParticleIndex
    (ElectronicH1Complex.value (scalarH1 Z hZ)), hv] with X hX hφ
  exact hX.trans (hφ.trans (congrArg (fun x => (orbital Z x : ℂ)) (oneParticle_coordinates X)))

theorem oneParticleH1_derivative (Z : ℝ) (hZ : 0 < Z) (j : Fin 1 × Fin 3) :
    (ElectronicH1Complex.derivative j (oneParticleH1 Z hZ) : Configuration 1 → ℂ) =ᵐ[volume]
      fun X => (derivative Z j.2 (particle X 0) : ℂ) := by
  have hv := (ElectronicH1Reindex.coordinates oneParticleIndex).symm.measurePreserving
    |>.quasiMeasurePreserving.ae (scalarH1_derivative Z hZ j.2)
  filter_upwards [ElectronicH1Reindex.pull_ae oneParticleIndex
    (ElectronicH1Complex.derivative j.2 (scalarH1 Z hZ)), hv] with X hX hφ
  exact hX.trans (hφ.trans (congrArg (fun x => (derivative Z j.2 x : ℂ))
    (oneParticle_coordinates X)))

theorem oneParticleH1_value_norm (Z : ℝ) (hZ : 0 < Z) :
    ‖ElectronicH1Complex.value (oneParticleH1 Z hZ)‖ = 1 := by
  change ‖ElectronicH1Reindex.pull oneParticleIndex
    (ElectronicH1Complex.value (scalarH1 Z hZ))‖ = 1
  rw [(ElectronicH1Reindex.pull oneParticleIndex).norm_map, scalarH1_value_norm]

theorem oneParticleH1_kinetic_norms (Z : ℝ) (hZ : 0 < Z) :
    (∑ j : Fin 1 × Fin 3,
      ‖ElectronicH1Complex.derivative j (oneParticleH1 Z hZ)‖ ^ 2) = Z ^ 2 := by
  rw [← oneParticleIndex.sum_comp]
  change (∑ j : Fin 3, ‖ElectronicH1Reindex.pull oneParticleIndex
    (ElectronicH1Complex.derivative j (scalarH1 Z hZ))‖ ^ 2) = Z ^ 2
  simp only [(ElectronicH1Reindex.pull oneParticleIndex).norm_map]
  exact scalarH1_kinetic_norms Z hZ

theorem oneParticle_integral_density_div_norm {Z : ℝ} (hZ : 0 < Z) :
    (∫ X : Configuration 1, density Z (particle X 0) / ‖particle X 0‖) = Z := by
  simp_rw [← oneParticle_coordinates]
  exact ((ElectronicH1Reindex.coordinates oneParticleIndex).symm.measurePreserving.integral_comp
    (ElectronicH1Reindex.coordinates oneParticleIndex).symm.toMeasurableEquiv.measurableEmbedding
    (fun x : Space => density Z x / ‖x‖)).trans (integral_density_div_norm hZ)

end PfHk.HydrogenOrbital
