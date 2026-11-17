import GptLean.PhysicalPolarizationFrame
import GptLean.TransformationsKernelCovariance
import GptLean.TransformationsAffine
import GptLean.SymmetricLift.MetricGeometry

/-!
Rotations of the polarization frame, of the electron configuration and of the
photon momentum.

Let `R` be a linear isometry of `ℝ³` and `(ε₁(k), ε₂(k), k/|k|)` the
article's measurable orthonormal frame. For `k ≠ 0` the rotated vectors
`f_b = R ε_b(Rᵀ k)` form another orthonormal basis of the plane orthogonal to
`k`. Hence the overlap matrix `O_{ab}(k) = ⟪ε_a(k), f_b⟫` is orthogonal and
`ε_a(k) = ∑_b O_{ab}(k) f_b`. At `k = 0` the overlap is set to the identity.
If the cutoff is invariant, `χ(Rᵀ k) = χ(k)`, the article's form factors
`G_ν(k, b) = ε_b(k)_ν χ(-k)/√2` therefore satisfy

`∑_ν R_{μν} ∑_b O_{ab}(k) G_ν(Rᵀ k, b) = G_μ(k, a)`  for `k ≠ 0`,

where `R_{μν} = (R e_ν)_μ`. The same identity holds for the inverse-frequency
profiles, since `|Rᵀ k| = |k|`.

The simultaneous rotation `x_n ↦ Rᵀ x_n` of all electrons is a linear isometry
of configuration space whose chain-rule coefficients are `δ_{nm} R_{μν}`, and
`(k, λ) ↦ (Rᵀ k, λ)` is a measure-preserving relabelling of the photon modes
which preserves `|k|`.
-/

noncomputable section

namespace GptLean.TransformationsRotation

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization TransformationsFock
  TransformationsAffine PhotonLocalizationPhysicalKernels
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 400000

variable (R : FieldSpace ≃ₗᵢ[ℝ] FieldSpace)

/-! ### Matrix entries -/

/-- `rmat μ ν = (Rᵀ e_μ)_ν = (R e_ν)_μ`. -/
def rmat (μ ν : Fin 3) : ℝ := R.symm (EuclideanSpace.single μ 1) ν

theorem rmat_sum (v : FieldSpace) (μ : Fin 3) : ∑ ν, rmat R μ ν * v ν = R v μ := by
  have h1 : ∑ ν, rmat R μ ν * v ν = ⟪R.symm (EuclideanSpace.single μ 1), v⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [rmat, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [h1, R.symm.inner_map_eq_flip, EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

/-! ### The rotated frame -/

variable (F : Frame)

theorem basis_two_epsilon (q : FieldSpace) (b : Fin 2) :
    ⟪F.basis q 2, F.epsilon q b⟫_ℝ = 0 :=
  (F.basis q).orthonormal.2 (by
    intro h
    have := congrArg Fin.val h
    have hb := b.isLt
    change 2 = b.val at this
    omega)

theorem inner_epsilon_self (q : FieldSpace) (b : Fin 2) : ⟪q, F.epsilon q b⟫_ℝ = 0 := by
  by_cases hq : q = 0
  · rw [hq, inner_zero_left]
  · have hq' : q = ‖q‖ • F.basis q 2 := by
      rw [F.radial q hq, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hq), one_smul]
    rw [show ⟪q, F.epsilon q b⟫_ℝ = ⟪‖q‖ • F.basis q 2, F.epsilon q b⟫_ℝ from
      congrArg (fun v => ⟪v, F.epsilon q b⟫_ℝ) hq', real_inner_smul_left, basis_two_epsilon,
      mul_zero]

theorem epsilon_inner (q : FieldSpace) (b c : Fin 2) :
    ⟪F.epsilon q b, F.epsilon q c⟫_ℝ = if b = c then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (F.basis q).orthonormal b.castSucc c.castSucc
  change ⟪F.basis q b.castSucc, F.basis q c.castSucc⟫_ℝ = _
  rw [h]
  by_cases hbc : b = c
  · simp only [hbc, if_true]
  · simp only [hbc, if_false, (Fin.castSucc_injective 2).ne hbc]

/-- Vectors orthogonal to `k ≠ 0` expand in the transverse frame. -/
theorem transverse_expand (k : FieldSpace) (hk : k ≠ 0) (v : FieldSpace) (hv : ⟪k, v⟫_ℝ = 0) :
    ∑ a : Fin 2, ⟪F.epsilon k a, v⟫_ℝ • F.epsilon k a = v := by
  have h := congrArg (fun T : FieldSpace →L[ℝ] FieldSpace => T v) (F.transverseProjection_eq k)
  have hb : ⟪F.basis k 2, v⟫_ℝ = 0 := by
    rw [F.radial k hk, real_inner_smul_left, hv, mul_zero]
  simpa only [Frame.transverseProjection, ContinuousLinearMap.sum_apply,
    InnerProductSpace.rankOne_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    hb, zero_smul, sub_zero] using h

/-- The rotated frame vector `R ε_b(Rᵀ k)`. -/
def rotatedEpsilon (k : FieldSpace) (b : Fin 2) : FieldSpace := R (F.epsilon (R.symm k) b)

theorem inner_rotatedEpsilon (k : FieldSpace) (b : Fin 2) :
    ⟪k, rotatedEpsilon R F k b⟫_ℝ = 0 :=
  (R.symm.inner_map_eq_flip k (F.epsilon (R.symm k) b)).symm.trans
    (inner_epsilon_self F (R.symm k) b)

theorem rotatedEpsilon_inner (k : FieldSpace) (b c : Fin 2) :
    ⟪rotatedEpsilon R F k b, rotatedEpsilon R F k c⟫_ℝ = if b = c then 1 else 0 :=
  (R.inner_map_map _ _).trans (epsilon_inner F (R.symm k) b c)

/-- Vectors orthogonal to `k ≠ 0` expand in the rotated frame. -/
theorem rotated_expand (k : FieldSpace) (hk : k ≠ 0) (v : FieldSpace) (hv : ⟪k, v⟫_ℝ = 0) :
    ∑ b : Fin 2, ⟪rotatedEpsilon R F k b, v⟫_ℝ • rotatedEpsilon R F k b = v := by
  have hq : R.symm k ≠ 0 := fun h => hk (by simpa using congrArg R h)
  have hv' : ⟪R.symm k, R.symm v⟫_ℝ = 0 := (R.symm.inner_map_map k v).trans hv
  have h := transverse_expand F (R.symm k) hq (R.symm v) hv'
  have h2 := congrArg R h
  rw [map_sum, LinearIsometryEquiv.apply_symm_apply] at h2
  refine Eq.trans ?_ h2
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, rotatedEpsilon, R.inner_map_eq_flip]

/-- The overlap matrix `O_{ab}(k) = ⟪ε_a(k), R ε_b(Rᵀ k)⟫`, the identity at `k = 0`. -/
def overlap (k : FieldSpace) (a b : Fin 2) : ℝ :=
  if k = 0 then (if a = b then 1 else 0) else ⟪F.epsilon k a, rotatedEpsilon R F k b⟫_ℝ

theorem overlap_measurable (a b : Fin 2) : Measurable fun k => overlap R F k a b := by
  have hr : Measurable fun k => rotatedEpsilon R F k b :=
    R.continuous.measurable.comp ((F.epsilon_measurable b).comp R.symm.continuous.measurable)
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((continuous_inner (𝕜 := ℝ) (E := FieldSpace)).measurable.comp
      ((F.epsilon_measurable a).prodMk hr))

/-- The overlap matrix is orthogonal. -/
theorem overlap_orthogonal (k : FieldSpace) (b c : Fin 2) :
    ∑ a, overlap R F k a b * overlap R F k a c = if b = c then 1 else 0 := by
  by_cases hk : k = 0
  · simp only [overlap, hk, if_true, mul_ite, mul_one, mul_zero]
    by_cases hbc : b = c
    · subst hbc
      simp
    · simp [hbc, Ne.symm hbc]
  · simp only [overlap, hk, if_false]
    have he := transverse_expand F k hk (rotatedEpsilon R F k b) (inner_rotatedEpsilon R F k b)
    have h := congrArg (fun v => ⟪v, rotatedEpsilon R F k c⟫_ℝ) he
    simp only [sum_inner, real_inner_smul_left] at h
    exact h.trans (rotatedEpsilon_inner R F k b c)

/-- The frame at `k ≠ 0` is recovered from the rotated frame. -/
theorem overlap_reconstruction (k : FieldSpace) (hk : k ≠ 0) (a : Fin 2) :
    ∑ b, overlap R F k a b • rotatedEpsilon R F k b = F.epsilon k a := by
  have h := rotated_expand R F k hk (F.epsilon k a) (inner_epsilon_self F k a)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [overlap, if_neg hk, real_inner_comm]

/-- The real part of the form-factor identity. -/
theorem epsilon_rotation (k : FieldSpace) (hk : k ≠ 0) (a : Fin 2) (μ : Fin 3) :
    ∑ ν, rmat R μ ν * ∑ b, overlap R F k a b * F.epsilon (R.symm k) b ν = F.epsilon k a μ := by
  have h := congrArg (fun v : FieldSpace => v μ) (overlap_reconstruction R F k hk a)
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    rotatedEpsilon] at h
  refine Eq.trans ?_ h
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← rmat_sum R (F.epsilon (R.symm k) b) μ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- A profile with values `g_ν(k, b) = c(k) ε_b(k)_ν` transforms like the frame,
when `c(Rᵀ k) = c(k)`. -/
theorem profile_rotation (c : FieldSpace → ℂ) (hc : ∀ q, c (R.symm q) = c q)
    (k : FieldSpace) (hk : k ≠ 0) (a : Fin 2) (μ : Fin 3) :
    ∑ ν, (rmat R μ ν : ℂ) * ∑ b, (overlap R F k a b : ℂ) *
        ((F.epsilon (R.symm k) b ν : ℝ) * c (R.symm k)) =
      (F.epsilon k a μ : ℂ) * c k := by
  rw [hc, ← epsilon_rotation R F k hk a μ]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => ?_
  ring

variable (χ : ArticleCutoff)

/-- The article's form factors transform like the frame under an invariant cutoff. -/
theorem base_rotation (hχ : ∀ q, χ.value (R.symm q) = χ.value q) (k : FieldSpace) (hk : k ≠ 0)
    (a : Fin 2) (μ : Fin 3) :
    ∑ ν, (rmat R μ ν : ℂ) * ∑ b, (overlap R F k a b : ℂ) * base F χ ν (R.symm k, b) =
      base F χ μ (k, a) := by
  have h := profile_rotation R F (fun q => χ.value (-q) / (Real.sqrt 2 : ℂ))
    (fun q => by simp only [← map_neg, hχ]) k hk a μ
  refine Eq.trans ?_ (h.trans ?_)
  · refine Finset.sum_congr rfl fun ν _ => congrArg (fun z => (rmat R μ ν : ℂ) * z)
      (Finset.sum_congr rfl fun b _ => congrArg (fun z => (overlap R F k a b : ℂ) * z) ?_)
    simp only [base]
    ring
  · simp only [base]
    ring

/-- The inverse-frequency profiles transform in the same way. -/
theorem infraredBase_rotation (hχ : ∀ q, χ.value (R.symm q) = χ.value q) (k : FieldSpace)
    (hk : k ≠ 0) (a : Fin 2) (μ : Fin 3) :
    ∑ ν, (rmat R μ ν : ℂ) * ∑ b, (overlap R F k a b : ℂ) *
        infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ ν) (R.symm k, b) =
      infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ μ) (k, a) := by
  have h := profile_rotation R F
    (fun q => ((Real.sqrt ‖q‖)⁻¹ : ℂ) * (χ.value (-q) / (Real.sqrt 2 : ℂ)))
    (fun q => by simp only [← map_neg, hχ, LinearIsometryEquiv.norm_map]) k hk a μ
  refine Eq.trans ?_ (h.trans ?_)
  · refine Finset.sum_congr rfl fun ν _ => congrArg (fun z => (rmat R μ ν : ℂ) * z)
      (Finset.sum_congr rfl fun b _ => congrArg (fun z => (overlap R F k a b : ℂ) * z) ?_)
    simp only [infraredBase, base, Complex.real_smul]
    push_cast
    ring
  · simp only [infraredBase, base, Complex.real_smul]
    push_cast
    ring

/-! ### Rotation of the electron configuration -/

open SymmetricLift

/-- The simultaneous rotation `x_n ↦ Rᵀ x_n` of all electrons. -/
def configLinear (N : ℕ) : Configuration N →ₗ[ℝ] Configuration N where
  toFun x := WithLp.toLp 2 (fun q => R.symm (particle x q.1) q.2)
  map_add' x y := by
    ext q
    have h : particle (x + y) q.1 = particle x q.1 + particle y q.1 := by
      ext μ
      rfl
    simp only [h, map_add]
    rfl
  map_smul' c x := by
    ext q
    have h : particle (c • x) q.1 = c • particle x q.1 := by
      ext μ
      rfl
    simp only [h, map_smul]
    rfl

theorem particle_configLinear (N : ℕ) (x : Configuration N) (n : Fin N) :
    particle (configLinear R N x) n = R.symm (particle x n) := by
  ext μ
  rfl

theorem norm_sq_configuration {N : ℕ} (x : Configuration N) :
    ‖x‖ ^ 2 = ∑ n, ‖particle x n‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem configLinear_inv (N : ℕ) (x : Configuration N) :
    configLinear R.symm N (configLinear R N x) = x := by
  ext q
  change R.symm.symm (particle (configLinear R N x) q.1) q.2 = x q
  rw [particle_configLinear]
  change R (R.symm (particle x q.1)) q.2 = x q
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The configuration rotation as a linear isometry equivalence. -/
def configRotation (N : ℕ) : Configuration N ≃ₗᵢ[ℝ] Configuration N where
  toLinearMap := configLinear R N
  invFun := configLinear R.symm N
  left_inv := configLinear_inv R N
  right_inv x := configLinear_inv R.symm N x
  norm_map' x := by
    have h : ‖configLinear R N x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_configuration, norm_sq_configuration]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [particle_configLinear, LinearIsometryEquiv.norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The configuration rotation as an affine isometry with no shift. -/
def rotationIsometry (N : ℕ) : AffineIsometry (Fin N × Fin 3) where
  linear := configRotation R N
  shift := 0

theorem particle_rotationIsometry (N : ℕ) (x : Configuration N) (n : Fin N) :
    particle ((rotationIsometry R N).apply x) n = R.symm (particle x n) := by
  ext μ
  change (configLinear R N x + 0) (n, μ) = _
  rw [add_zero]
  rfl

/-- The chain-rule coefficients of the configuration rotation. -/
theorem rotationIsometry_coefficient (N : ℕ) (n m : Fin N) (μ ν : Fin 3) :
    (rotationIsometry R N).coefficient (n, μ) (m, ν) = if n = m then rmat R μ ν else 0 := by
  change R.symm (particle (EuclideanSpace.single (n, μ) (1 : ℝ)) m) ν = _
  have hp : particle (EuclideanSpace.single (n, μ) (1 : ℝ) : Configuration N) m =
      if n = m then EuclideanSpace.single μ 1 else 0 := by
    ext κ
    by_cases h : n = m
    · subst h
      simp only [particle, EuclideanSpace.single_apply, Prod.mk.injEq, true_and, if_true]
    · simp only [particle, EuclideanSpace.single_apply, Prod.mk.injEq, if_neg h]
      have hm : ¬ (m = n) := fun h' => h h'.symm
      simp [hm]
  rw [hp]
  by_cases h : n = m
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, map_zero]
    rfl

/-- The rotation commutes with relabelling the electrons. -/
theorem rotationIsometry_permute (N : ℕ) (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    (rotationIsometry R N).apply (permuteConfiguration π x) =
      permuteConfiguration π ((rotationIsometry R N).apply x) := by
  ext q
  change (configLinear R N (permuteConfiguration π x) + 0) q =
    (configLinear R N x + 0) (π.symm q.1, q.2)
  rw [add_zero, add_zero]
  change R.symm (particle (permuteConfiguration π x) q.1) q.2 =
    R.symm (particle x (π.symm q.1)) q.2
  rfl

/-! ### Rotation of the photon momentum -/

theorem measurable_rotateMode (S : FieldSpace ≃ₗᵢ[ℝ] FieldSpace) :
    Measurable (fun p : PhotonMode => (S p.1, p.2)) :=
  (S.continuous.measurable.comp measurable_fst).prodMk measurable_snd

/-- The relabelling `(k, λ) ↦ (Rᵀ k, λ)`. -/
def rotateMode : PhotonMode ≃ᵐ PhotonMode where
  toFun p := (R.symm p.1, p.2)
  invFun p := (R p.1, p.2)
  left_inv p := Prod.ext (R.apply_symm_apply p.1) rfl
  right_inv p := Prod.ext (R.symm_apply_apply p.1) rfl
  measurable_toFun := measurable_rotateMode R.symm
  measurable_invFun := measurable_rotateMode R

theorem rotateMode_preserving : MeasurePreserving (rotateMode R) photonMeasure photonMeasure := by
  have h₁ := R.symm.measurePreserving
  have h₂ := h₁.prod (MeasurePreserving.id (Measure.count : Measure (Fin 2)))
  have he : (rotateMode R : PhotonMode → PhotonMode) = Prod.map (⇑R.symm) id := rfl
  rw [he]
  exact h₂

/-- The photon momentum rotation `(U f)(k, λ) = f(Rᵀ k, λ)`. -/
def photonRotation : PointwiseUnitary photonMeasure where
  map := rotateMode R
  preserving := rotateMode_preserving R
  weight _ := 1
  measurable_weight := measurable_const
  norm_weight _ := norm_one

theorem photonRotation_dispersion : ∀ p, ‖((photonRotation R).map p).1‖ = ‖p.1‖ :=
  fun p => R.symm.norm_map p.1

theorem photonRotation_ae (f : Lp ℂ 2 photonMeasure) :
    oneParticle (photonRotation R) f =ᵐ[photonMeasure] fun p => f (R.symm p.1, p.2) := by
  filter_upwards [oneParticle_ae (photonRotation R) f] with p hp
  rw [hp]
  exact one_mul _

end GptLean.TransformationsRotation
