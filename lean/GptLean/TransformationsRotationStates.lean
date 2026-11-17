import GptLean.TransformationsIsometryReference
import GptLean.TransformationsRotationFrame
import GptLean.TransformationsPairIsometry
import GptLean.TransformationsPureStates

/-!
Orthogonal covariance of the Levy--Lieb and Lieb functionals on the actual
Pauli--Fierz model, `prop-orthogonal-covariance`.

For a linear isometry `R` of `ℝ³` the rotation acts on wave functions by
`(U_R Ψ)(x₁, …, x_N) = Γ Ψ(Rᵀ x₁, …, Rᵀ x_N)`, where `Γ` is the second
quantization of a dispersive photon sector family. Suppose the internal
potential is rotation invariant and the field kernels are covariant,
`K(μ, y) = ∑_ν R_{μν} Γ₁ K(ν, Rᵀ y)` with `R_{μν} = (R e_ν)_μ`. Then the
covariant derivatives mix with the matrix `R`, the energy is invariant, and the
density-current pair moves to `(ρ ∘ Rᵀ, R j ∘ Rᵀ)`. Hence

`F(ρ ∘ Rᵀ, R j ∘ Rᵀ) = F(ρ, j)`

for `F = F_LL` and for the Lieb functional `F = F_L`.
-/

noncomputable section

namespace GptLean.TransformationsRotation

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms TransformationsFock TransformationsAffine
  TransformationsIsometry TransformationsPotentials
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

variable {N : ℕ} (R : Gaussian.FieldSpace ≃ₗᵢ[ℝ] Gaussian.FieldSpace)
  (G : SectorFamily photonMeasure) (hG : G.Dispersive)

/-- The inverse of an isometry commuting with electron relabelling commutes as well. -/
theorem inv_permute (A : AffineIsometry (Fin N × Fin 3))
    (hA : ∀ π x, A.apply (permuteConfiguration π x) = permuteConfiguration π (A.apply x))
    (π : Equiv.Perm (Fin N)) (y : Configuration N) :
    A.inv.apply (permuteConfiguration π y) = permuteConfiguration π (A.inv.apply y) := by
  have h := hA π (A.inv.apply y)
  rw [A.apply_inv_apply] at h
  rw [← h, A.inv_apply_apply]

/-- An isometry commuting with electron relabelling commutes with the
electronic permutations of wave functions. -/
theorem waveMap_permutation (A : AffineIsometry (Fin N × Fin 3))
    (hA : ∀ π x, A.apply (permuteConfiguration π x) = permuteConfiguration π (A.apply x))
    (H : SectorFamily photonMeasure) (π : Equiv.Perm (Fin N))
    (v : WaveSpace (Fin N × Fin 3)) :
    PhysicalElectronicFermions.permutation N PhotonFock π (waveMap A H v) =
      waveMap A H (PhysicalElectronicFermions.permutation N PhotonFock π v) := by
  apply Lp.ext
  have hcomp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (waveMap_ae A H v)
  filter_upwards [PhysicalElectronicFermions.permutation_ae N PhotonFock π (waveMap A H v),
    hcomp, waveMap_ae A H (PhysicalElectronicFermions.permutation N PhotonFock π v),
    ae_pull A (PhysicalElectronicFermions.permutation_ae N PhotonFock π v)]
    with x h₁ h₂ h₃ h₄
  refine h₁.trans (h₂.trans (Eq.trans ?_ (h₃.trans (congrArg H.fock h₄)).symm))
  exact congrArg (fun y => H.fock (v y)) (hA π x)

theorem waveMap_mem_fermionic (A : AffineIsometry (Fin N × Fin 3))
    (hA : ∀ π x, A.apply (permuteConfiguration π x) = permuteConfiguration π (A.apply x))
    (H : SectorFamily photonMeasure) {v : WaveSpace (Fin N × Fin 3)}
    (hv : v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    waveMap A H v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  fun π => (waveMap_permutation A hA H π v).trans ((congrArg (waveMap A H) (hv π)).trans
    (map_smul (waveMap A H) _ v))

/-- Multiplying a weighted sum by a common factor. -/
theorem mul_sum_comm (t : ℝ) (r f : Fin 3 → ℝ) :
    t * ∑ ν, r ν * f ν = ∑ ν, r ν * (t * f ν) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- Rotation of the electron positions with the photon map `Γ`. -/
abbrev rotation (v : WaveSpace (Fin N × Fin 3)) : WaveSpace (Fin N × Fin 3) :=
  waveMap (rotationIsometry R N) G v

/-- The inverse rotation. -/
abbrev rotationInv (v : WaveSpace (Fin N × Fin 3)) : WaveSpace (Fin N × Fin 3) :=
  waveMap (rotationIsometry R N).inv G.symm v

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (hV : ∀ x, V ((rotationIsometry R N).apply x) = V x)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)
  (hKcov : ∀ μ y, K (μ, y) = ∑ ν, rmat R μ ν • G.kernel hG (K (ν, R.symm y)))

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

/-- The rotation on the reference domain. -/
abbrev rotateRef (u : Reference (Fin N × Fin 3) V) : Reference (Fin N × Fin 3) V :=
  isoMap (rotationIsometry R N) G hG V hV u

/-- Mixing sums over all coordinates collapse to the coordinates of one electron. -/
theorem sum_coefficient {E : Type*} [AddCommGroup E] [Module ℝ E] (n : Fin N) (μ : Fin 3)
    (w : Fin N × Fin 3 → E) :
    ∑ j, (rotationIsometry R N).coefficient (n, μ) j • w j = ∑ ν, rmat R μ ν • w (n, ν) := by
  rw [Fintype.sum_prod_type]
  simp only [rotationIsometry_coefficient, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ n)]

theorem sum_coefficient_complex {E : Type*} [AddCommGroup E] [Module ℂ E] (n : Fin N) (μ : Fin 3)
    (w : Fin N × Fin 3 → E) :
    ∑ j, (((rotationIsometry R N).coefficient (n, μ) j : ℝ) : ℂ) • w j =
      ∑ ν, ((rmat R μ ν : ℝ) : ℂ) • w (n, ν) := by
  rw [Fintype.sum_prod_type]
  simp only [rotationIsometry_coefficient, apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_zero,
    ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ n)]

include hKcov in
theorem kernel_covariance (q : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, κP q x = ∑ j, (rotationIsometry R N).coefficient q j •
      G.kernel hG (κP j ((rotationIsometry R N).apply x)) := by
  refine ae_of_all _ fun x => ?_
  refine Eq.trans ?_ (sum_coefficient R q.1 q.2 _).symm
  change K (q.2, particle x q.1) = ∑ ν, rmat R q.2 ν •
    G.kernel hG (K (ν, particle ((rotationIsometry R N).apply x) q.1))
  rw [particle_rotationIsometry]
  exact hKcov q.2 (particle x q.1)

include hKcov in
theorem energy_rotation (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C κP hκP M hbP e (rotateRef R G hG V hV u) =
      energy (Fin N × Fin 3) V C κP hκP M hbP e u :=
  energy_isoMap (rotationIsometry R N) G hG V hV C κP hκP M hbP
    (kernel_covariance R G hG K hKcov) e u

include hKcov in
theorem covariant_rotation (a : Fin 3) (u : Reference (Fin N × Fin 3) V) :
    covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) (rotateRef R G hG V hV u) =
      ∑ ν, ((rmat R a ν : ℝ) : ℂ) •
        waveMap (rotationIsometry R N) G (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u) :=
  (covariant_isoMap (rotationIsometry R N) G hG V hV C κP hκP M hbP
    (kernel_covariance R G hG K hKcov) e (i, a) u).trans (sum_coefficient_complex R i a _)

/-- Rotating the test weight together with the electron coordinates. -/
theorem tested_rotation (t : PhysicalPairSpace.Position → ℝ) (f g : Configuration N → ℝ)
    (hfg : ∀ᵐ z ∂volume, f z = g ((rotationIsometry R N).apply z)) :
    (∫ z, t ((PhysicalSourceCoordinates.split i) z).1 * f z) =
      ∫ w, t (R ((PhysicalSourceCoordinates.split i) w).1) * g w := by
  refine (integral_congr_ae ?_).trans ((rotationIsometry R N).measurePreserving.integral_comp
    (rotationIsometry R N).toMeasurableEquiv.measurableEmbedding
      (fun w => t (R ((PhysicalSourceCoordinates.split i) w).1) * g w))
  filter_upwards [hfg] with z hz
  simp only [hz, PhysicalSourcePair.split_fst_eq_particle, AffineIsometry.toMeasurableEquiv_apply,
    particle_rotationIsometry, LinearIsometryEquiv.apply_symm_apply]

theorem integral_rotate_weight (t : PhysicalPairSpace.Position → ℝ)
    (f : PhysicalPairSpace.Position → ℝ) :
    (∫ x, t x * f (R.symm x)) = ∫ y, t (R y) * f y := by
  refine Eq.trans ?_ (integral_comp_rotate R (fun y => t (R y) * f y))
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem weight_split_measurable (t : PhysicalPairSpace.Position → ℝ)
    (ht : AEStronglyMeasurable (fun x => t (R x)) volume) :
    AEStronglyMeasurable (fun w : Configuration N => t (R ((PhysicalSourceCoordinates.split i) w).1))
      volume :=
  ht.comp_quasiMeasurePreserving
    ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure PhysicalPairSpace.Position))
      (ν := (volume : Measure (PhysicalSourceCoordinates.Spectator i)))).comp
      (PhysicalSourceCoordinates.split_measurePreserving i).quasiMeasurePreserving)

include hKcov in
/-- The rotated constructed pair is the rotated pair. -/
theorem pair_rotation (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e (rotateRef R G hG V hV u) =
      rotatePair R (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  set A := rotationIsometry R N
  set T := rotateRef R G hG V hV u
  set d := PhysicalPFParticle.pair C K hK M hM V i e u
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    have htm : AEStronglyMeasurable (fun x => t.weight (R x)) volume :=
      t.measurable.comp_measurePreserving R.measurePreserving
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    have hR : (∫ x, t.weight x * densityL1 (rotatePair R d) x) =
        ∫ y, t.weight (R y) * densityL1 d y :=
      (integral_congr_ae (by
        filter_upwards [densityL1_rotatePair R d] with x hx
        exact congrArg (fun r => t.weight x * r) hx)).trans
        (integral_rotate_weight R t.weight _)
    refine Eq.trans ?_ hR.symm
    refine Eq.trans ?_ (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) _ htm
      (ae_of_all _ fun x => t.bounded (R x))).symm
    refine congrArg (fun r : ℝ => (N : ℝ) * r) ?_
    refine tested_rotation R i t.weight _ (fun w => ‖inclusion (Fin N × Fin 3) V u w‖ ^ 2) ?_
    filter_upwards [waveMap_ae A G (inclusion (Fin N × Fin 3) V u)] with z hz
    exact congrArg (· ^ 2) ((congrArg norm hz).trans (G.fock.norm_map _))
  · intro a t
    have htm : AEStronglyMeasurable (fun x => t.weight (R x)) volume :=
      t.measurable.comp_measurePreserving R.measurePreserving
    have hinner : ∀ᵐ z ∂volume, (⟪inclusion (Fin N × Fin 3) V T z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T z⟫_ℂ).re =
        ∑ ν, rmat R a ν * (⟪inclusion (Fin N × Fin 3) V u (A.apply z),
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u (A.apply z)⟫_ℂ).re := by
      have hw : ∀ᵐ z ∂volume, ∀ ν, waveMap A G
          (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u) z =
            G.fock (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u (A.apply z)) :=
        ae_all_iff.mpr fun ν => waveMap_ae A G _
      have hs : ∀ᵐ z ∂volume, ∀ ν, (((rmat R a ν : ℝ) : ℂ) • waveMap A G
          (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u)) z =
            ((rmat R a ν : ℝ) : ℂ) • waveMap A G
              (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u) z :=
        ae_all_iff.mpr fun ν => Lp.coeFn_smul _ _
      filter_upwards [waveMap_ae A G (inclusion (Fin N × Fin 3) V u),
        Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w)
          (covariant_rotation R G hG V hV C K hK M hM e i hKcov a u)),
        coeFn_finset_sum Finset.univ fun ν => ((rmat R a ν : ℝ) : ℂ) • waveMap A G
          (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u), hs, hw] with z h₁ h₂ h₃ h₄ h₅
      refine (congrArg Complex.re ((congrArg₂ (fun p q => ⟪p, q⟫_ℂ) h₁ (h₂.trans h₃)).trans
        ((inner_sum _ _ _).trans (Finset.sum_congr rfl (g := fun ν =>
          ((rmat R a ν : ℝ) : ℂ) * ⟪inclusion (Fin N × Fin 3) V u (A.apply z),
            covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u (A.apply z)⟫_ℂ)
          fun ν _ => ?_)))).trans
        ((Complex.re_sum _ _).trans (Finset.sum_congr rfl fun ν _ => Complex.re_ofReal_mul _ _))
      refine (congrArg (fun q => ⟪G.fock (inclusion (Fin N × Fin 3) V u (A.apply z)), q⟫_ℂ)
        ((h₄ ν).trans (congrArg (fun q => ((rmat R a ν : ℝ) : ℂ) • q) (h₅ ν)))).trans ?_
      exact (inner_smul_right _ _ _).trans (congrArg (fun q => ((rmat R a ν : ℝ) : ℂ) * q)
        (G.fock.inner_map_map _ _))
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) a t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    have hint (ν : Fin 3) : Integrable (fun y => t.weight (R y) * currentL1 d y ν) volume :=
      (current_component_integrable d ν).bdd_mul htm (ae_of_all _ fun y => t.bounded (R y))
    have hR : (∫ x, t.weight x * currentL1 (rotatePair R d) x a) =
        ∑ ν, rmat R a ν * ∫ y, t.weight (R y) * currentL1 d y ν := by
      refine (integral_congr_ae (by
        filter_upwards [currentL1_rotatePair R d] with x hx
        exact congrArg (fun r : PhysicalPairSpace.Vector => t.weight x * r a) hx)).trans
        ((integral_rotate_weight R t.weight (fun y => R (currentL1 d y) a)).trans ?_)
      refine (integral_congr_ae (ae_of_all _ fun y => ?_)).trans
        ((integral_finset_sum Finset.univ fun ν _ => (hint ν).const_mul (rmat R a ν)).trans
          (Finset.sum_congr rfl fun ν _ => integral_const_mul _ _))
      change t.weight (R y) * R (currentL1 d y) a =
        ∑ ν, rmat R a ν * (t.weight (R y) * currentL1 d y ν)
      rw [← rmat_sum R (currentL1 d y) a, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    refine Eq.trans ?_ hR.symm
    refine Eq.trans ?_ (Finset.sum_congr rfl fun ν _ => congrArg (fun r => rmat R a ν * r)
      (PhysicalSourcePair.tested_current_ofWaveFunction i
        (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
        (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) ν _ htm
        (ae_of_all _ fun x => t.bounded (R x))).symm)
    have hw := weight_split_measurable R i t.weight htm
    have hint' (ν : Fin 3) : Integrable (fun w : Configuration N =>
        t.weight (R ((PhysicalSourceCoordinates.split i) w).1) *
          (⟪inclusion (Fin N × Fin 3) V u w,
            covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u w⟫_ℂ).re) volume :=
      (L2.integrable_inner (𝕜 := ℂ) (inclusion (Fin N × Fin 3) V u)
        (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u)).re.bdd_mul hw
        (ae_of_all _ fun w => t.bounded _)
    refine (congrArg (fun r : ℝ => (N : ℝ) * r) ((tested_rotation R i t.weight _
      (fun w => ∑ ν, rmat R a ν * (⟪inclusion (Fin N × Fin 3) V u w,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, ν) u w⟫_ℂ).re) hinner).trans
      ((integral_congr_ae (ae_of_all _ fun w => ?_)).trans
        ((integral_finset_sum Finset.univ fun ν _ => (hint' ν).const_mul (rmat R a ν)).trans
          (Finset.sum_congr rfl fun ν _ => integral_const_mul _ _))))).trans ?_
    · exact mul_sum_comm _ _ _
    · exact mul_sum_comm _ _ _

include hG hV in
theorem rotation_reference (u : Reference (Fin N × Fin 3) V) :
    ∃ u' : Reference (Fin N × Fin 3) V,
      inclusion (Fin N × Fin 3) V u' = rotationInv R G (inclusion (Fin N × Fin 3) V u) :=
  ⟨isoMap (rotationIsometry R N).inv G.symm (G.dispersive_symm hG) V
      (potential_inv (rotationIsometry R N) V hV) u,
    inclusion_isoMap _ _ _ V _ u⟩

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

include hV hKcov in
/-- **Orthogonal covariance of `F_LL`** on the constructed Pauli--Fierz model. -/
theorem search_rotation (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) (rotatePair R d) =
      DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) d := by
  have hA := rotationIsometry_permute R N
  have h := TransformationsPureStates.search_covariance_of_reference V C K hK M hM B S e i
    (rotation R G) (rotationInv R G) (rotatePair R) (fun _ => 0)
    (fun v => norm_waveMap _ _ v) (fun v => norm_waveMap _ _ v)
    (fun v hv => waveMap_mem_fermionic _ hA G hv)
    (fun v hv => waveMap_mem_fermionic _ (inv_permute _ hA) G.symm hv)
    (waveMap_inv _ G) (waveMap_inv_left _ G)
    (rotation_reference R G hG V hV)
    (fun u _ => ⟨rotateRef R G hG V hV u, inclusion_isoMap _ _ _ V _ u,
      (energy_rotation R G hG V hV C K hK M hM e hKcov u).trans (add_zero _).symm,
      pair_rotation R G hG V hV C K hK M hM e i hKcov u⟩) d
  rw [h, EReal.coe_zero, add_zero]

include hV hKcov in
/-- **Orthogonal covariance of the Lieb functional** `F_L`. -/
theorem lieb_rotation (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (rotatePair R d) =
      DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_rotate _ R (search_rotation R G hG V hV C K hK M hM e i hKcov B S) d

end GptLean.TransformationsRotation
