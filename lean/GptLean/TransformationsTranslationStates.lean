import GptLean.TransformationsTranslationReference
import GptLean.TransformationsKernelCovariance
import GptLean.TransformationsPureStates
import GptLean.TransformationsPotentials

/-!
Translation covariance of the Levy--Lieb and Lieb functionals on the actual
Pauli--Fierz model, `prop-translation-covariance`.

The translation is `T(b) Ψ(X) = Γ(t_b) Ψ(X - b)`, where all electrons are
shifted by `b` and `t_b` multiplies one-photon wave functions by `e^{-i k·b}`.
If the internal potential is translation invariant and the field kernels are
translation covariant, `t_b K(·, y - b) = K(·, y)`, then `T(b)` maps pure
states to pure states, preserves the energy, and moves the density-current
pair to `(ρ(· - b), j(· - b))`. Hence

`F(ρ(· - b), j(· - b)) = F(ρ, j)`

for `F = F_LL` and for the Lieb functional `F = F_L`. The kernel covariance
holds for the actual form-factor kernels by `kernelMap_translation`.
-/

noncomputable section

namespace GptLean.TransformationsTranslation

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms TransformationsFock TransformationsKernelCovariance
  TransformationsPotentials
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

/-- The configuration displacement moving every electron by `b`. -/
def diag {N : ℕ} (b : PhysicalPairSpace.Position) : Configuration N :=
  WithLp.toLp 2 (fun q => b q.2)

theorem particle_add_diag {N : ℕ} (x : Configuration N) (b : PhysicalPairSpace.Position)
    (j : Fin N) : particle (x + diag b) j = particle x j + b := by
  ext a
  rfl

theorem permute_diag {N : ℕ} (π : Equiv.Perm (Fin N)) (b : PhysicalPairSpace.Position) :
    permuteConfiguration π (diag b) = diag (N := N) b := by
  ext q
  rfl

theorem neg_diag {N : ℕ} (b : PhysicalPairSpace.Position) : -diag (N := N) b = diag (-b) := by
  ext q
  rfl

variable {N : ℕ} (b : PhysicalPairSpace.Position)

/-- The physical translation `T(b) Ψ(X) = Γ(t_b) Ψ(X - b)` of wave functions. -/
abbrev translation (b : PhysicalPairSpace.Position) (v : WaveSpace (Fin N × Fin 3)) :
    WaveSpace (Fin N × Fin 3) :=
  waveMap (diag (-b)) (photonTranslation b) v

/-- The inverse translation. -/
abbrev translationInv (b : PhysicalPairSpace.Position) (v : WaveSpace (Fin N × Fin 3)) :
    WaveSpace (Fin N × Fin 3) :=
  waveMap (-diag (-b)) (photonTranslation b).symm v

theorem translationInv_translation (v : WaveSpace (Fin N × Fin 3)) :
    translationInv b (translation b v) = v :=
  waveMap_neg (diag (-b)) (photonTranslation b) v

theorem translation_translationInv (v : WaveSpace (Fin N × Fin 3)) :
    translation b (translationInv b v) = v := by
  apply Lp.ext
  filter_upwards [waveMap_ae (diag (-b)) (photonTranslation b) (translationInv b v),
    ae_shift (diag (-b)) (waveMap_ae (-diag (-b)) (photonTranslation b).symm v)] with x h₁ h₂
  refine h₁.trans ((congrArg (fockMap (photonTranslation b)) h₂).trans ?_)
  have hx : x + diag (-b) + -diag (-b) = x := add_neg_cancel_right x _
  exact (congrArg (fun y => fockMap (photonTranslation b)
    (fockMap (photonTranslation b).symm (v y))) hx).trans
    ((congrArg (fockMap (photonTranslation b)) (fockMap_symm_eq _ (v x))).trans
      ((fockMap (photonTranslation b)).apply_symm_apply (v x)))

/-- A permutation-invariant displacement commutes with electronic permutations. -/
theorem waveMap_permutation (c : Configuration N) (hc : ∀ π, permuteConfiguration π c = c)
    (U : PointwiseUnitary photonMeasure) (π : Equiv.Perm (Fin N))
    (v : WaveSpace (Fin N × Fin 3)) :
    PhysicalElectronicFermions.permutation N PhotonFock π (waveMap c U v) =
      waveMap c U (PhysicalElectronicFermions.permutation N PhotonFock π v) := by
  apply Lp.ext
  have hcomp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (waveMap_ae c U v)
  filter_upwards [PhysicalElectronicFermions.permutation_ae N PhotonFock π (waveMap c U v),
    hcomp, waveMap_ae c U (PhysicalElectronicFermions.permutation N PhotonFock π v),
    ae_shift c (PhysicalElectronicFermions.permutation_ae N PhotonFock π v)]
    with x h₁ h₂ h₃ h₄
  refine h₁.trans (h₂.trans (Eq.trans ?_ (h₃.trans (congrArg (fockMap U) h₄)).symm))
  have hx : permuteConfiguration π (x + c) = permuteConfiguration π x + c := by
    rw [map_add, hc π]
  exact congrArg (fun y => fockMap U (v y)) hx.symm

theorem waveMap_mem_fermionic (c : Configuration N) (hc : ∀ π, permuteConfiguration π c = c)
    (U : PointwiseUnitary photonMeasure) {v : WaveSpace (Fin N × Fin 3)}
    (hv : v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    waveMap c U v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock := by
  intro π
  rw [waveMap_permutation c hc U π v, hv π, waveMap_smul]

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (hV : ∀ x c, V (x + diag c) = V x)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)
  (hKcov : ∀ a y, kernelMap (photonTranslation b) (photonTranslation_dispersion b)
    (K (a, y - b)) = K (a, y))

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

include hV in
theorem potential_invariant (c : PhysicalPairSpace.Position) :
    ∀ x, V (x + diag (N := N) c) = V x := fun x => hV x c

/-- The translation on the reference domain. -/
abbrev translateRef (u : Reference (Fin N × Fin 3) V) : Reference (Fin N × Fin 3) V :=
  translate (diag (-b)) (photonTranslation b) (photonTranslation_dispersion b) V
    (potential_invariant V hV (-b)) u

include hKcov in
theorem kernel_covariance (q : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, κP q x = kernelMap (photonTranslation b) (photonTranslation_dispersion b)
      (κP q (x + diag (-b))) := by
  refine ae_of_all _ fun x => ?_
  change K (q.2, particle x q.1) = kernelMap (photonTranslation b) (photonTranslation_dispersion b)
    (K (q.2, particle (x + diag (-b)) q.1))
  rw [particle_add_diag, ← sub_eq_add_neg, hKcov]

include hKcov in
theorem energy_translation (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C κP hκP M hbP e (translateRef b V hV u) =
      energy (Fin N × Fin 3) V C κP hκP M hbP e u :=
  energy_translate (diag (-b)) (photonTranslation b) (photonTranslation_dispersion b) V
    (potential_invariant V hV (-b)) C κP hκP M hbP (kernel_covariance b K hKcov) e u

private theorem particle_sub_diag (z : Configuration N) :
    particle (z - diag (-b)) i = particle z i + b := by
  rw [sub_eq_add_neg, neg_diag, neg_neg, particle_add_diag]

include hKcov in
/-- The translated constructed pair is the translated pair. -/
theorem pair_translation (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e (translateRef b V hV u) =
      translatePair b (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  let c : Configuration N := diag (-b)
  let T := translateRef b V hV u
  have hincl : ∀ᵐ z ∂volume, ‖inclusion (Fin N × Fin 3) V T z‖ =
      ‖inclusion (Fin N × Fin 3) V u (z + c)‖ := by
    filter_upwards [waveMap_ae c (photonTranslation b) (inclusion (Fin N × Fin 3) V u)] with z hz
    exact (congrArg norm hz).trans ((fockMap (photonTranslation b)).norm_map _)
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    have htm : AEStronglyMeasurable (fun x => t.weight (x + b)) volume :=
      t.measurable.comp_measurePreserving (measurePreserving_add_right volume b)
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    have hR : (∫ x, t.weight x * densityL1 (translatePair b
        (PhysicalPFParticle.pair C K hK M hM V i e u)) x) =
        ∫ x, t.weight (x + b) * densityL1 (PhysicalPFParticle.pair C K hK M hM V i e u) x := by
      refine (integral_congr_ae ?_).trans ((integral_add_right_eq_self (μ := volume)
        (fun x => t.weight x * densityL1 (PhysicalPFParticle.pair C K hK M hM V i e u) (x - b))
          b).symm.trans (integral_congr_ae (ae_of_all _ fun x => ?_)))
      · filter_upwards [densityL1_translatePair b (PhysicalPFParticle.pair C K hK M hM V i e u)]
          with x hx
        exact congrArg (fun r => t.weight x * r) hx
      · exact congrArg (fun y => t.weight (x + b) *
          densityL1 (PhysicalPFParticle.pair C K hK M hM V i e u) y) (add_sub_cancel_right x b)
    refine Eq.trans ?_ hR.symm
    refine Eq.trans ?_ (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) _ htm
      (ae_of_all _ fun x => t.bounded (x + b))).symm
    refine congrArg (fun r : ℝ => (N : ℝ) * r) ?_
    refine (integral_congr_ae ?_).trans (integral_add_right_eq_self (μ := volume)
      (fun z => t.weight (particle z i + b) * ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) c)
    filter_upwards [hincl] with z hz
    have hp : ((PhysicalSourceCoordinates.split i) z).1 = particle (z + c) i + b := by
      rw [PhysicalSourcePair.split_fst_eq_particle, particle_add_diag, neg_add_cancel_right]
    exact congrArg₂ (fun (y : PhysicalPairSpace.Position) (r : ℝ) => t.weight y * r ^ 2) hp hz
  · intro a t
    have htm : AEStronglyMeasurable (fun x => t.weight (x + b)) volume :=
      t.measurable.comp_measurePreserving (measurePreserving_add_right volume b)
    have hcov := covariant_translate (diag (-b)) (photonTranslation b)
      (photonTranslation_dispersion b) V (potential_invariant V hV (-b)) C κP hκP M hbP
      (kernel_covariance b K hKcov) e (i, a) u
    have hinner : ∀ᵐ z ∂volume, (⟪inclusion (Fin N × Fin 3) V T z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T z⟫_ℂ).re =
        (⟪inclusion (Fin N × Fin 3) V u (z + c),
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u (z + c)⟫_ℂ).re := by
      filter_upwards [waveMap_ae c (photonTranslation b) (inclusion (Fin N × Fin 3) V u),
        Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w) hcov),
        waveMap_ae c (photonTranslation b)
          (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u)] with z h₁ h₂ h₃
      refine congrArg Complex.re ((congrArg₂ (fun p q => ⟪p, q⟫_ℂ) h₁ (h₂.trans h₃)).trans ?_)
      exact (fockMap (photonTranslation b)).inner_map_map _ _
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) a t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    have hR : (∫ x, t.weight x * currentL1 (translatePair b
        (PhysicalPFParticle.pair C K hK M hM V i e u)) x a) =
        ∫ x, t.weight (x + b) * currentL1 (PhysicalPFParticle.pair C K hK M hM V i e u) x a := by
      refine (integral_congr_ae ?_).trans ((integral_add_right_eq_self (μ := volume)
        (fun x => t.weight x * currentL1 (PhysicalPFParticle.pair C K hK M hM V i e u) (x - b) a)
          b).symm.trans (integral_congr_ae (ae_of_all _ fun x => ?_)))
      · filter_upwards [currentL1_translatePair b (PhysicalPFParticle.pair C K hK M hM V i e u)]
          with x hx
        exact congrArg (fun r : PhysicalPairSpace.Vector => t.weight x * r a) hx
      · exact congrArg (fun y => t.weight (x + b) *
          currentL1 (PhysicalPFParticle.pair C K hK M hM V i e u) y a) (add_sub_cancel_right x b)
    refine Eq.trans ?_ hR.symm
    refine Eq.trans ?_ (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) a _ htm
      (ae_of_all _ fun x => t.bounded (x + b))).symm
    refine congrArg (fun r : ℝ => (N : ℝ) * r) ?_
    refine (integral_congr_ae ?_).trans (integral_add_right_eq_self (μ := volume)
      (fun z => t.weight (particle z i + b) *
        (⟪inclusion (Fin N × Fin 3) V u z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u z⟫_ℂ).re) c)
    filter_upwards [hinner] with z hz
    have hp : ((PhysicalSourceCoordinates.split i) z).1 = particle (z + c) i + b := by
      rw [PhysicalSourcePair.split_fst_eq_particle, particle_add_diag, neg_add_cancel_right]
    exact congrArg₂ (fun (y : PhysicalPairSpace.Position) (r : ℝ) => t.weight y * r) hp hz

include hV in
theorem translation_reference (u : Reference (Fin N × Fin 3) V) :
    ∃ u' : Reference (Fin N × Fin 3) V,
      inclusion (Fin N × Fin 3) V u' = translationInv b (inclusion (Fin N × Fin 3) V u) := by
  refine ⟨translate (-diag (-b)) (photonTranslation b).symm ?_ V ?_ u, ?_⟩
  · exact fun p => (photonTranslation b).symm_invariant (fun p => ‖p.1‖)
      (photonTranslation_dispersion b) p
  · intro x
    rw [neg_diag, neg_neg]
    exact hV x b
  · exact inclusion_translate _ _ _ V _ u

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

include hV hKcov in
/-- **Translation invariance of `F_LL`** on the constructed Pauli--Fierz model. -/
theorem search_translation (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) (translatePair b d) =
      DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) d := by
  have h := TransformationsPureStates.search_covariance_of_reference V C K hK M hM B S e i
    (translation b) (translationInv b) (translatePair b) (fun _ => 0)
    (fun v => norm_waveMap _ _ v) (fun v => norm_waveMap _ _ v)
    (fun v hv => waveMap_mem_fermionic _ (fun π => permute_diag π _) _ hv)
    (fun v hv => waveMap_mem_fermionic _ (fun π => by rw [map_neg, permute_diag]) _ hv)
    (translationInv_translation b) (translation_translationInv b)
    (translation_reference b V hV)
    (fun u _ => ⟨translateRef b V hV u, inclusion_translate _ _ _ V _ u,
      (energy_translation b V hV C K hK M hM e hKcov u).trans (add_zero _).symm,
      pair_translation b V hV C K hK M hM e i hKcov u⟩) d
  rw [h, EReal.coe_zero, add_zero]

include hV hKcov in
/-- **Translation invariance of the Lieb functional** `F_L`. -/
theorem lieb_translation (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (translatePair b d) =
      DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_translate _ b (search_translation b V hV C K hK M hM e i hKcov B S) d

include hV in
/-- For the actual form-factor kernels, translation covariance is automatic. -/
theorem search_translation_physical {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : PhotonLocalizationPhysicalKernels.FormFactors photonMeasure (Fin 3))
    (hF : F.momentum = Prod.fst) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] T) (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C (PhysicalProfiles.momentumKernel F hF J)
        (PhysicalProfiles.momentumKernel_continuous F hF J) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.momentumKernel_bound F hF J) B S e i) (translatePair b d) =
      DFT.search (TransformationsPureStates.pureModel V C (PhysicalProfiles.momentumKernel F hF J)
        (PhysicalProfiles.momentumKernel_continuous F hF J) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.momentumKernel_bound F hF J) B S e i) d :=
  search_translation b V hV C _ _ _ _ e i (kernelMap_translation F hF J b) B S d

end GptLean.TransformationsTranslation
