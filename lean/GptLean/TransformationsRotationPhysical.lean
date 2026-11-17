import GptLean.TransformationsRotationStates
import GptLean.TransformationsFockMixing
import GptLean.TransformationsCoulomb

/-!
Orthogonal covariance for the article's form factors, `prop-orthogonal-covariance`.

For a linear isometry `R` of `ℝ³` and the article's measurable polarization
frame, the one-photon rotation is

`(Υ_R f)(k, a) = ∑_b O_{ab}(k) f(Rᵀ k, b)`,

with the orthogonal overlap matrix `O_{ab}(k) = ⟪ε_a(k), R ε_b(Rᵀ k)⟫`. It is
the composite of the momentum relabelling and a polarization-mixing fibre
unitary, so it has a second quantization on the actual photon Fock space
(`TransformationsFockMixing`). If the cutoff is invariant, `χ(Rᵀ k) = χ(k)`,
the article's kernels satisfy `K(μ, y) = ∑_ν R_{μν} Υ_R K(ν, Rᵀ y)`. With the
rotation invariance of the Coulomb interaction this gives

`F(ρ ∘ Rᵀ, R j ∘ Rᵀ) = F(ρ, j)`

for `F_LL` and `F_L` on the actual Coulomb model with the article's kernels.
-/

noncomputable section

namespace GptLean.TransformationsRotation

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization TransformationsFock
  TransformationsAffine TransformationsIsometry TransformationsPotentials
  TransformationsKernelCovariance PhotonLocalizationPhysicalKernels PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms SymmetricLift
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

variable (R : FieldSpace ≃ₗᵢ[ℝ] FieldSpace) (F : Frame)

/-- The polarization overlap as a fibre unitary. -/
def frameUnitary : FibreUnitary FieldSpace (Fin 2) where
  matrix k a b := (overlap R F k a b : ℂ)
  measurable a b := Complex.measurable_ofReal.comp (overlap_measurable R F a b)
  unitary k := by
    ext b c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def,
      Complex.conj_ofReal]
    have h := overlap_orthogonal R F k b c
    rw [← Complex.ofReal_inj] at h
    push_cast at h
    rw [h]
    split_ifs <;> rfl

/-- The one-photon rotation `Υ_R`: rotate the momentum, then mix the polarizations. -/
def photonFamily : SectorFamily photonMeasure :=
  (photonRotation R).family.trans (frameUnitary R F).photonFamily

theorem photonFamily_dispersive : (photonFamily R F).Dispersive :=
  SectorFamily.dispersive_trans _ _
    ((photonRotation R).family_dispersive (photonRotation_dispersion R))
    (frameUnitary R F).photonFamily_dispersive

theorem photonFamily_one_ae {f : Lp ℂ 2 photonMeasure} {g : PhotonMode → ℂ}
    (hf : f =ᵐ[photonMeasure] g) :
    (photonFamily R F).one f =ᵐ[photonMeasure]
      fun p => ∑ b, (overlap R F p.1 p.2 b : ℂ) * g (R.symm p.1, b) := by
  have hr : oneParticle (photonRotation R) f =ᵐ[photonMeasure]
      fun q => g (R.symm q.1, q.2) := by
    filter_upwards [photonRotation_ae R f,
      (rotateMode_preserving R).quasiMeasurePreserving.ae hf] with q h₁ h₂
    exact h₁.trans h₂
  exact (frameUnitary R F).photonFamily_one_eq hr

theorem fieldPhase_rotate (k y : FieldSpace) :
    fieldPhase (R.symm k) (R.symm y) = fieldPhase k y := by
  unfold fieldPhase
  rw [R.symm.inner_map_map]

/-- Pulling the common phase out of the mixing sums. -/
theorem phase_factor (r : Fin 3 → ℝ) (o : Fin 2 → ℂ) (c : ℂ) (g : Fin 3 → Fin 2 → ℂ) :
    ∑ ν, r ν • ∑ b, o b * (c * g ν b) = c * ∑ ν, (r ν : ℂ) * ∑ b, o b * g ν b := by
  simp only [Complex.real_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => ?_
  ring

variable (χ : ArticleCutoff) (hχ : ∀ q, χ.value (R.symm q) = χ.value q)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] T)

/-- A phased profile family transforming like the frame is rotation covariant. -/
theorem oneParticle_rotation (g : Fin 3 → PhotonMode → ℂ)
    (hg : ∀ k, k ≠ 0 → ∀ a μ,
      ∑ ν, (rmat R μ ν : ℂ) * ∑ b, (overlap R F k a b : ℂ) * g ν (R.symm k, b) = g μ (k, a))
    (u : Fin 3 × FieldSpace → Lp ℂ 2 photonMeasure)
    (hu : ∀ ν x, u (ν, x) =ᵐ[photonMeasure] fun p => fieldPhase p.1 x * g ν p)
    (μ : Fin 3) (y : FieldSpace) :
    u (μ, y) = ∑ ν, rmat R μ ν • (photonFamily R F).one (u (ν, R.symm y)) := by
  apply Lp.ext
  have hn : ∀ᵐ p ∂photonMeasure, p.1 ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae
      ((volume : Measure FieldSpace).ae_ne 0)
  have hs : ∀ᵐ p ∂photonMeasure, ∀ ν, (rmat R μ ν • (photonFamily R F).one (u (ν, R.symm y))) p =
      rmat R μ ν • (photonFamily R F).one (u (ν, R.symm y)) p :=
    ae_all_iff.mpr fun ν => Lp.coeFn_smul _ _
  have ho : ∀ᵐ p ∂photonMeasure, ∀ ν, (photonFamily R F).one (u (ν, R.symm y)) p =
      ∑ b, (overlap R F p.1 p.2 b : ℂ) *
        (fieldPhase (R.symm p.1) (R.symm y) * g ν (R.symm p.1, b)) :=
    ae_all_iff.mpr fun ν => photonFamily_one_ae R F (hu ν (R.symm y))
  filter_upwards [hu μ y, coeFn_finset_sum Finset.univ fun ν =>
    rmat R μ ν • (photonFamily R F).one (u (ν, R.symm y)), hs, ho, hn] with p h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun ν _ => (h₃ ν).symm)
  simp only [h₄, fieldPhase_rotate]
  rw [phase_factor, hg p.1 h₅ p.2 μ]

include hχ in
/-- **Rotation covariance of the article's kernels**,
`K(μ, y) = ∑_ν R_{μν} Υ_R K(ν, Rᵀ y)`, for an invariant cutoff. -/
theorem kernel_rotation (μ : Fin 3) (y : FieldSpace) :
    PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (μ, y) =
      ∑ ν, rmat R μ ν • (photonFamily R F).kernel (photonFamily_dispersive R F)
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (ν, R.symm y)) := by
  apply Subtype.ext
  apply Prod.ext
  · refine (momentumKernel_fst (formFactors F χ) rfl J (μ, y)).trans (Eq.trans
      (oneParticle_rotation R F (base F χ)
        (fun k hk a μ => base_rotation R F χ hχ k hk a μ) _
        (fun ν x => fourierKernel_ae (formFactors F χ) rfl ν x) μ y) ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Prod.fst_sum, Prod.smul_fst,
      SectorFamily.kernel_fst, momentumKernel_fst]
  · refine (momentumKernel_snd (formFactors F χ) rfl J (μ, y)).trans (Eq.trans
      (oneParticle_rotation R F
        (fun ν => infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ ν))
        (fun k hk a μ => infraredBase_rotation R F χ hχ k hk a μ) _
        (fun ν x => weightedFourierKernel_ae (formFactors F χ) rfl ν x) μ y) ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Prod.snd_sum, Prod.smul_snd,
      SectorFamily.kernel_snd, momentumKernel_snd]

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (hV : ∀ x, V ((rotationIsometry R N).apply x) = V x)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (i : Fin N)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

include hχ hV in
/-- **Orthogonal covariance of `F_LL`** for the article's kernels and a
rotation-invariant potential. -/
theorem search_rotation_physical (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (rotatePair R d) =
      DFT.search (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i) d :=
  search_rotation R (photonFamily R F) (photonFamily_dispersive R F) V hV C _ _ _ _ e i
    (kernel_rotation R F χ hχ J) B S d

include hχ hV in
/-- **Orthogonal covariance of the Lieb functional** for the article's kernels. -/
theorem lieb_rotation_physical (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (rotatePair R d) =
      DFT.lieb (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_rotation R (photonFamily R F) (photonFamily_dispersive R F) V hV C _ _ _ _ e i
    (kernel_rotation R F χ hχ J) B S d

/-- The Coulomb interaction is invariant under simultaneous rotations. -/
theorem coulomb_rotation (c : ℝ) (x : Configuration N) :
    TransformationsCoulomb.coulomb N c ((rotationIsometry R N).apply x) =
      TransformationsCoulomb.coulomb N c x := by
  simp only [TransformationsCoulomb.coulomb]
  unfold PhysicalCoulombH1.potential
  simp only [particle_rotationIsometry, ← map_sub, LinearIsometryEquiv.norm_map]

include hχ in
/-- **Orthogonal covariance of `F_LL`** for the actual Coulomb model with the
article's kernels. The only hypothesis is the invariance of the cutoff. -/
theorem search_rotation_coulomb (c : ℝ) (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel (TransformationsCoulomb.coulomb N c) C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (rotatePair R d) =
      DFT.search (TransformationsPureStates.pureModel (TransformationsCoulomb.coulomb N c) C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i) d :=
  search_rotation_physical R F χ hχ J _ (coulomb_rotation R c) C e i B S d

include hχ in
/-- **Orthogonal covariance of the Lieb functional** for the actual Coulomb model
with the article's kernels. -/
theorem lieb_rotation_coulomb (c : ℝ) (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel (TransformationsCoulomb.coulomb N c) C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (rotatePair R d) =
      DFT.lieb (TransformationsPureStates.pureModel (TransformationsCoulomb.coulomb N c) C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_rotation_physical R F χ hχ J _ (coulomb_rotation R c) C e i B S d

end GptLean.TransformationsRotation
