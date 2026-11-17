import GptLean.PhysicalFockChannelSpatial
import GptLean.PhysicalFockFourierField
import GptLean.PhysicalFockChannel

/-!
Actual original and tail Fourier profiles form compatible channel kernels.
The retained adjoint is computed from the physical real multiplier and
the same Fourier map used in the channel. The vacuum norm loss is exactly
the discarded L2 mass from the square partition.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhotonLocalizationPhysicalKernels
  PhotonLocalizationFockChannel PhotonLocalizationKernelCutoffs
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

private theorem transported_retained_adjoint {h k : Type*}
    [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    [NormedAddCommGroup k] [InnerProductSpace ℂ k] [CompleteSpace k]
    (e : h ≃ₗᵢ[ℂ] k) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (hs : ∀ u v, ⟪retainedMap j u, v⟫_ℂ = ⟪u, retainedMap j v⟫_ℂ) (f : h) :
    (retainedMap (transportSplit e j)).adjoint (e f) = e (retainedMap j f) := by
  apply ext_inner_left ℂ
  intro v
  calc
    _ = ⟪retainedMap (transportSplit e j) v, e f⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ⟪retainedMap j (e.symm v), f⟫_ℂ := e.inner_map_map _ _
    _ = ⟪e.symm v, retainedMap j f⟫_ℂ := hs _ _
    _ = _ := by rw [← e.inner_map_map, e.apply_symm_apply]

variable {E V S ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [TopologicalSpace ι]
  {μ : Measure FieldSpace}
  (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := photonMeasure))
  (J : V ≃ₗᵢ[ℝ] S) (hdispersion : C.momentum = Prod.fst)

theorem physicalRetained_adjoint (m : ℕ) (f : Lp E 2 μ) :
    (retainedMap (transportSplit C.fourier (complexOnePhotonIsometry (radius m)))).adjoint
      (C.fourier f) = C.fourier (retainedOperator (radius m) f) := by
  apply transported_retained_adjoint
  intro u v
  exact (l2Multiplier_inner (retained (radius m)) (retained_measurable _)
    (ae_of_all _ (retained_abs_le_one _)) u v).symm

variable (p c : SpatialKernelProfile C J ι) (m : ℕ)
  (hc : ∀ z, c.l2 z = p.l2 z - retainedOperator (radius m) (p.l2 z))

/-- The weighted retained kernel is the original kernel minus its actual tail. -/
def profileChannelKernel (z : ι × FieldSpace) :
    ChannelKernel (transportSplit C.fourier (complexOnePhotonIsometry (radius m))) :=
  ⟨(C.fourier (p.l2 z),
      profileMomentumKernel C J hdispersion p z - profileMomentumKernel C J hdispersion c z), by
    change (retainedMap (transportSplit C.fourier (complexOnePhotonIsometry (radius m)))).adjoint
      (C.fourier (p.l2 z)) = C.fourier (p.l2 z) - C.fourier (c.l2 z)
    rw [physicalRetained_adjoint C m, hc, map_sub]
    abel⟩

theorem profileChannelKernel_continuous : Continuous (profileChannelKernel C J hdispersion p c m hc) :=
  ((C.fourier.continuous.comp p.continuous_l2).prodMk
    ((profileMomentumKernel_continuous C J hdispersion p).sub
      (profileMomentumKernel_continuous C J hdispersion c))).subtype_mk _

def profileChannelKernelBound : ℝ :=
  max (profileKernelBound C J p) (profileKernelBound C J p + profileKernelBound C J c)

theorem profileChannelKernel_bound (z : ι × FieldSpace) :
    ‖profileChannelKernel C J hdispersion p c m hc z‖ ≤ profileChannelKernelBound C J p c := by
  change max ‖C.fourier (p.l2 z)‖
    ‖profileMomentumKernel C J hdispersion p z - profileMomentumKernel C J hdispersion c z‖ ≤ _
  apply max_le_max
  · exact (norm_fst_le (profileMomentumKernel C J hdispersion p z).val).trans
      (profileMomentumKernel_bound C J hdispersion p z)
  · exact (norm_sub_le _ _).trans (add_le_add
      (profileMomentumKernel_bound C J hdispersion p z)
      (profileMomentumKernel_bound C J hdispersion c z))

theorem profileChannelKernel_mass_loss (z : ι × FieldSpace) :
    ‖(profileChannelKernel C J hdispersion p c m hc z).val.1‖ ^ 2 -
      ‖(profileChannelKernel C J hdispersion p c m hc z).val.2.val.1‖ ^ 2 =
        ‖discardedOperator (radius m) (p.l2 z)‖ ^ 2 := by
  have hk : (profileChannelKernel C J hdispersion p c m hc z).val.2.val.1 =
      C.fourier (retainedOperator (radius m) (p.l2 z)) :=
    (profileChannelKernel C J hdispersion p c m hc z).property.symm.trans
      (physicalRetained_adjoint C m (p.l2 z))
  change ‖C.fourier (p.l2 z)‖ ^ 2 - _ = _
  rw [hk, C.fourier.norm_map, C.fourier.norm_map]
  linarith [square_partition_l2 (radius m) (p.l2 z)]

section Spatial
variable {X : Type*} [MeasurableSpace X] (ν : Measure X)
  (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
  (position : X → ι × FieldSpace) (hposition : AEStronglyMeasurable position ν)

def profileChannelVacuum : SpatialRadiationGraph ν →L[ℂ]
    Space (fun _ : ℕ => SpatialPhotonSpace ν) :=
  spatialChannelVacuum ν BF CCR (transportSplit C.fourier (complexOnePhotonIsometry (radius m)))
    (fun x => profileChannelKernel C J hdispersion p c m hc (position x))
    ((profileChannelKernel_continuous C J hdispersion p c m hc).comp_aestronglyMeasurable hposition)
    (profileChannelKernelBound C J p c)
    (ae_of_all _ fun x => profileChannelKernel_bound C J hdispersion p c m hc (position x))

theorem profileChannelVacuum_orthogonal (u : SpatialRadiationGraph ν) (v : SpatialPhotonSpace ν) :
    ⟪KrausL2.lift ν ((photonFactorization BF).factor
      (transportSplit C.fourier (complexOnePhotonIsometry (radius m)))) v,
      profileChannelVacuum C J hdispersion p c m hc ν BF CCR position hposition u⟫_ℂ = 0 :=
  spatialChannelVacuum_orthogonal ν BF CCR _ _ _ _ _ u v

/-- The actual discarded kernel controls the spatial vacuum correction. -/
theorem profileChannelVacuum_bound (ε : ℝ) (hε : 0 ≤ ε)
    (hdiscard : ∀ᵐ x ∂ν, ‖discardedOperator (radius m) (p.l2 (position x))‖ ≤ ε)
    (u : SpatialRadiationGraph ν) :
    ‖profileChannelVacuum C J hdispersion p c m hc ν BF CCR position hposition u‖ ≤
      ε * ‖spatialRadiationInclusion ν u‖ := by
  apply spatialChannelVacuum_norm_le ν BF CCR _ _ _ _ _ ε hε _ u
  filter_upwards [hdiscard] with x hx
  rw [profileChannelKernel_mass_loss]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

theorem profileChannelVacuum_supported_bound (ε : ℝ) (hε : 0 ≤ ε)
    (u : SpatialRadiationGraph ν)
    (hdiscard : ∀ᵐ x ∂ν, u x ≠ 0 →
      ‖discardedOperator (radius m) (p.l2 (position x))‖ ≤ ε) :
    ‖profileChannelVacuum C J hdispersion p c m hc ν BF CCR position hposition u‖ ≤
      ε * ‖spatialRadiationInclusion ν u‖ := by
  apply spatialChannelVacuum_supported_norm_le ν BF CCR _ _ _ _ _ ε hε u
  filter_upwards [hdiscard] with x hx
  intro hu
  rw [profileChannelKernel_mass_loss]
  exact pow_le_pow_left₀ (norm_nonneg _) (hx hu) 2

end Spatial
end GptLean.PhysicalFock
