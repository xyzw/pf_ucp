import GptLean.PhysicalFockChannelAnnihilation
import GptLean.PhysicalFockFieldSymmetry
import GptLean.PhysicalFockRadiationCutoff

/-!
The complementary vacuum correction is constructed from actual creation.
It is orthogonal to the channel range, and its norm is exactly the lost
one-photon mass. These statements follow from sector adjointness, the
annihilation graph identity and the CCR on the same physical model.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

private theorem coordinate_creation_pairing
    {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    (u v c a : Space K) (hc : c 0 = 0)
    (h : ∀ n, ⟪c (n + 1), v (n + 1)⟫_ℂ = ⟪u n, a n⟫_ℂ) :
    ⟪c, v⟫_ℂ = ⟪u, a⟫_ℂ := by
  have hs := (lp.hasSum_inner (𝕜 := ℂ) c v).summable
  calc
    _ = ∑' n, ⟪c n, v n⟫_ℂ := lp.inner_eq_tsum c v
    _ = ∑' n, ⟪c (n + 1), v (n + 1)⟫_ℂ := by
      rw [hs.tsum_eq_zero_add, hc, inner_zero_left, zero_add]
    _ = ∑' n, ⟪u n, a n⟫_ℂ := tsum_congr h
    _ = _ := (lp.inner_eq_tsum u a).symm

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem creationOnDomain_duality (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ) (u v : Fock μ)
    (hu : annihilationForm μ f u < ⊤) (hv : annihilationForm μ f v < ⊤) :
    ⟪creationOnDomain μ C f u hu, v⟫_ℂ = ⟪u, annihilationOnDomain μ f v hv⟫_ℂ :=
  coordinate_creation_pairing u v _ _ rfl (fun n => annihilationSector_duality μ n f (u n) (v (n + 1)))

theorem profileCreationOutput_duality (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ)
    (u v : Space (fun _ : ℕ => Fock μ))
    (hu : (∑' a, annihilationForm μ f (u a)) < ⊤)
    (hv : (∑' a, annihilationForm μ f (v a)) < ⊤) :
    ⟪profileCreationOutput μ C f u hu, v⟫_ℂ =
      ⟪u, profileAnnihilationOutput μ f v hv⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr (fun a => creationOnDomain_duality μ C f (u a) (v a)
    ((ENNReal.le_tsum a).trans_lt hu) ((ENNReal.le_tsum a).trans_lt hv))

end Generic

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
  (f : Lp ℂ 2 photonMeasure) (k : WeightedPhotonKernel)
  (hk : (retainedMap j).adjoint f = k.val.1)

theorem channelCreation_duality (u v : RadiationGraphSpace) :
    ⟪channelCreation BF C j f k hk u, (photonFactorization BF).factor j (radiationGraphInclusion v)⟫_ℂ =
      ⟪(photonFactorization BF).factor j (radiationGraphInclusion u),
        channelAnnihilation BF C j f k hk v⟫_ℂ :=
  profileCreationOutput_duality photonMeasure C f _ _
    (channelAnnihilation_finite BF C j f k hk u)
    (channelAnnihilation_finite BF C j f k hk v)

def channelVacuum : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  channelCreation BF C j f k hk -
    ((photonFactorization BF).factor j).toContinuousLinearMap.comp (kernelCreation C k)

theorem channelVacuum_orthogonal_graph (u v : RadiationGraphSpace) :
    ⟪channelVacuum BF C j f k hk u,
      (photonFactorization BF).factor j (radiationGraphInclusion v)⟫_ℂ = 0 := by
  change ⟪channelCreation BF C j f k hk u -
    (photonFactorization BF).factor j (kernelCreation C k u),
    (photonFactorization BF).factor j (radiationGraphInclusion v)⟫_ℂ = 0
  have ha := congrArg
    (fun w : Space (fun _ : ℕ => PhotonFock) =>
      ⟪(photonFactorization BF).factor j (radiationGraphInclusion u), w⟫_ℂ)
    (channelAnnihilation_eq_factor BF C j f k hk v)
  have hc : ⟪channelCreation BF C j f k hk u,
      (photonFactorization BF).factor j (radiationGraphInclusion v)⟫_ℂ =
      ⟪radiationGraphInclusion u, kernelAnnihilation k v⟫_ℂ :=
    (channelCreation_duality BF C j f k hk u v).trans
      (ha.trans (((photonFactorization BF).factor j).inner_map_map _ _))
  have hr : ⟪(photonFactorization BF).factor j (kernelCreation C k u),
      (photonFactorization BF).factor j (radiationGraphInclusion v)⟫_ℂ =
      ⟪radiationGraphInclusion u, kernelAnnihilation k v⟫_ℂ :=
    (((photonFactorization BF).factor j).inner_map_map _ _).trans
      (kernelCreation_annihilation_duality C k u v)
  exact (inner_sub_left _ _ _).trans
    ((congrArg₂ (fun a b : ℂ => a - b) hc hr).trans (sub_self _))

theorem channelVacuum_orthogonal (u : RadiationGraphSpace) (v : PhotonFock) :
    ⟪channelVacuum BF C j f k hk u, (photonFactorization BF).factor j v⟫_ℂ = 0 := by
  have hc : Continuous (fun w : PhotonFock =>
      ⟪channelVacuum BF C j f k hk u, (photonFactorization BF).factor j w⟫_ℂ) := by fun_prop
  have ht := (hc.tendsto v).comp (energyCutoff_tendsto v)
  have hz (M : ℕ) :
      ⟪channelVacuum BF C j f k hk u, (photonFactorization BF).factor j (energyCutoff M v)⟫_ℂ = 0 :=
    channelVacuum_orthogonal_graph BF C j f k hk u (radiationEnergyCutoff M v)
  have hz' : (fun w : PhotonFock =>
      ⟪channelVacuum BF C j f k hk u, (photonFactorization BF).factor j w⟫_ℂ) ∘
        (fun M : ℕ => energyCutoff M v) = fun _ : ℕ => (0 : ℂ) := funext hz
  exact tendsto_nhds_unique ht (hz' ▸ tendsto_const_nhds)

theorem channelVacuum_orthogonal_left (u : RadiationGraphSpace) (v : PhotonFock) :
    ⟪(photonFactorization BF).factor j v, channelVacuum BF C j f k hk u⟫_ℂ = 0 := by
  have he := congrArg (starRingEnd ℂ) (channelVacuum_orthogonal BF C j f k hk u v)
  simpa only [inner_conj_symm, map_zero] using he

theorem channelCreation_norm_sq (u : RadiationGraphSpace) :
    ‖channelCreation BF C j f k hk u‖ ^ 2 =
      ‖kernelAnnihilation k u‖ ^ 2 + ‖f‖ ^ 2 * ‖radiationGraphInclusion u‖ ^ 2 := by
  have hm : annihilationForm photonMeasure k.val.1 (radiationGraphInclusion u) =
      ENNReal.ofReal (‖kernelAnnihilation k u‖ ^ 2) := by
    change (∑' n, ENNReal.ofReal (‖kernelAnnihilation k u n‖ ^ 2)) = _
    simpa only [weightedForm, one_mul] using massForm_eq (Sector photonMeasure) (kernelAnnihilation k u)
  have he := channelCreationOutput_mass BF C j f k hk u
  rw [hm, ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (by positivity)).mp he

private theorem isometric_defect_norm_sq {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H →ₗᵢ[ℂ] K) (v : K) (w : H) (h : ⟪v - U w, U w⟫_ℂ = 0) :
    ‖v - U w‖ ^ 2 = ‖v‖ ^ 2 - ‖w‖ ^ 2 := by
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - U w) (U w) h
  rw [sub_add_cancel, U.norm_map] at he
  linarith

/-- Exact complementary vacuum norm, before any physical cutoff estimate. -/
theorem channelVacuum_norm_sq (u : RadiationGraphSpace) :
    ‖channelVacuum BF C j f k hk u‖ ^ 2 =
      (‖f‖ ^ 2 - ‖k.val.1‖ ^ 2) * ‖radiationGraphInclusion u‖ ^ 2 := by
  have hp : ‖channelVacuum BF C j f k hk u‖ ^ 2 =
      ‖channelCreation BF C j f k hk u‖ ^ 2 - ‖kernelCreation C k u‖ ^ 2 :=
    isometric_defect_norm_sq ((photonFactorization BF).factor j)
      (channelCreation BF C j f k hk u) (kernelCreation C k u)
      (channelVacuum_orthogonal BF C j f k hk u (kernelCreation C k u))
  have hc := channelCreation_norm_sq BF C j f k hk u
  have hs := creationRadiation_norm_sq C k.val.1 k.val.2 k.property u
  change ‖kernelCreation C k u‖ ^ 2 = ‖kernelAnnihilation k u‖ ^ 2 +
    ‖k.val.1‖ ^ 2 * ‖radiationGraphInclusion u‖ ^ 2 at hs
  nlinarith only [hp, hc, hs]

private theorem map_add_defect {H K : Type*}
    [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]
    (U : H →ₗ[ℂ] K) (a b : H) (c d : K) (h : c = U a) :
    c + d = U (a + b) + (d - U b) := by
  rw [h, map_add]
  abel

theorem channelField_eq_factor_add_vacuum (u : RadiationGraphSpace) :
    channelField BF C j f k hk u =
      (photonFactorization BF).factor j (kernelField C k u) + channelVacuum BF C j f k hk u := by
  change channelAnnihilation BF C j f k hk u + channelCreation BF C j f k hk u =
    (photonFactorization BF).factor j (kernelAnnihilation k u + kernelCreation C k u) +
      (channelCreation BF C j f k hk u - (photonFactorization BF).factor j (kernelCreation C k u))
  exact map_add_defect ((photonFactorization BF).factor j).toLinearMap _ _ _ _
    (channelAnnihilation_eq_factor BF C j f k hk u)

end GptLean.PhysicalFock
