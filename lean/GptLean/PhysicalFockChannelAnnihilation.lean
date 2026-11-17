import GptLean.PhysicalFockChannelFields

/-!
The retained annihilation graph intertwines the actual Fock channel.
The tensor pair-sector identity identifies each coordinate of the full
output. Summability has already been proved by the form pullback, so
there is no additional domain or graph-density assumption.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory UniformSpace TensorCoordinates TensorSectors
  PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

private theorem tensorMap_ext {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup L] [NormedSpace ℂ L]
    (A B : TensorSpace H K →L[ℂ] L)
    (h : ∀ v w, A (tensor v w) = B (tensor v w)) : A = B := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq A.continuous B.continuous
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero]
    | tmul v w => exact h v w
    | add u v hu hv => simp only [Completion.coe_add, map_add, hu, hv]

private theorem pair_retained_sector
    (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    [∀ n, CompleteSpace (K n)] (n r s : ℕ) (z : TensorSpace (Space K) (Space K)) :
    pairCoefficients K (retainedOperator (sector K n) z) (r, s) =
      if r = n then pairCoefficients K z (r, s) else 0 := by
  let A := (pairCoordinate K (r, s)).comp (retainedOperator (sector K n))
  let B : TensorSpace (Space K) (Space K) →L[ℂ] TensorSpace (K r) (K s) :=
    if r = n then pairCoordinate K (r, s) else 0
  have he : A = B := tensorMap_ext A B (by
    intro v w
    by_cases h : r = n
    · subst r
      change pairCoefficients K (retainedOperator (sector K n) (tensor v w)) (n, s) =
        (if n = n then pairCoordinate K (n, s) else 0) (tensor v w)
      rw [ite_eq_left rfl, retainedOperator_tensor, pairCoefficients_tensor,
        pairCoordinate_apply, pairCoefficients_tensor, sector_coordinate]
    · change pairCoefficients K (retainedOperator (sector K n) (tensor v w)) (r, s) =
        (if r = n then pairCoordinate K (r, s) else 0) (tensor v w)
      rw [ite_eq_right h, zero_apply, retainedOperator_tensor,
        pairCoefficients_tensor, sector_coordinate_ne K n r h]
      exact map_zero (tensor.flip (w s)))
  have hz := congrArg (fun T : TensorSpace (Space K) (Space K) →L[ℂ]
    TensorSpace (K r) (K s) => T z) he
  change pairCoefficients K (retainedOperator (sector K n) z) (r, s) = B z at hz
  by_cases h : r = n
  · simpa only [B, h, ite_true, pairCoordinate_apply] using hz
  · simpa only [B, h, ite_false, zero_apply] using hz

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (C : CanonicalSectorCCR μ) (B : ConcreteExponentialLaw μ)
  (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
  (f : Lp ℂ 2 μ) (u v : Fock μ)
  (hv : ∀ n, v n = annihilationSector μ n ((retainedMap j).adjoint f) (u (n + 1)))

include C hv in
theorem split_annihilation_graph_pair (r s : ℕ) :
    firstTensorMap (annihilationSector μ r f)
      (pairCoefficients (Sector μ) (B.split μ j u) (r + 1, s)) =
        pairCoefficients (Sector μ) (B.split μ j v) (r, s) := by
  have hsector : photonSector μ (r + s) v =
      annihilationBlock μ (r + s) ((retainedMap j).adjoint f) u := by
    change lp.single 2 (r + s) (v (r + s)) =
      lp.single 2 (r + s) (annihilationSector μ (r + s) ((retainedMap j).adjoint f) (u (r + s + 1)))
    rw [hv]
  exact (split_pair_annihilation μ C B j f u r s).trans
    ((congrArg (fun w : Fock μ => pairCoefficients (Sector μ) (B.split μ j w) (r, s))
      hsector.symm).trans ((split_pair_eq_sector μ B j v (r, s)).symm))

include C hv in
theorem split_annihilation_graph_block (n : ℕ) :
    retainedOperator (annihilationBlock μ n f) (B.split μ j u) =
      retainedOperator (photonSector μ n) (B.split μ j v) := by
  apply (pairCoefficients (Sector μ)).injective
  apply lp.ext
  funext p
  rcases p with ⟨r, s⟩
  by_cases h : r = n
  · subst r
    have hp := pair_retained_sector (Sector μ) n n s (B.split μ j v)
    simp only [ite_true] at hp
    exact (pair_retained_annihilationBlock μ n s f (B.split μ j u)).trans
      ((split_annihilation_graph_pair μ C B j f u v hv n s).trans hp.symm)
  · have hp := pair_retained_sector (Sector μ) n r s (B.split μ j v)
    simp only [h, ite_false] at hp
    exact (pair_retained_annihilationBlock_off μ n r s h f (B.split μ j u)).trans hp.symm

include C hv in
theorem factorization_annihilation_graph
    (W : TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ] lp (fun _ : ℕ => Fock μ) 2)
    (hW : ∀ (A : Fock μ →L[ℂ] Fock μ) (z : TensorSpace (Fock μ) (Fock μ)) (a : ℕ),
      W (retainedOperator A z) a = A (W z a)) (a n : ℕ) :
    annihilationSector μ n f ((B.factorization μ W).factor j u a (n + 1)) =
      (B.factorization μ W).factor j v a n := by
  have he := congrArg (fun z : TensorSpace (Fock μ) (Fock μ) => W z a)
    (split_annihilation_graph_block μ C B j f u v hv n)
  have hb : annihilationBlock μ n f (W (B.split μ j u) a) =
      photonSector μ n (W (B.split μ j v) a) :=
    (hW (annihilationBlock μ n f) (B.split μ j u) a).symm.trans
      (he.trans (hW (photonSector μ n) (B.split μ j v) a))
  have hn := congrArg (fun w : Fock μ => w n) hb
  change (lp.single 2 n (annihilationSector μ n f (W (B.split μ j u) a (n + 1)))) n =
    (lp.single 2 n (W (B.split μ j v) a n)) n at hn
  change annihilationSector μ n f (W (B.split μ j u) a (n + 1)) =
    W (B.split μ j v) a n
  simpa only [lp.single_apply_self] using hn

end Generic

theorem photonFactorization_annihilation_graph
    (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (f : Lp ℂ 2 photonMeasure) (u v : PhotonFock)
    (hv : ∀ n, v n = annihilationSector photonMeasure n ((retainedMap j).adjoint f) (u (n + 1)))
    (a n : ℕ) :
    annihilationSector photonMeasure n f ((photonFactorization BF).factor j u a (n + 1)) =
      (photonFactorization BF).factor j v a n :=
  factorization_annihilation_graph photonMeasure C (photonExponential BF) j f u v hv
    (environmentalCoordinates PhotonFock) environmentalCoordinates_retainedOperator a n

theorem channelAnnihilation_eq_factor
    (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (f : Lp ℂ 2 photonMeasure) (k : WeightedPhotonKernel)
    (hk : (retainedMap j).adjoint f = k.val.1) (u : RadiationGraphSpace) :
    channelAnnihilation BF C j f k hk u =
      (photonFactorization BF).factor j (kernelAnnihilation k u) := by
  apply lp.ext
  funext a
  apply lp.ext
  funext n
  exact photonFactorization_annihilation_graph BF C j f (radiationGraphInclusion u)
    (kernelAnnihilation k u) (fun m => by rw [hk]; rfl) a n

end GptLean.PhysicalFock
