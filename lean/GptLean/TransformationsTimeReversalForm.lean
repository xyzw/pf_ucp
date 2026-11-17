import GptLean.TransformationsTimeReversalStates
import GptLean.TransformationsClosedForm

/-!
Time reversal and the closed Pauli--Fierz forms, the operator identities of
`prop-time-reversal`.

Let `Θ` act pointwise by an antiunitary `W` of the photon Fock space, with a
compatible antiunitary of the radiation graph, and suppose the field kernels
are odd. This file proves:

* `Θ` maps the form domain onto itself;
* on the form domain, `D (Θ v) = Θ̃ (D v)`, where `Θ̃` is `-Θ` on the covariant
  coordinates and `Θ` on the radiation and Coulomb coordinates. Thus
  `Θ Dᵢ Θ⁻¹ = -Dᵢ` and `Θ` commutes with `√H_rad` and the Coulomb root, as in
  `A-time-reversal`;
* `q(Θ v, Θ w) = conj q(v, w)`;
* for bounded real external potentials,
  `q^{w,-a}(Θ v, Θ v') = conj q^{w,a}(v, v')`.

Since `Θ` is antiunitary, `⟪Θ v, H' Θ v'⟫ = conj ⟪v, H v'⟫` is the form version
of `Θ H Θ⁻¹ = H'`. With the uniqueness part of the representation theorem for
closed forms, the last two statements are `H-time-reversal`,
`Θ H^{v,A} Θ⁻¹ = H^{v,-A}`, here for bounded potentials and the internal
Hamiltonian `H^{0,0}`. For the time reversal `Θ = (-1)^N 𝒞_J`, the oddness of the
kernels follows from `conj g_a(-k, λ) = g_a(k, λ)`.
-/

noncomputable section

namespace GptLean.TransformationsTimeReversal

open MeasureTheory PhysicalFock PhysicalPFReference TransformationsFock TransformationsClosedForm
  TransformationsKernelCovariance
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace'' : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

section General

variable {I : Type} [Fintype I] [DecidableEq I] (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock)

/-- The pointwise antiunitary as a conjugate-linear isometry of the wave space. -/
def antiWaveEquiv : WaveSpace I ≃ₗᵢ⋆[ℂ] WaveSpace I where
  toFun := antiWave W
  invFun := antiWave W.symm
  map_add' := antiWave_add W
  map_smul' := antiWave_smul W
  left_inv := antiWave_symm W
  right_inv := antiWave_symm_left W
  norm_map' := norm_antiWave W

/-- `Θ` conjugates inner products. -/
theorem inner_antiWave (v w : WaveSpace I) :
    ⟪antiWave W v, antiWave W w⟫_ℂ = starRingEnd ℂ ⟪v, w⟫_ℂ :=
  inner_antiunitary (antiWaveEquiv W) v w

omit [DecidableEq I] in
theorem antiWave_zero : antiWave W (0 : WaveSpace I) = 0 :=
  map_zero ((realCLM W).compLpL 2 (volume : Measure (Position I)))

/-- `Θ` commutes with real multiples. -/
theorem antiWave_real (c : ℝ) (y : WaveSpace I) :
    antiWave W ((c : ℂ) • y) = (c : ℂ) • antiWave W y :=
  (antiWave_smul W _ y).trans (congrArg (fun t : ℂ => t • antiWave W y) (Complex.conj_ofReal c))

/-- `Θ` commutes with multiplication by a bounded real function. -/
theorem multiplier_antiWave (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume) (B : ℝ)
    (hb : ∀ᵐ x ∂volume, |a x| ≤ B) (v : WaveSpace I) :
    PhotonLocalization.realL2Multiplier a ha B hb (antiWave W v) =
      antiWave W (PhotonLocalization.realL2Multiplier a ha B hb v) := by
  apply Lp.ext
  filter_upwards [PhotonLocalization.realL2Multiplier_apply a ha B hb (antiWave W v),
    antiWave_ae W v, antiWave_ae W (PhotonLocalization.realL2Multiplier a ha B hb v),
    PhotonLocalization.realL2Multiplier_apply a ha B hb v] with x h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg (fun y => a x • y) h₂).trans
    (((realCLM W).map_smul (a x) (v x)).symm.trans (h₃.trans (congrArg W h₄)).symm))

/-- `Θ` turns the vector potential `a` into `-a`. -/
theorem vectorMultiplier_negVector (P : BoundedPotential I) (i : I) (v : WaveSpace I) :
    P.negVector.vectorMultiplier i (antiWave W v) = -antiWave W (P.vectorMultiplier i v) := by
  apply Lp.ext
  filter_upwards [P.negVector.vectorMultiplier_ae i (antiWave W v), antiWave_ae W v,
    Lp.coeFn_neg (antiWave W (P.vectorMultiplier i v)), antiWave_ae W (P.vectorMultiplier i v),
    P.vectorMultiplier_ae i v] with x h₁ h₂ h₃ h₄ h₅
  refine h₁.trans ((congrArg (fun y => (-P.vector i x) • y) h₂).trans (Eq.trans ?_
    (h₃.trans (congrArg Neg.neg (h₄.trans (congrArg W h₅)))).symm))
  exact (neg_smul _ _).trans (congrArg Neg.neg ((realCLM W).map_smul (P.vector i x) (v x)).symm)

/-- Time reversal of form coordinates: `-Θ` on the covariant coordinates and
`Θ` on the radiation and Coulomb coordinates. -/
def outputReverse (x : EnergyOutput I) : EnergyOutput I :=
  WithLp.toLp 2 (Sum.elim (fun i => -antiWave W (x (Sum.inl i)))
    (fun n : Fin 2 => antiWave W (x (Sum.inr n))))

omit [DecidableEq I] in
theorem outputReverse_inl (x : EnergyOutput I) (i : I) :
    outputReverse W x (Sum.inl i) = -antiWave W (x (Sum.inl i)) := rfl

omit [DecidableEq I] in
theorem outputReverse_inr (x : EnergyOutput I) (n : Fin 2) :
    outputReverse W x (Sum.inr n) = antiWave W (x (Sum.inr n)) := rfl

theorem outputReverse_add (x y : EnergyOutput I) :
    outputReverse W (x + y) = outputReverse W x + outputReverse W y := by
  apply PiLp.ext
  intro z
  rcases z with i | n
  · exact (congrArg Neg.neg (antiWave_add W (x (Sum.inl i)) (y (Sum.inl i)))).trans (neg_add _ _)
  · exact antiWave_add W (x (Sum.inr n)) (y (Sum.inr n))

/-- `Θ̃` is antiunitary on form coordinates. -/
theorem inner_outputReverse (x y : EnergyOutput I) :
    ⟪outputReverse W x, outputReverse W y⟫_ℂ = starRingEnd ℂ ⟪x, y⟫_ℂ := by
  have hi (i : I) : ⟪outputReverse W x (Sum.inl i), outputReverse W y (Sum.inl i)⟫_ℂ =
      starRingEnd ℂ ⟪x (Sum.inl i), y (Sum.inl i)⟫_ℂ :=
    (congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ) (outputReverse_inl W x i)
      (outputReverse_inl W y i)).trans ((inner_neg_neg _ _).trans (inner_antiWave W _ _))
  have hn (n : Fin 2) : ⟪outputReverse W x (Sum.inr n), outputReverse W y (Sum.inr n)⟫_ℂ =
      starRingEnd ℂ ⟪x (Sum.inr n), y (Sum.inr n)⟫_ℂ :=
    inner_antiWave W _ _
  refine (inner_output _ _).trans (Eq.trans ?_ (congrArg (starRingEnd ℂ) (inner_output x y)).symm)
  rw [map_add, map_add, map_sum, Finset.sum_congr rfl fun i _ => hi i, hn 0, hn 1]

/-- The external part of the form coordinates is reversed with `a ↦ -a`. -/
theorem output_negVector (P : BoundedPotential I) (v : WaveSpace I) :
    P.negVector.output (antiWave W v) = outputReverse W (P.output v) := by
  apply PiLp.ext
  intro z
  rcases z with i | n
  · exact (congrArg (fun y => (Real.sqrt (1 / 2 : ℝ) : ℂ) • y)
      (vectorMultiplier_negVector W P i v)).trans ((smul_neg _ _).trans
        (congrArg Neg.neg (antiWave_real W _ (P.vectorMultiplier i v)).symm))
  · exact (antiWave_zero W).symm

variable (Wr : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace)
  (hincl : ∀ q, radiationGraphInclusion (Wr q) = W (radiationGraphInclusion q))
  (hderiv : ∀ q, radiationGraphDerivative (Wr q) = W (radiationGraphDerivative q))

include hincl in
/-- The inverse maps are compatible as well. -/
theorem inclusion_symm (q : RadiationGraphSpace) :
    radiationGraphInclusion (Wr.symm q) = W.symm (radiationGraphInclusion q) :=
  W.injective ((hincl (Wr.symm q)).symm.trans
    ((congrArg radiationGraphInclusion (Wr.apply_symm_apply q)).trans
      (W.apply_symm_apply _).symm))

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hodd : ∀ i x q, kernelField C (κ i x) (Wr q) = -W (kernelField C (κ i x) q)) (e : ℝ)

set_option hygiene false in
local notation "D" => energyOperator I V C κ hκ M hbound e

include hincl in
/-- **`Θ` preserves the form domain** in both directions. -/
theorem mem_domain_reverse (v : WaveSpace I) :
    antiWave W v ∈ (D).domain ↔ v ∈ (D).domain :=
  mem_domain_transport V C κ hκ M hbound e κ hκ M hbound e (antiWave W) (antiWave W.symm)
    (antiWave_symm W) (fun u => ⟨reverse W Wr hincl V u, inclusion_reverse W Wr hincl V u⟩)
    (fun u => ⟨reverse W.symm Wr.symm (inclusion_symm W Wr hincl) V u,
      inclusion_reverse W.symm Wr.symm (inclusion_symm W Wr hincl) V u⟩) v

include hodd hderiv in
/-- Time reversal acts on form coordinates of reference vectors by `Θ̃`. -/
theorem energyOutput_reverse (u : Reference I V) :
    energyOutput I V C κ hκ M hbound e (reverse W Wr hincl V u) =
      outputReverse W (energyOutput I V C κ hκ M hbound e u) := by
  apply PiLp.ext
  intro z
  rcases z with i | n
  · exact (energyOutput_inl I V C κ hκ M hbound e _ i).trans
      ((congrArg (fun y => (Real.sqrt (1 / 2 : ℝ) : ℂ) • y)
        (covariant_reverse W Wr hincl V C κ hκ M hbound hodd e i u)).trans
        ((smul_neg _ _).trans (congrArg Neg.neg
          (antiWave_real W _ (covariant I V C κ hκ M hbound e i u)).symm)))
  · rcases n with ⟨_ | _ | k, hk⟩
    · exact (energyOutput_rad I V C κ hκ M hbound e _).trans
        ((radiation_reverse W Wr hincl hderiv V u).trans
          (congrArg (antiWave W) (energyOutput_rad I V C κ hκ M hbound e u).symm))
    · exact (energyOutput_pot I V C κ hκ M hbound e _).trans
        ((potential_reverse W Wr hincl V u).trans
          (congrArg (antiWave W) (energyOutput_pot I V C κ hκ M hbound e u).symm))
    · exact absurd hk (by omega)

include hodd hderiv in
/-- **`A-time-reversal` on the form domain**: `D (Θ v) = Θ̃ (D v)`, that is,
`Θ Dᵢ Θ⁻¹ = -Dᵢ`, and `Θ` commutes with the radiation and Coulomb roots. -/
theorem energyOperator_reverse (v : (D).domain) :
    D ⟨antiWave W v, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e v).mpr v.2⟩ =
      outputReverse W (D v) :=
  Exists.elim (exists_reference V C κ hκ M hbound e v) fun u hu =>
    (energyOperator_reference V C κ hκ M hbound e (reverse W Wr hincl V u)
      ⟨antiWave W v, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e v).mpr v.2⟩
      ((inclusion_reverse W Wr hincl V u).trans (congrArg (antiWave W) hu))).trans
      ((energyOutput_reverse W Wr hincl hderiv V C κ hκ M hbound hodd e u).trans
        (congrArg (outputReverse W) (energyOperator_reference V C κ hκ M hbound e u v hu).symm))

include hodd hderiv in
/-- **Antiunitary invariance of the closed form**, `q(Θ v, Θ w) = conj q(v, w)`.
With domain preservation this is `Θ H^{0,0} Θ⁻¹ = H^{0,0}`. -/
theorem form_reverse (v w : (D).domain) :
    ⟪D ⟨antiWave W v, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e v).mpr v.2⟩,
      D ⟨antiWave W w, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e w).mpr w.2⟩⟫_ℂ =
      starRingEnd ℂ ⟪D v, D w⟫_ℂ :=
  (congrArg₂ (fun x y : EnergyOutput I => ⟪x, y⟫_ℂ)
    (energyOperator_reverse W Wr hincl hderiv V C κ hκ M hbound hodd e v)
    (energyOperator_reverse W Wr hincl hderiv V C κ hκ M hbound hodd e w)).trans
    (inner_outputReverse W _ _)

include hodd hderiv in
/-- **`H-time-reversal` for closed forms**: for bounded real external potentials,
`q^{w,-a}(Θ v, Θ v') = conj q^{w,a}(v, v')`, the form of
`Θ H^{w,a} Θ⁻¹ = H^{w,-a}`. -/
theorem externalForm_reverse (P : BoundedPotential I) (v w : (D).domain) :
    externalForm V C κ hκ M hbound e P.negVector
        ⟨antiWave W v, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e v).mpr v.2⟩
        ⟨antiWave W w, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e w).mpr w.2⟩ =
      starRingEnd ℂ (externalForm V C κ hκ M hbound e P v w) := by
  have hx (y : (D).domain) :
      D ⟨antiWave W y, (mem_domain_reverse W Wr hincl V C κ hκ M hbound e y).mpr y.2⟩ +
          P.negVector.output (antiWave W y) =
        outputReverse W (D y + P.output y) :=
    (congrArg₂ (· + ·) (energyOperator_reverse W Wr hincl hderiv V C κ hκ M hbound hodd e y)
      (output_negVector W P y)).trans (outputReverse_add W _ _).symm
  have hs : ⟪antiWave W (v : WaveSpace I), P.negVector.scalarMultiplier (antiWave W w)⟫_ℂ =
      starRingEnd ℂ ⟪(v : WaveSpace I), P.scalarMultiplier w⟫_ℂ :=
    (congrArg (fun y => ⟪antiWave W (v : WaveSpace I), y⟫_ℂ)
      (multiplier_antiWave W P.scalar P.scalar_measurable.aestronglyMeasurable P.scalarBound
        (ae_of_all _ P.scalar_bounded) w)).trans (inner_antiWave W _ _)
  refine (congrArg₂ (· + ·) ((congrArg₂ (fun x y : EnergyOutput I => ⟪x, y⟫_ℂ) (hx v) (hx w)).trans
    (inner_outputReverse W _ _)) hs).trans ?_
  exact (map_add (starRingEnd ℂ) _ _).symm

end General

section Physical

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ)
  (hKodd : ∀ z, kernelAnti reflection (photonReflection_dispersion (-1) norm_neg_one) (K z) =
    (-1 : ℂ) • K z)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM
set_option hygiene false in
local notation "DP" => energyOperator (Fin N × Fin 3) V C κP hκP M hbP e

/-- **Time reversal preserves the form domain.** -/
theorem mem_domain_reversal (v : WaveSpace (Fin N × Fin 3)) :
    reversal v ∈ (DP).domain ↔ v ∈ (DP).domain :=
  mem_domain_reverse photonReversal radiationReversal reversal_inclusion V C κP hκP M hbP e v

include hKodd in
/-- **`Θ H^{0,0} Θ⁻¹ = H^{0,0}`** for the time reversal `Θ = (-1)^N 𝒞_J`. -/
theorem form_reversal (v w : (DP).domain) :
    ⟪DP ⟨reversal v, (mem_domain_reversal V C K hK M hM e v).mpr v.2⟩,
      DP ⟨reversal w, (mem_domain_reversal V C K hK M hM e w).mpr w.2⟩⟫_ℂ =
      starRingEnd ℂ ⟪DP v, DP w⟫_ℂ :=
  form_reverse photonReversal radiationReversal reversal_inclusion reversal_derivative V C κP hκP
    M hbP (field_odd C K hKodd) e v w

include hKodd in
/-- **`H-time-reversal`**, `Θ H^{w,a} Θ⁻¹ = H^{w,-a}`, for bounded real external
potentials, as an identity of closed forms. -/
theorem externalForm_reversal (P : BoundedPotential (Fin N × Fin 3)) (v w : (DP).domain) :
    externalForm V C κP hκP M hbP e P.negVector
        ⟨reversal v, (mem_domain_reversal V C K hK M hM e v).mpr v.2⟩
        ⟨reversal w, (mem_domain_reversal V C K hK M hM e w).mpr w.2⟩ =
      starRingEnd ℂ (externalForm V C κP hκP M hbP e P v w) :=
  externalForm_reverse photonReversal radiationReversal reversal_inclusion reversal_derivative V C
    κP hκP M hbP (field_odd C K hKodd) e P v w

/-- **`H-time-reversal` for the article's form factors** with
`conj (g_a(-k, λ)) = g_a(k, λ)`. -/
theorem externalForm_reversal_physical {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : PhotonLocalizationPhysicalKernels.FormFactors photonMeasure (Fin 3))
    (hF : F.momentum = Prod.fst) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] T)
    (hpar : ∀ a (p : PhotonMode), starRingEnd ℂ (F.base a (-p.1, p.2)) = F.base a p)
    (P : BoundedPotential (Fin N × Fin 3))
    (v w : (energyOperator (Fin N × Fin 3) V C
      (PhysicalPFParticle.particleKernel (N := N) (PhysicalProfiles.momentumKernel F hF J))
      (PhysicalPFParticle.particleKernel_measurable (N := N) _
        (PhysicalProfiles.momentumKernel_continuous F hF J))
      (PhysicalProfiles.kernelBound F hF J)
      (PhysicalPFParticle.particleKernel_bound (N := N) _ _
        (PhysicalProfiles.momentumKernel_bound F hF J)) e).domain) :
    externalForm V C
        (PhysicalPFParticle.particleKernel (N := N) (PhysicalProfiles.momentumKernel F hF J))
        (PhysicalPFParticle.particleKernel_measurable (N := N) _
          (PhysicalProfiles.momentumKernel_continuous F hF J))
        (PhysicalProfiles.kernelBound F hF J)
        (PhysicalPFParticle.particleKernel_bound (N := N) _ _
          (PhysicalProfiles.momentumKernel_bound F hF J)) e P.negVector
        ⟨reversal v, (mem_domain_reversal V C _ (PhysicalProfiles.momentumKernel_continuous F hF J)
          _ (PhysicalProfiles.momentumKernel_bound F hF J) e v).mpr v.2⟩
        ⟨reversal w, (mem_domain_reversal V C _ (PhysicalProfiles.momentumKernel_continuous F hF J)
          _ (PhysicalProfiles.momentumKernel_bound F hF J) e w).mpr w.2⟩ =
      starRingEnd ℂ (externalForm V C
        (PhysicalPFParticle.particleKernel (N := N) (PhysicalProfiles.momentumKernel F hF J))
        (PhysicalPFParticle.particleKernel_measurable (N := N) _
          (PhysicalProfiles.momentumKernel_continuous F hF J))
        (PhysicalProfiles.kernelBound F hF J)
        (PhysicalPFParticle.particleKernel_bound (N := N) _ _
          (PhysicalProfiles.momentumKernel_bound F hF J)) e P v w) :=
  externalForm_reversal V C _ (PhysicalProfiles.momentumKernel_continuous F hF J) _
    (PhysicalProfiles.momentumKernel_bound F hF J) e
    (fun z => kernelAnti_reflection F hF J (-1) norm_neg_one hpar z.1 z.2) P v w

end Physical

end GptLean.TransformationsTimeReversal
