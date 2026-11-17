import GptLean.PhysicalCoulombReferenceCore

/-! The actual zero-potential reference and the Coulomb reference are the
same common electronic/radiation form domain, with equivalent norms. The
zero potential coordinate is reconstructed by a bounded linear map. The
resulting free-reference equivalence and existing Coulomb map preserve
all physical wave and field coordinates. -/

noncomputable section
namespace PfHk.PhysicalReferenceCoulombEquiv

open GptLean GptLean.PhysicalPFReference

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}

local instance radiationNormedSpace : NormedSpace ℂ PhysicalFock.RadiationGraphSpace :=
  PhysicalFock.radiationRoot.graph.normedSpace

local instance electronicNormedSpace {I : Type*} [Fintype I] [DecidableEq I] :
    NormedSpace ℂ (ElectronicGraph I) :=
  (ElectronicH1Complex.complexWeakGraph PhysicalFock.PhotonFock I).normedSpace

local instance freeNormedSpace {I : Type*} [Fintype I] [DecidableEq I] :
    NormedSpace ℂ (PhysicalFreeReferenceCore.FreeReference I) :=
  (PhysicalFreeReferenceCore.freeSubspace I).normedSpace

private def zeroPotential (I : Type*) [Fintype I] [DecidableEq I] :
    WaveSpace I →L[ℂ] PotentialGraph I (fun _ => 0) :=
  ((ContinuousLinearMap.id ℂ (WaveSpace I)).prod
    (0 : WaveSpace I →L[ℂ] WaveSpace I)).codRestrict
    (PhysicalMultiplicationGraph.graph MeasureTheory.volume
      (H := PhysicalFock.PhotonFock) (fun _ : Position I => (Real.sqrt (0 : ℝ) : ℂ))) (by
      intro w
      filter_upwards [MeasureTheory.Lp.coeFn_zero PhysicalFock.PhotonFock 2
        (MeasureTheory.volume : MeasureTheory.Measure (Position I))] with x hx
      change (0 : WaveSpace I) x = (Real.sqrt (0 : ℝ) : ℂ) • w x
      simpa only [Pi.zero_apply, Real.sqrt_zero, Complex.ofReal_zero, zero_smul] using hx)

private def forget (I : Type*) [Fintype I] [DecidableEq I] :
    Reference I (fun _ => 0) →L[ℂ] PhysicalFreeReferenceCore.FreeReference I :=
  ((electronic I (fun _ => 0)).prod (radiationSource I (fun _ => 0))).codRestrict
    (PhysicalFreeReferenceCore.freeSubspace I) (by
      intro q
      change inclusion I (fun _ => 0) q -
        PhysicalFock.spatialRadiationInclusion MeasureTheory.volume
          (radiationSource I (fun _ => 0) q) = 0
      exact sub_eq_zero.mpr (radiation_matches I (fun _ => 0) q).symm)

private theorem forget_injective (I : Type*) [Fintype I] [DecidableEq I] :
    Function.Injective (forget I) := by
  intro u v huv
  exact inclusion_injective I (fun _ => 0)
    (congrArg (PhysicalFreeReferenceCore.inclusion I) huv)

private def tripleMap {Q E F G : Type*}
    [TopologicalSpace Q] [AddCommGroup Q] [Module ℂ Q]
    [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℂ G]
    (a : Q →L[ℂ] E) (b : Q →L[ℂ] F) (p : E →L[ℂ] G) :
    Q →L[ℂ] E × F × G := a.prod (b.prod (p.comp a))

private def attachAmbient (I : Type*) [Fintype I] [DecidableEq I] :
    PhysicalFreeReferenceCore.FreeReference I →L[ℂ] Ambient I (fun _ => 0) :=
  tripleMap (Q := PhysicalFreeReferenceCore.FreeReference I)
    (E := ElectronicGraph I) (F := RadiationGraph I) (G := PotentialGraph I (fun _ => 0))
    (PhysicalFreeReferenceCore.electronic I) (PhysicalFreeReferenceCore.radiationSource I)
    ((zeroPotential I).comp (ElectronicH1Complex.value (E := PhysicalFock.PhotonFock) (I := I)))

private def attach (I : Type*) [Fintype I] [DecidableEq I] :
    PhysicalFreeReferenceCore.FreeReference I →L[ℂ] Reference I (fun _ => 0) :=
  (attachAmbient I).codRestrict (referenceSubspace I (fun _ => 0)) (by
    intro q
    change (ElectronicH1Complex.value (PhysicalFreeReferenceCore.electronic I q) -
      PhysicalFock.spatialRadiationInclusion MeasureTheory.volume
        (PhysicalFreeReferenceCore.radiationSource I q),
      PhysicalFreeReferenceCore.inclusion I q - PhysicalFreeReferenceCore.inclusion I q) = (0, 0)
    exact Prod.ext (sub_eq_zero.mpr (PhysicalFreeReferenceCore.value_matching I q))
      (sub_self _))

private theorem forget_attach (I : Type*) [Fintype I] [DecidableEq I]
    (q : PhysicalFreeReferenceCore.FreeReference I) : forget I (attach I q) = q := by
  apply Subtype.ext
  rfl

private theorem attach_forget (I : Type*) [Fintype I] [DecidableEq I]
    (u : Reference I (fun _ => 0)) : attach I (forget I u) = u := by
  apply inclusion_injective I (fun _ => 0)
  rfl

private def zeroFreeEquiv (I : Type*) [Fintype I] [DecidableEq I] :
    Reference I (fun _ => 0) ≃L[ℂ] PhysicalFreeReferenceCore.FreeReference I where
  toFun := forget I
  invFun := attach I
  left_inv := attach_forget I
  right_inv := forget_attach I
  map_add' := map_add (forget I)
  map_smul' a u := (forget I).map_smul' a u
  continuous_toFun := (forget I).continuous
  continuous_invFun := (attach I).continuous

private theorem zeroFreeEquiv_apply (I : Type*) [Fintype I] [DecidableEq I]
    (u : Reference I (fun _ => 0)) : zeroFreeEquiv I u = forget I u := rfl

private theorem inclusion_forget (I : Type*) [Fintype I] [DecidableEq I]
    (u : Reference I (fun _ => 0)) :
    PhysicalFreeReferenceCore.inclusion I (forget I u) = inclusion I (fun _ => 0) u := rfl

private theorem electronic_forget (I : Type*) [Fintype I] [DecidableEq I]
    (u : Reference I (fun _ => 0)) :
    PhysicalFreeReferenceCore.electronic I (forget I u) = electronic I (fun _ => 0) u := rfl

private theorem radiation_forget (I : Type*) [Fintype I] [DecidableEq I]
    (u : Reference I (fun _ => 0)) :
    PhysicalFreeReferenceCore.radiationSource I (forget I u) =
      radiationSource I (fun _ => 0) u := rfl

private theorem electronic_coulomb (c : ℝ) (hc : 0 ≤ c)
    (q : PhysicalCoulombReferenceCore.Free N) :
    electronic (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
      (PhysicalCoulombReferenceCore.referenceEquiv N c hc q) =
      PhysicalFreeReferenceCore.electronic (Fin N × Fin 3) q := rfl

private theorem radiation_coulomb (c : ℝ) (hc : 0 ≤ c)
    (q : PhysicalCoulombReferenceCore.Free N) :
    radiationSource (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
      (PhysicalCoulombReferenceCore.referenceEquiv N c hc q) =
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q := rfl

attribute [local irreducible] zeroFreeEquiv PhysicalCoulombReferenceCore.referenceEquiv

def equiv (c : ℝ) (hc : 0 ≤ c) :
    Reference (Fin N × Fin 3) (fun _ => 0) ≃L[ℂ]
      Reference (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) :=
  (zeroFreeEquiv (Fin N × Fin 3)).trans
    (PhysicalCoulombReferenceCore.referenceEquiv N c hc)

theorem inclusion_equiv (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    inclusion (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) (equiv (N := N) c hc u) =
      inclusion (Fin N × Fin 3) (fun _ => 0) u :=
  (PhysicalCoulombReferenceCore.inclusion_referenceEquiv N c hc
    (zeroFreeEquiv (Fin N × Fin 3) u)).trans
      ((congrArg (PhysicalFreeReferenceCore.inclusion (Fin N × Fin 3))
        (zeroFreeEquiv_apply (Fin N × Fin 3) u)).trans
          (inclusion_forget (Fin N × Fin 3) u))

theorem inclusion_symm (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)) :
    inclusion (Fin N × Fin 3) (fun _ => 0) ((equiv (N := N) c hc).symm u) =
      inclusion (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) u :=
  (inclusion_equiv (N := N) c hc ((equiv (N := N) c hc).symm u)).symm.trans
    (congrArg (inclusion (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X))
      ((equiv (N := N) c hc).apply_symm_apply u))

theorem electronic_equiv (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    electronic (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) (equiv (N := N) c hc u) =
      electronic (Fin N × Fin 3) (fun _ => 0) u :=
  (electronic_coulomb c hc (zeroFreeEquiv (Fin N × Fin 3) u)).trans
    ((congrArg (PhysicalFreeReferenceCore.electronic (Fin N × Fin 3))
      (zeroFreeEquiv_apply (Fin N × Fin 3) u)).trans
        (electronic_forget (Fin N × Fin 3) u))

theorem radiationSource_equiv (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    radiationSource (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) (equiv (N := N) c hc u) =
      radiationSource (Fin N × Fin 3) (fun _ => 0) u :=
  (radiation_coulomb c hc (zeroFreeEquiv (Fin N × Fin 3) u)).trans
    ((congrArg (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3))
      (zeroFreeEquiv_apply (Fin N × Fin 3) u)).trans
        (radiation_forget (Fin N × Fin 3) u))

theorem radiation_equiv (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    radiation (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) (equiv (N := N) c hc u) =
      radiation (Fin N × Fin 3) (fun _ => 0) u :=
  congrArg (PhysicalFock.spatialRadiationDerivative MeasureTheory.volume) (radiationSource_equiv (N := N) c hc u)

theorem ordinary_equiv (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (i : Fin N × Fin 3) :
    ordinary (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X) i (equiv (N := N) c hc u) =
      ordinary (Fin N × Fin 3) (fun _ => 0) i u :=
  congrArg (ElectronicH1Complex.derivative i) (electronic_equiv (N := N) c hc u)

open MeasureTheory GptLean.PhysicalFock

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ X ∂volume, ‖κ i X‖ ≤ M)

theorem field_equiv (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (i : Fin N × Fin 3) :
    field (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
      C κ hκ M hbound i (equiv (N := N) c hc u) =
      field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound i u :=
  congrArg (spatialField volume C (κ i) (hκ i) M (hbound i)) (radiationSource_equiv (N := N) c hc u)

theorem covariant_equiv (c : ℝ) (hc : 0 ≤ c) (e : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (i : Fin N × Fin 3) :
    covariant (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
      C κ hκ M hbound e i (equiv (N := N) c hc u) =
      covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u := by
  simp only [covariant_apply, ordinary_equiv, field_equiv]

end PfHk.PhysicalReferenceCoulombEquiv
