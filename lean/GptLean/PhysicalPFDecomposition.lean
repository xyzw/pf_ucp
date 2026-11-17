import GptLean.PhysicalCovariantJointDomain
import GptLean.PhysicalSpatialPotential
import GptLean.PhysicalPFRadiation

/-!
The actual full Pauli–Fierz expectation is the sum of its covariant
kinetic, Coulomb, and radiation expectations on every positive normal
operator. The joint-domain converse covers infinite energies as well.
-/

noncomputable section

namespace GptLean.PhysicalPFDecomposition

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhotonLocalizationChannel RemovalState PhysicalCovariantKinetic
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem decomposition_from_finite {W Q : Type*}
    (E K P R : W → ℝ≥0∞) (f : Q → W)
    (hf : ∀ w, E w < ⊤ → ∃ q, f q = w)
    (hcommon : ∀ w, K w < ⊤ → R w < ⊤ → E w < ⊤)
    (hgraph : ∀ q, E (f q) = K (f q) + P (f q) + R (f q)) (w : W) :
    E w = K w + P w + R w := by
  by_cases he : E w < ⊤
  · obtain ⟨q, rfl⟩ := hf w he
    exact hgraph q
  · have het : E w = ⊤ := top_unique (not_lt.mp he)
    by_cases hk : K w < ⊤
    · by_cases hr : R w < ⊤
      · exact (he (hcommon w hk hr)).elim
      · have hrt : R w = ⊤ := top_unique (not_lt.mp hr)
        simp only [het, hrt, add_top]
    · have hkt : K w = ⊤ := top_unique (not_lt.mp hk)
      simp only [het, hkt, top_add]

private theorem normal_eq_of_rankOne {H T : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    {A : Gaussian.RankOneData H T} (normal : NormalTraceData A) (F : NormalFunctionalData A)
    (E K P R : PositiveForm (positiveTrace normal F))
    (h : ∀ v, E.expectation (A.rankOne v) = K.expectation (A.rankOne v) +
      P.expectation (A.rankOne v) + R.expectation (A.rankOne v))
    {x : T} (hx : x ∈ A.positive) :
    E.expectation x = K.expectation x + P.expectation x + R.expectation x := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have he (G : PositiveForm (positiveTrace normal F)) :
      G.expectation x = ∑' n, G.expectation (A.rankOne (v n)) := by
    rw [← hv.tsum_eq]
    exact G.expectation_tsum hv.summable (fun n => A.rankOne_positive (v n))
  rw [he E, he K, he P, he R]
  simp only [h, ENNReal.tsum_add]

private theorem ofReal_energy (k r p : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r) (hp : 0 ≤ p) :
    ENNReal.ofReal (k + r + p) = ENNReal.ofReal k + ENNReal.ofReal p + ENNReal.ofReal r := by
  rw [ENNReal.ofReal_add (add_nonneg hk hr) hp, ENNReal.ofReal_add hk hr]
  ac_rfl

variable (N : ℕ) (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def coulombWeight : PhysicalPFReference.Position (Index N) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (potential N x)

theorem coulombWeight_measurable : Measurable (coulombWeight N) :=
  (measurable_const.mul (PhysicalCoulombH1.potential_measurable N)).ennreal_ofReal

def coulomb : PositiveForm (B.traceData (H := Wave N)) :=
  PhysicalSpatialPotential.normalForm volume (coulombWeight N) (coulombWeight_measurable N) B

def radiation : PositiveForm (B.traceData (H := Wave N)) :=
  PhysicalPFRadiation.normalRadiation (Index N) B

theorem coulomb_reference (u : Reference N) :
    (coulomb N B).expectation ((B.realization (Wave N)).rank.rankOne
      (PhysicalPFReference.inclusion (Index N) (potential N) u)) =
        ENNReal.ofReal (‖PhysicalPFReference.potential (Index N) (potential N) u‖ ^ 2) :=
  (PhysicalSpatialPotential.normalForm_rankOne volume (coulombWeight N)
    (coulombWeight_measurable N) B _).trans
      (PhysicalPFReference.potential_energy (Index N) (potential N)
        (fun x => mul_nonneg zero_le_one (PhysicalCoulombH1.potential_nonneg N x)) u).symm

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → PhysicalPFReference.Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

def energy := PhysicalPFReference.normalEnergy (Index N) (potential N) C κ hκ M hbound B S e
def kinetic := PhysicalCovariantKinetic.normalEnergy N C κ hκ M hbound e B S

theorem reference_decomposition (u : Reference N) :
    (energy N B S C κ hκ M hbound e).expectation
      ((B.realization (Wave N)).rank.rankOne (PhysicalPFReference.inclusion (Index N) (potential N) u)) =
    (kinetic N B S C κ hκ M hbound e).expectation
      ((B.realization (Wave N)).rank.rankOne (PhysicalPFReference.inclusion (Index N) (potential N) u)) +
    (coulomb N B).expectation
      ((B.realization (Wave N)).rank.rankOne (PhysicalPFReference.inclusion (Index N) (potential N) u)) +
    (radiation N B).expectation
      ((B.realization (Wave N)).rank.rankOne (PhysicalPFReference.inclusion (Index N) (potential N) u)) := by
  have he := PhysicalPFReference.normalEnergy_rankOne (Index N) (potential N) C κ hκ M hbound B S e u
  have hk := PhysicalCovariantKinetic.normalEnergy_reference N C κ hκ M hbound e B S u
  have hp := coulomb_reference N B u
  have hr := PhysicalPFRadiation.normalRadiation_reference (Index N) (potential N) B u
  have hkn : 0 ≤ PhysicalPFReference.kineticEnergy (Index N) (potential N) C κ hκ M hbound e u := by
    unfold PhysicalPFReference.kineticEnergy
    positivity
  exact he.trans ((ofReal_energy _ _ _ hkn (sq_nonneg _) (sq_nonneg _)).trans
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) hk.symm hp.symm) hr.symm))

theorem rankOne_decomposition (v : Wave N) :
    (energy N B S C κ hκ M hbound e).expectation ((B.realization (Wave N)).rank.rankOne v) =
      (kinetic N B S C κ hκ M hbound e).expectation ((B.realization (Wave N)).rank.rankOne v) +
      (coulomb N B).expectation ((B.realization (Wave N)).rank.rankOne v) +
      (radiation N B).expectation ((B.realization (Wave N)).rank.rankOne v) := by
  refine decomposition_from_finite
    (fun w => (energy N B S C κ hκ M hbound e).expectation
      ((B.realization (Wave N)).rank.rankOne w))
    (fun w => (kinetic N B S C κ hκ M hbound e).expectation
      ((B.realization (Wave N)).rank.rankOne w))
    (fun w => (coulomb N B).expectation ((B.realization (Wave N)).rank.rankOne w))
    (fun w => (radiation N B).expectation ((B.realization (Wave N)).rank.rankOne w))
    (PhysicalPFReference.inclusion (Index N) (potential N)) ?_ ?_ ?_ v
  · intro w hw
    exact (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff (Index N) (potential N)
      C κ hκ M hbound B S e w).mp hw
  · intro w hk hr
    exact finite_joint_domain N C κ hκ M hbound e B S w hk hr
  · exact reference_decomposition N B S C κ hκ M hbound e

theorem normal_decomposition {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive) :
    (energy N B S C κ hκ M hbound e).expectation x =
      (kinetic N B S C κ hκ M hbound e).expectation x +
        (coulomb N B).expectation x + (radiation N B).expectation x :=
  normal_eq_of_rankOne B.normal (B.realization (Wave N)).functional
    (energy N B S C κ hκ M hbound e) (kinetic N B S C κ hκ M hbound e)
    (coulomb N B) (radiation N B) (rankOne_decomposition N B S C κ hκ M hbound e) hx

end GptLean.PhysicalPFDecomposition
