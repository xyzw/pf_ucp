import GptLean.PhysicalAttainment

/-!
The article's constrained searches and Lieb functional on the actual
fermionic Pauli--Fierz states, with Coulomb coefficient one.

The mixed search ranges over positive trace-one states with finite form
energy, without a photon-number restriction. The pure search ranges over
normalized fermionic vectors of finite form energy. Both constrain the
physical density and combined current in `PhysicalPairSpace.Pair`.

The shifted ground energy is written in its variational form, with the
scalar potential already including the diamagnetic shift. Its integral
formula uses the article's scalar and vector potential spaces. No spectral
operator realization of an external Hamiltonian is introduced here.
-/

noncomputable section

namespace GptLean.PhysicalAttainmentFunctionals

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhysicalPolarization PhysicalRemovalKernels PhysicalSobolevRealization
  PhysicalPhotonLocalizedNumber PhysicalPairSpace PhysicalPairDuality
  Gaussian SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] PhysicalPFReference.normalEnergy

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- Normalized fermionic vectors in the actual internal-energy form domain. -/
abbrev PureState := PhysicalPFStates.PureState (PhysicalRemoval.potential N 1) C
  (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e

/-- Positive trace-one fermionic normal states with finite internal energy. -/
abbrev MixedState := PhysicalRemoval.mixedState F χ 1 C B S e (N := N)

/-- The internal form energy of a pure state, evaluated on its rank-one trace. -/
def pureInternalEnergy (p : PureState F χ C B S e (N := N)) : ℝ≥0∞ :=
  (PhysicalRemoval.fullEnergy F χ 1 C B S e (N := N)).expectation
    ((B.realization (PhysicalPFReference.WaveSpace (Fin N × Fin 3))).rank.rankOne p.val)

/-- The internal form trace of a finite-energy density matrix. -/
def mixedInternalEnergy (m : MixedState F χ C B S e (N := N)) : ℝ≥0∞ :=
  (PhysicalRemoval.fullEnergy F χ 1 C B S e (N := N)).expectation m.val.val

theorem pureInternalEnergy_lt_top (p : PureState F χ C B S e (N := N)) :
    pureInternalEnergy F χ C B S e p < ⊤ := p.property.2.2

theorem mixedInternalEnergy_lt_top (m : MixedState F χ C B S e (N := N)) :
    mixedInternalEnergy F χ C B S e m < ⊤ := m.val.property.2.2

theorem pureModel_energy_eq (p : PureState F χ C B S e (N := N)) :
    (PhysicalAttainment.pureModel i F χ C B S e).energy p =
      (pureInternalEnergy F χ C B S e p).toReal := rfl

theorem mixedModel_energy_eq (m : MixedState F χ C B S e (N := N)) :
    (PhysicalRemoval.model i F χ 1 C B S e).energy m =
      (mixedInternalEnergy F χ C B S e m).toReal := rfl

theorem pureModel_energy_coe (p : PureState F χ C B S e (N := N)) :
    ((PhysicalAttainment.pureModel i F χ C B S e).energy p : EReal) =
      (pureInternalEnergy F χ C B S e p : EReal) :=
  EReal.coe_ennreal_toReal (pureInternalEnergy_lt_top F χ C B S e p).ne

theorem mixedModel_energy_coe (m : MixedState F χ C B S e (N := N)) :
    ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      (mixedInternalEnergy F χ C B S e m : EReal) :=
  EReal.coe_ennreal_toReal (mixedInternalEnergy_lt_top F χ C B S e m).ne

/-- `FLL-def`, with the empty constrained fiber assigned `⊤`. -/
def pureFunctional (d : Pair) : EReal :=
  ⨅ p : PureState F χ C B S e (N := N),
    ⨅ (_ : (PhysicalAttainment.pureModel i F χ C B S e).density p = d),
      ((PhysicalAttainment.pureModel i F χ C B S e).energy p : EReal)

/-- `FLcs-def`, over the article's finite-energy density matrices. -/
def mixedFunctional (d : Pair) : EReal :=
  ⨅ m : MixedState F χ C B S e (N := N),
    ⨅ (_ : (PhysicalRemoval.model i F χ 1 C B S e).density m = d),
      ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal)

theorem pureFunctional_eq_search (d : Pair) :
    pureFunctional i F χ C B S e d =
      DFT.search (PhysicalAttainment.pureModel i F χ C B S e) d := rfl

theorem mixedFunctional_eq_search (d : Pair) :
    mixedFunctional i F χ C B S e d =
      DFT.search (PhysicalRemoval.model i F χ 1 C B S e) d := rfl

/-- The pure search is literally the infimum of rank-one form energies. -/
theorem pureFunctional_eq_rankOneInf (d : Pair) :
    pureFunctional i F χ C B S e d =
      ⨅ p : PureState F χ C B S e (N := N),
        ⨅ (_ : (PhysicalAttainment.pureModel i F χ C B S e).density p = d),
          (pureInternalEnergy F χ C B S e p : EReal) := by
  apply iInf_congr
  intro p
  apply iInf_congr
  intro _
  exact pureModel_energy_coe i F χ C B S e p

/-- The mixed search is literally the infimum of internal form traces. -/
theorem mixedFunctional_eq_traceInf (d : Pair) :
    mixedFunctional i F χ C B S e d =
      ⨅ m : MixedState F χ C B S e (N := N),
        ⨅ (_ : (PhysicalRemoval.model i F χ 1 C B S e).density m = d),
          (mixedInternalEnergy F χ C B S e m : EReal) := by
  apply iInf_congr
  intro m
  apply iInf_congr
  intro _
  exact mixedModel_energy_coe i F χ C B S e m

theorem mixedFunctional_nonneg (d : Pair) : 0 ≤ mixedFunctional i F χ C B S e d :=
  DFT.lower_bound (PhysicalRemoval.model i F χ 1 C B S e) 0
    (fun _ => ENNReal.toReal_nonneg) d

/-- Finite values occur exactly at mixed-state representable physical pairs. -/
theorem mixedFunctional_lt_top_iff (d : Pair) :
    mixedFunctional i F χ C B S e d < ⊤ ↔
      d ∈ Set.range (PhysicalRemoval.model i F χ 1 C B S e).density :=
  DFT.representable_iff (PhysicalRemoval.model i F χ 1 C B S e) d

theorem mixedFunctional_eq_top_iff (d : Pair) :
    mixedFunctional i F χ C B S e d = ⊤ ↔
      ∀ m : MixedState F χ C B S e (N := N),
        (PhysicalRemoval.model i F χ 1 C B S e).density m ≠ d :=
  DFT.search_eq_top_iff (PhysicalRemoval.model i F χ 1 C B S e) d

/-- Rank-one inclusion gives the article's mixed-to-pure search inequality. -/
theorem mixedFunctional_le_pureFunctional (d : Pair) :
    mixedFunctional i F χ C B S e d ≤ pureFunctional i F χ C B S e d :=
  DFT.mixed_le_pure (PhysicalAttainment.pureModel i F χ C B S e)
    (PhysicalRemoval.model i F χ 1 C B S e)
    (PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e) d

/-- The variational shifted energy `shifted-energy`, on `X* × Y*`. -/
def shiftedGroundEnergy (a : Potential) : EReal :=
  ⨅ p : PureState F χ C B S e (N := N),
    (((PhysicalAttainment.pureModel i F χ C B S e).energy p +
      pairPotential a ((PhysicalAttainment.pureModel i F χ C B S e).density p) : ℝ) : EReal)

theorem shiftedGroundEnergy_eq_ground (a : Potential) :
    shiftedGroundEnergy i F χ C B S e a =
      DFT.ground (PhysicalAttainment.pureModel i F χ C B S e)
        (fun a d => pairPotential a d) a := rfl

/-- Spectral ensembles give the same shifted variational infimum over mixed states. -/
theorem shiftedGroundEnergy_eq_mixedInf (a : Potential) :
    shiftedGroundEnergy i F χ C B S e a =
      ⨅ m : MixedState F χ C B S e (N := N),
        (((PhysicalRemoval.model i F χ 1 C B S e).energy m +
          pairPotential a ((PhysicalRemoval.model i F χ 1 C B S e).density m) : ℝ) : EReal) :=
  PhysicalPFSpectralPair.ground_eq i (PhysicalRemoval.potential N 1) C
    (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e a

/-- The shifted pure-state potential infimum with the actual integral pairing. -/
theorem shiftedGroundEnergy_eq_integralInf (a : Potential) :
    shiftedGroundEnergy i F χ C B S e a =
      ⨅ p : PureState F χ C B S e (N := N),
        (((pureInternalEnergy F χ C B S e p).toReal +
          ((∫ x, a.1.val x * densityL1
            ((PhysicalAttainment.pureModel i F χ C B S e).density p) x) +
          ∫ x, inner ℝ (a.2.val x) (currentL1
            ((PhysicalAttainment.pureModel i F χ C B S e).density p) x)) : ℝ) : EReal) := by
  apply iInf_congr
  intro p
  exact congrArg (fun r : ℝ =>
    (((pureInternalEnergy F χ C B S e p).toReal + r : ℝ) : EReal))
    (pairPotential_eq_integral a ((PhysicalAttainment.pureModel i F χ C B S e).density p))

/-- `FL-def`, the supremum over the article's scalar and vector potentials. -/
def liebFunctional (d : Pair) : EReal :=
  ⨆ a : Potential, shiftedGroundEnergy i F χ C B S e a - (pairPotential a d : EReal)

theorem liebFunctional_eq_lieb (d : Pair) :
    liebFunctional i F χ C B S e d =
      DFT.lieb (PhysicalAttainment.pureModel i F χ C B S e)
        (fun a d => pairPotential a d) d := rfl

theorem liebFunctional_eq_integralSup (d : Pair) :
    liebFunctional i F χ C B S e d =
      ⨆ a : Potential, shiftedGroundEnergy i F χ C B S e a -
        (((∫ x, a.1.val x * densityL1 d x) +
          ∫ x, inner ℝ (a.2.val x) (currentL1 d x) : ℝ) : EReal) := by
  apply iSup_congr
  intro a
  exact congrArg (fun r : ℝ => shiftedGroundEnergy i F χ C B S e a - (r : EReal))
    (pairPotential_eq_integral a d)

/-- The density variational principle for the shifted energy. -/
theorem shiftedGroundEnergy_eq_pairInf (a : Potential) :
    shiftedGroundEnergy i F χ C B S e a =
      ⨅ d : Pair, pureFunctional i F χ C B S e d + (pairPotential a d : EReal) :=
  DFT.density_variational_principle (PhysicalAttainment.pureModel i F χ C B S e)
    (fun a d => pairPotential a d) a

private theorem energy_eq_toReal {r : ℝ} {z : EReal} (h : (r : EReal) = z) :
    r = z.toReal := (EReal.toReal_coe r).symm.trans (congrArg EReal.toReal h)

variable (BF : StandardSymmetricFockExponential) (BW : StandardWienerSegal)
  (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ) (Sob : StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : StandardFractionalHardy)
  (hLp : StandardFiniteDimensionalLpRepresentation) (hFM : StandardDualFenchelMoreau)

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- `thm-unrestricted-attainment` in the article's functional notation.
The constant is chosen before the density-current pair. The stronger
number estimate for every optimizer follows from the same construction. -/
theorem unrestricted_attainment (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      (∀ d, mixedFunctional i F χ C B S e d < ⊤ →
        ∃ m : MixedState F χ C B S e (N := N),
          (PhysicalRemoval.model i F χ 1 C B S e).density m = d ∧
          (mixedInternalEnergy F χ C B S e m : EReal) = mixedFunctional i F χ C B S e d ∧
          PhysicalRemoval.number F χ 1 C B S e m ≤ ENNReal.ofReal
            (Cnumber * (1 + (mixedFunctional i F χ C B S e d).toReal)) ∧
          PhysicalRemoval.number F χ 1 C B S e m < ⊤) ∧
      (∀ m : MixedState F χ C B S e (N := N),
        (mixedInternalEnergy F χ C B S e m : EReal) =
          mixedFunctional i F χ C B S e ((PhysicalRemoval.model i F χ 1 C B S e).density m) →
        PhysicalRemoval.number F χ 1 C B S e m ≤ ENNReal.ofReal
          (Cnumber * (1 + (mixedFunctional i F χ C B S e
            ((PhysicalRemoval.model i F χ 1 C B S e).density m)).toReal))) ∧
      LowerSemicontinuous (mixedFunctional i F χ C B S e) ∧
      (∀ d, mixedFunctional i F χ C B S e d = liebFunctional i F χ C B S e d) := by
  obtain ⟨Cnumber, hCnumber, hatt, hnumber, hlsc, heq⟩ :=
    PhysicalAttainment.all_conclusions i F χ C B S BF BW e core smooth C₀ scaled B₀ B₁
      basis index Sob Rellich Hardy hLp hFM he hC₀
  refine ⟨Cnumber, hCnumber, ?_, ?_, hlsc, heq⟩
  · intro d hd
    obtain ⟨m, hm, henergy, hn, hfinite⟩ := hatt d hd
    have hvalue : (PhysicalRemoval.model i F χ 1 C B S e).energy m =
        (mixedFunctional i F χ C B S e d).toReal := energy_eq_toReal henergy
    refine ⟨m, hm, (mixedModel_energy_coe i F χ C B S e m).symm.trans henergy, ?_, hfinite⟩
    exact hn.trans_eq (congrArg (fun r : ℝ => ENNReal.ofReal (Cnumber * (1 + r))) hvalue)
  · intro m hm
    have henergy := (mixedModel_energy_coe i F χ C B S e m).trans hm
    have hvalue := energy_eq_toReal henergy
    exact (hnumber m henergy).trans_eq
      (congrArg (fun r : ℝ => ENNReal.ofReal (Cnumber * (1 + r))) hvalue)

end GptLean.PhysicalAttainmentFunctionals
