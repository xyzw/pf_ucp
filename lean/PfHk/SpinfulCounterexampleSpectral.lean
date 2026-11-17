import PfHk.SpinfulCounterexampleSpectralRadial
import PfHk.SpinfulCounterexampleField

/-! Spectral estimates for the actual photon-valued electronic H1 space.
The retained background is the parameter-free circular Fourier/Sobolev
coordinate theorem. The hydrogenic lower bound, dependence on the magnetic
parameter, equality case and spin selection are proved here. -/

noncomputable section
namespace PfHk.SpinfulCounterexampleSpectral

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.ElectronicH1Complex
open scoped InnerProductSpace ENNReal Topology

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

local instance photonRealInner : InnerProductSpace ℝ PhotonFock :=
  CounterexampleSpectral.photonRealInner

abbrev Index := CounterexampleSpectral.Index
abbrev Space := CounterexampleSpectral.Space
abbrev Electronic := CounterexampleSpectral.Electronic
abbrev position := CounterexampleSpectral.position

attribute [local irreducible] ElectronicH1Complex.value ElectronicH1Complex.derivative

/-- The cylindrical angular form `⟨ψ, f(s) L_z ψ⟩`. -/
def rotationForm (q : Electronic) : ℝ :=
  ∑ j : Fin 3, ∫ X, SpinfulCounterexampleField.field (position X) j *
    (inner ℂ (value q X) ((-Complex.I) • derivative (0, j) q X)).re

/-- The spin-up Zeeman weight `∫ f(s)^2 |ψ|^2`. -/
def upWeight (q : Electronic) : ℝ :=
  ∫ X, SpinfulCounterexampleField.weight (position X) ^ 2 * ‖value q X‖ ^ 2

/-- The hydrogen form shifted by the ground-state energy, `Q_Z[ψ]`. -/
def hydrogenExcess (Z : ℝ) (q : Electronic) : ℝ :=
  CounterexampleSpectral.kinetic q - Z * CounterexampleSpectral.coulomb q +
    (Z ^ 2 / 2) * ‖value q‖ ^ 2

/-- The two spin blocks after the compensating scalar and diamagnetic
terms have been combined with the external Pauli form. -/
def spinEnergy (Z t : ℝ) (up down : Electronic) : ℝ :=
  (CounterexampleSpectral.kinetic up - Z * CounterexampleSpectral.coulomb up) +
    (CounterexampleSpectral.kinetic down - Z * CounterexampleSpectral.coulomb down) +
    t * (rotationForm up + rotationForm down) + 2 * t * upWeight up

/-- The standard unitary circular Fourier transform and its H1 Parseval
identities. Mode values contain the factor `sqrt s`, so their measure is
ordinary `ds dz` on `s > 0`. The profiles contain only parameter-free
multiplication and IBP identities. Neither Z nor t occurs in this
structure, and no spectral, magnetic-bound or equality conclusion is an
input. -/
structure StandardCylindricalDecomposition where
  profile : (m : ℤ) → Electronic → CylindricalProfile PhotonFock m
  summable_kinetic : ∀ q, Summable (fun m => modeKinetic m (profile m q))
  summable_coulomb : ∀ q,
    Summable (fun m => inner ℝ (profile m q).inverseRadius (profile m q).value)
  summable_norm : ∀ q, Summable (fun m => ‖(profile m q).value‖ ^ 2)
  summable_rotation : ∀ q,
    Summable (fun m : ℤ => (m : ℝ) * ‖(profile m q).rotationWeight‖ ^ 2)
  kinetic_decomposition : ∀ q, CounterexampleSpectral.kinetic q =
    ∑' m, modeKinetic m (profile m q)
  coulomb_decomposition : ∀ q, CounterexampleSpectral.coulomb q =
    ∑' m, inner ℝ (profile m q).inverseRadius (profile m q).value
  norm_decomposition : ∀ q, ‖value q‖ ^ 2 = ∑' m, ‖(profile m q).value‖ ^ 2
  rotation_decomposition : ∀ q, rotationForm q =
    ∑' m : ℤ, (m : ℝ) * ‖(profile m q).rotationWeight‖ ^ 2

attribute [local irreducible] rotationForm upWeight hydrogenExcess spinEnergy
  CounterexampleSpectral.kinetic CounterexampleSpectral.coulomb

/-! Scalar series algebra, kept away from the Hilbert-space types. -/

private theorem series_excess {ι : Type*} (K C N : ι → ℝ)
    (hK : Summable K) (hC : Summable C) (hN : Summable N) (Z : ℝ) :
    (∑' j, K j) - Z * (∑' j, C j) + (Z ^ 2 / 2) * (∑' j, N j) =
      ∑' j, (K j - Z * C j + (Z ^ 2 / 2) * N j) := by
  rw [(hK.sub (hC.mul_left Z)).tsum_add (hN.mul_left (Z ^ 2 / 2)),
    hK.tsum_sub (hC.mul_left Z), tsum_mul_left, tsum_mul_left]

private theorem abs_tsum_le {ι : Type*} (f g : ι → ℝ)
    (hf : Summable f) (hg : Summable g) (h : ∀ i, |f i| ≤ g i) :
    |∑' i, f i| ≤ ∑' i, g i := by
  refine abs_le.mpr ⟨?_, hf.tsum_le_tsum (fun i => (abs_le.mp (h i)).2) hg⟩
  rw [← tsum_neg]
  exact hg.neg.tsum_le_tsum (fun i => (abs_le.mp (h i)).1) hf

theorem excess_summable (D : StandardCylindricalDecomposition)
    (Z : ℝ) (q : Electronic) :
    Summable (fun m => modeExcess Z m (D.profile m q)) :=
  ((D.summable_kinetic q).sub ((D.summable_coulomb q).mul_left Z)).add
    ((D.summable_norm q).mul_left (Z ^ 2 / 2))

/-- The actual electronic energy excess is the sum of the proved mode
squares. -/
theorem excess_decomposition (D : StandardCylindricalDecomposition)
    (Z : ℝ) (q : Electronic) :
    hydrogenExcess Z q = ∑' m, modeExcess Z m (D.profile m q) := by
  have h := series_excess (fun m => modeKinetic m (D.profile m q))
    (fun m => inner ℝ (D.profile m q).inverseRadius (D.profile m q).value)
    (fun m => ‖(D.profile m q).value‖ ^ 2)
    (D.summable_kinetic q) (D.summable_coulomb q) (D.summable_norm q) Z
  rw [← D.kinetic_decomposition q, ← D.coulomb_decomposition q,
    ← D.norm_decomposition q] at h
  unfold hydrogenExcess
  exact h

theorem hydrogenExcess_nonneg (D : StandardCylindricalDecomposition)
    (Z : ℝ) (q : Electronic) : 0 ≤ hydrogenExcess Z q := by
  rw [excess_decomposition D]
  exact tsum_nonneg (fun m => mode_excess_nonneg Z m (D.profile m q))

/-- The angular form bound in the manuscript. The factor two comes from
the kinetic-energy normalization. -/
theorem rotation_abs_le (D : StandardCylindricalDecomposition)
    (Z : ℝ) (q : Electronic) : |rotationForm q| ≤ 2 * hydrogenExcess Z q := by
  rw [D.rotation_decomposition q, excess_decomposition D Z q, ← tsum_mul_left]
  exact abs_tsum_le _ _ (D.summable_rotation q) ((excess_summable D Z q).mul_left 2)
    (fun m => mode_rotation_abs_le Z m (D.profile m q))

/-- Coercive comparison with the hydrogen form. -/
theorem electronic_excess_lower (D : StandardCylindricalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : 0 ≤ t) (q : Electronic) :
    (1 - 2 * t) * hydrogenExcess Z q ≤ hydrogenExcess Z q + t * rotationForm q := by
  have h := mul_le_mul_of_nonneg_left (abs_le.mp (rotation_abs_le D Z q)).1 ht
  linarith

theorem upWeight_nonneg (q : Electronic) : 0 ≤ upWeight q := by
  unfold upWeight
  exact integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-! Generic weighted L2 facts. They are stated for an arbitrary normed
space so that no rewriting takes place inside the photon Fock space. -/

private theorem weight_sq_bound (w a : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha : 0 ≤ a) :
    ‖w ^ 2 * a‖ ≤ a := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg w) ha)]
  have hw2 : w ^ 2 ≤ 1 := by nlinarith
  nlinarith

private theorem lp_eq_zero_of_weighted {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (u : Lp E 2 μ) (w : α → ℝ)
    (hw : ∀ x, w x ≠ 0) (hi : Integrable (fun x => w x ^ 2 * ‖u x‖ ^ 2) μ)
    (h : (∫ x, w x ^ 2 * ‖u x‖ ^ 2 ∂μ) = 0) : u = 0 := by
  have hz := (integral_eq_zero_iff_of_nonneg
    (fun x => mul_nonneg (sq_nonneg (w x)) (sq_nonneg ‖u x‖)) hi).mp h
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero E 2 μ] with x hx h0
  have hv : ‖u x‖ ^ 2 = 0 := (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 (hw x))
  rw [h0]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hv)

theorem upWeight_integrable (q : Electronic) : Integrable
    (fun X => SpinfulCounterexampleField.weight (position X) ^ 2 * ‖value q X‖ ^ 2) volume := by
  have hn : Integrable (fun X => ‖value q X‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (value q))).mp
      (Lp.memLp (value q))
  have hpos : Measurable position := by
    unfold position CounterexampleSpectral.position SymmetricLift.particle
    fun_prop
  have hm : AEStronglyMeasurable
      (fun X => SpinfulCounterexampleField.weight (position X) ^ 2 * ‖value q X‖ ^ 2) volume :=
    ((SpinfulCounterexampleField.contDiff_weight.continuous.measurable.comp
      hpos).aestronglyMeasurable.pow 2).mul ((Lp.aestronglyMeasurable (value q)).norm.pow 2)
  exact hn.mono' hm (ae_of_all _ fun X => weight_sq_bound _ _
    (SpinfulCounterexampleField.weight_pos (position X)).le
    (SpinfulCounterexampleField.weight_le_one (position X)) (sq_nonneg _))

/-- The additional spin-up multiplication is strictly positive on every
nonzero L2 vector, although it need not have a uniform positive lower
bound. -/
theorem value_eq_zero_of_upWeight_eq_zero (q : Electronic) (h : upWeight q = 0) :
    value q = 0 := by
  unfold upWeight at h
  exact lp_eq_zero_of_weighted (value q) (fun X => SpinfulCounterexampleField.weight (position X))
    (fun X => (SpinfulCounterexampleField.weight_pos (position X)).ne') (upWeight_integrable q) h

/-- The block identity behind the manuscript's spinful lower bound. -/
theorem spinEnergy_shift (Z t : ℝ) (up down : Electronic) :
    spinEnergy Z t up down + (Z ^ 2 / 2) * (‖value up‖ ^ 2 + ‖value down‖ ^ 2) =
      (hydrogenExcess Z up + t * rotationForm up) +
        (hydrogenExcess Z down + t * rotationForm down) + 2 * t * upWeight up := by
  unfold spinEnergy hydrogenExcess
  ring

/-- The spinful energy lower bound, retaining the terms that determine
the equality case. -/
theorem spin_excess_lower (D : StandardCylindricalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : 0 ≤ t) (up down : Electronic) :
    (1 - 2 * t) * (hydrogenExcess Z up + hydrogenExcess Z down) + 2 * t * upWeight up ≤
      spinEnergy Z t up down +
        (Z ^ 2 / 2) * (‖value up‖ ^ 2 + ‖value down‖ ^ 2) := by
  have hu := electronic_excess_lower D Z ht up
  have hd := electronic_excess_lower D Z ht down
  rw [spinEnergy_shift]
  linarith

theorem spin_energy_lower_bound (D : StandardCylindricalDecomposition)
    (Z : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (up down : Electronic) :
    -(Z ^ 2 / 2) * (‖value up‖ ^ 2 + ‖value down‖ ^ 2) ≤ spinEnergy Z t up down := by
  have h := spin_excess_lower D Z ht0 up down
  have hn := add_nonneg (hydrogenExcess_nonneg D Z up) (hydrogenExcess_nonneg D Z down)
  have hp : 0 ≤ (1 - 2 * t) * (hydrogenExcess Z up + hydrogenExcess Z down) :=
    mul_nonneg (by linarith) hn
  have hw := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht0) (upWeight_nonneg up)
  linarith

/-- Equality removes spin up and forces the down-spin hydrogen equality
case before the photon vacuum is identified. -/
theorem spin_equality_parts (D : StandardCylindricalDecomposition)
    (Z : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) (up down : Electronic)
    (he : spinEnergy Z t up down =
      -(Z ^ 2 / 2) * (‖value up‖ ^ 2 + ‖value down‖ ^ 2)) :
    value up = 0 ∧ hydrogenExcess Z down = 0 := by
  have h := spin_excess_lower D Z ht0.le up down
  have hu := hydrogenExcess_nonneg D Z up
  have hd := hydrogenExcess_nonneg D Z down
  have hw := upWeight_nonneg up
  have hc : 0 < 1 - 2 * t := by linarith
  have hsum : (1 - 2 * t) * (hydrogenExcess Z up + hydrogenExcess Z down) +
      2 * t * upWeight up ≤ 0 := by linarith
  have hp1 : 0 ≤ (1 - 2 * t) * (hydrogenExcess Z up + hydrogenExcess Z down) :=
    mul_nonneg hc.le (add_nonneg hu hd)
  have hp2 : 0 ≤ 2 * t * upWeight up := mul_nonneg (by linarith) hw
  have hweight : upWeight up = 0 := by
    have h2 : 2 * t * upWeight up = 0 := le_antisymm (by linarith) hp2
    exact (mul_eq_zero.mp h2).resolve_left (mul_pos two_pos ht0).ne'
  have hs : hydrogenExcess Z up + hydrogenExcess Z down = 0 := by
    have h1 : (1 - 2 * t) * (hydrogenExcess Z up + hydrogenExcess Z down) = 0 :=
      le_antisymm (by linarith) hp1
    exact (mul_eq_zero.mp h1).resolve_left hc.ne'
  exact ⟨value_eq_zero_of_upWeight_eq_zero up hweight, by linarith⟩

/-- A vanishing hydrogen excess is the spherical equality hypothesis at
zero magnetic parameter. -/
theorem electronicEnergy_level (Z : ℝ) (q : Electronic) (h : hydrogenExcess Z q = 0) :
    CounterexampleSpectral.electronicEnergy Z 0 q = -(Z ^ 2 / 2) * ‖value q‖ ^ 2 := by
  unfold hydrogenExcess at h
  unfold CounterexampleSpectral.electronicEnergy
  linarith

/-- The ordinary spherical hydrogen equality theorem, with a complex
scalar coefficient. Its standard radial weak ODE input is reused. -/
theorem hydrogen_radial (S : CounterexampleSpectral.StandardSphericalDecomposition)
    (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
    {Z : ℝ} (hZ : 0 < Z) (q : Electronic) (h : hydrogenExcess Z q = 0) :
    ∃ c : PhotonFock, value q =ᵐ[volume] fun X =>
      ((Real.sqrt (Z ^ 3 / Real.pi) * Real.exp (-Z * ‖position X‖) : ℝ) : ℂ) • c := by
  have hex := CounterexampleSpectral.energy_equality_radial S O hZ
    (by norm_num : |(0 : ℝ)| < 1) q (electronicEnergy_level Z q h)
  rcases hex with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [hc] with X hX
  exact hX.trans (RCLike.real_smul_eq_coe_smul (K := ℂ)
    (Real.sqrt (Z ^ 3 / Real.pi) * Real.exp (-Z * ‖position X‖)) c)

/-- Equality removes spin up and identifies the surviving spatial factor. -/
theorem spin_equality_radial (D : StandardCylindricalDecomposition)
    (S : CounterexampleSpectral.StandardSphericalDecomposition)
    (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
    {Z t : ℝ} (hZ : 0 < Z) (ht0 : 0 < t) (ht1 : t < 1 / 2) (up down : Electronic)
    (he : spinEnergy Z t up down =
      -(Z ^ 2 / 2) * (‖value up‖ ^ 2 + ‖value down‖ ^ 2)) :
    value up = 0 ∧ ∃ c : PhotonFock, value down =ᵐ[volume] fun X =>
      ((Real.sqrt (Z ^ 3 / Real.pi) * Real.exp (-Z * ‖position X‖) : ℝ) : ℂ) • c :=
  ⟨(spin_equality_parts D Z ht0 ht1 up down he).1,
    hydrogen_radial S O hZ down (spin_equality_parts D Z ht0 ht1 up down he).2⟩

theorem rotationForm_eq_zero_of_hydrogenExcess_zero
    (D : StandardCylindricalDecomposition) (Z : ℝ) (q : Electronic)
    (h : hydrogenExcess Z q = 0) : rotationForm q = 0 := by
  have hb := rotation_abs_le D Z q
  rw [h, mul_zero] at hb
  exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))

end PfHk.SpinfulCounterexampleSpectral
