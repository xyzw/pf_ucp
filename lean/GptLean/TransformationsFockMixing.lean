import GptLean.TransformationsFockFamily
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option Elab.async false
set_option maxHeartbeats 400000

/-!
Second quantization of polarization-mixing unitaries.

Let `ν` be a σ-finite measure on a base space `X` and let `ι` be a finite set
of labels with counting measure. A fibre unitary is a measurable field
`x ↦ W x` of unitary `ι × ι` matrices. It acts on L² of `ν × count` by
`(W f)(x, a) = ∑ b, W x a b * f (x, b)`, and this is a unitary with inverse
given by the conjugate transpose field. On the full n-particle product space
the same rule with the product matrix `∏ i, W (x i) (a i) (b i)` gives a
unitary which commutes with every coordinate permutation and intertwines
tensor insertion with the one-particle map. Hence the fibre unitary defines a
sector family, and so a Fock unitary. Both the one-particle and the
n-particle maps commute with multiplication by functions of the base points
alone. For photons, with base space the momentum space and labels the two
polarizations, the family is therefore dispersive.

The analysis is done once, on a measure space `Z` identified with
`Y × ι` by a measure-preserving measurable equivalence. Almost every point
of `Y × ι` is characterized by its base point for every label, so changing
the label is quasi-measure-preserving, and the L² norm splits as an
integral over the base of a finite sum over labels. The one-particle space
is the case `Z = X × ι`, and the n-particle space is the case
`Z = Fin n → X × ι`, `Y = Fin n → X` with labels `Fin n → ι`, since the
product of counting measures is the counting measure.
-/

noncomputable section

namespace GptLean.TransformationsFock

open MeasureTheory Filter
open GptLean.PhysicalFock
open scoped ENNReal Matrix

section Algebra

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem norm_sq_ofReal_eq (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = star w * w := by
  rw [Complex.ofReal_pow, ← Complex.conj_mul', starRingEnd_apply]

/-- A matrix with orthonormal columns preserves the Euclidean norm. -/
theorem sum_norm_sq_mul (T : κ → κ → ℂ)
    (hT : ∀ b c, ∑ a, star (T a b) * T a c = if b = c then 1 else 0) (v : κ → ℂ) :
    ∑ a, ‖∑ b, T a b * v b‖ ^ 2 = ∑ b, ‖v b‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_sum]
  simp only [norm_sq_ofReal_eq]
  calc ∑ a, star (∑ b, T a b * v b) * ∑ c, T a c * v c
      = ∑ a, ∑ b, ∑ c, star (v b) * v c * (star (T a b) * T a c) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        rw [star_mul']
        ring
    _ = ∑ b, ∑ c, star (v b) * v c * ∑ a, star (T a b) * T a c := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ b, star (v b) * v b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hT, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem enorm_rpow_two_eq (z : ℂ) :
    ‖z‖ₑ ^ (2 : ℝ≥0∞).toReal = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.toReal_ofNat, ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg z)]

/-- The norm identity of `sum_norm_sq_mul` with extended nonnegative values. -/
theorem sum_enorm_sq_mul (T : κ → κ → ℂ)
    (hT : ∀ b c, ∑ a, star (T a b) * T a c = if b = c then 1 else 0) (v : κ → ℂ) :
    ∑ a, ‖∑ b, T a b * v b‖ₑ ^ (2 : ℝ≥0∞).toReal = ∑ b, ‖v b‖ₑ ^ (2 : ℝ≥0∞).toReal := by
  calc ∑ a, ‖∑ b, T a b * v b‖ₑ ^ (2 : ℝ≥0∞).toReal
      = ∑ a, ENNReal.ofReal (‖∑ b, T a b * v b‖ ^ 2) := by simp only [enorm_rpow_two_eq]
    _ = ENNReal.ofReal (∑ a, ‖∑ b, T a b * v b‖ ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun a _ => sq_nonneg ‖∑ b, T a b * v b‖).symm
    _ = ENNReal.ofReal (∑ b, ‖v b‖ ^ 2) := by rw [sum_norm_sq_mul T hT v]
    _ = ∑ b, ENNReal.ofReal (‖v b‖ ^ 2) :=
        ENNReal.ofReal_sum_of_nonneg fun b _ => sq_nonneg ‖v b‖
    _ = ∑ b, ‖v b‖ₑ ^ (2 : ℝ≥0∞).toReal := by simp only [enorm_rpow_two_eq]

/-- A left inverse matrix undoes the matrix action. -/
theorem sum_mul_sum_inv (S T : κ → κ → ℂ)
    (h : ∀ a c, ∑ b, S a b * T b c = if a = c then 1 else 0) (v : κ → ℂ) (a : κ) :
    ∑ b, S a b * ∑ c, T b c * v c = v a := by
  calc ∑ b, S a b * ∑ c, T b c * v c = ∑ c, (∑ b, S a b * T b c) * v c := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = v a := by
        simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype κ] in
theorem prod_boole_eq {n : ℕ} (b c : Fin n → κ) :
    (∏ i, if b i = c i then (1 : ℂ) else 0) = if b = c then 1 else 0 := by
  rw [Fintype.prod_boole]
  by_cases h : b = c
  · rw [ite_eq_left (fun i => congrFun h i), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (funext h')), ite_eq_right h]

/-- The tensor power of matrices with orthonormal columns has orthonormal columns. -/
theorem prod_orth {n : ℕ} (M : Fin n → κ → κ → ℂ)
    (hM : ∀ i b c, ∑ a, star (M i a b) * M i a c = if b = c then 1 else 0)
    (b c : Fin n → κ) :
    ∑ a : Fin n → κ, (∏ i, star (M i (a i) (b i))) * ∏ i, M i (a i) (c i) =
      if b = c then 1 else 0 := by
  calc ∑ a : Fin n → κ, (∏ i, star (M i (a i) (b i))) * ∏ i, M i (a i) (c i)
      = ∑ a : Fin n → κ, ∏ i, star (M i (a i) (b i)) * M i (a i) (c i) := by
        simp only [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ α, star (M i α (b i)) * M i α (c i) :=
        (Fintype.prod_sum fun i α => star (M i α (b i)) * M i α (c i)).symm
    _ = ∏ i, if b i = c i then (1 : ℂ) else 0 :=
        Finset.prod_congr rfl fun i _ => hM i (b i) (c i)
    _ = if b = c then 1 else 0 := prod_boole_eq b c

omit [DecidableEq κ] in
/-- Reindexing the label tuple by a permutation of the particles. -/
theorem sum_perm_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (A : Fin n → κ → ℂ)
    (v : (Fin n → κ) → ℂ) :
    ∑ b : Fin n → κ, (∏ i, A i (b i)) * v (fun j => b (π.symm j)) =
      ∑ c : Fin n → κ, (∏ j, A (π.symm j) (c j)) * v c := by
  refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl κ)) _ _ fun b => ?_
  change (∏ i, A i (b i)) * v (fun j => b (π.symm j)) =
    (∏ j, A (π.symm j) (b (π.symm j))) * v (fun j => b (π.symm j))
  rw [Equiv.prod_comp π.symm fun i => A i (b i)]

omit [DecidableEq κ] in
/-- Splitting the label tuple into its head and tail. -/
theorem sum_cons_split {n : ℕ} (A : Fin (n + 1) → κ → ℂ) (F : κ → ℂ) (G : (Fin n → κ) → ℂ) :
    ∑ b : Fin (n + 1) → κ, (∏ i, A i (b i)) * (F (b 0) * G (fun i => b i.succ)) =
      (∑ β, A 0 β * F β) * ∑ c : Fin n → κ, (∏ i, A i.succ (c i)) * G c := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.consEquiv fun _ => κ).symm _ _ fun b => ?_
  simp only [Fin.consEquiv_symm_apply, Fin.prod_univ_succ]
  change A 0 (b 0) * (∏ i : Fin n, A i.succ (b i.succ)) * (F (b 0) * G (fun i => b i.succ)) =
    A 0 (b 0) * F (b 0) * ((∏ i : Fin n, A i.succ (b i.succ)) * G (fun i => b i.succ))
  ring

end Algebra

/-- A measurable field of unitary matrices over a base space. -/
structure FibreUnitary (X ι : Type*) [MeasurableSpace X] [Fintype ι] [DecidableEq ι] where
  matrix : X → Matrix ι ι ℂ
  measurable : ∀ a b, Measurable fun x => matrix x a b
  unitary : ∀ x, (matrix x)ᴴ * matrix x = 1

namespace FibreUnitary

section Basic

variable {Y κ : Type*} [MeasurableSpace Y] [Fintype κ] [DecidableEq κ]
variable (W : FibreUnitary Y κ)

theorem mul_conjTranspose (y : Y) : W.matrix y * (W.matrix y)ᴴ = 1 :=
  mul_eq_one_comm.mp (W.unitary y)

/-- The columns of each matrix are orthonormal. -/
theorem col_orth (y : Y) (b c : κ) :
    ∑ a, star (W.matrix y a b) * W.matrix y a c = if b = c then 1 else 0 := by
  have h := congrFun (congrFun (W.unitary y) b) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa only [Matrix.conjTranspose_apply] using h

/-- The inverse field, given by the conjugate transpose matrices. -/
def symm : FibreUnitary Y κ where
  matrix y := (W.matrix y)ᴴ
  measurable a b := by
    simp only [Matrix.conjTranspose_apply]
    exact continuous_star.measurable.comp (W.measurable b a)
  unitary y := by
    show ((W.matrix y)ᴴ)ᴴ * (W.matrix y)ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact W.mul_conjTranspose y

@[simp] theorem symm_matrix (y : Y) : W.symm.matrix y = (W.matrix y)ᴴ := rfl

theorem symm_mul_apply (y : Y) (a c : κ) :
    ∑ b, W.symm.matrix y a b * W.matrix y b c = if a = c then 1 else 0 := by
  have h := congrFun (congrFun (W.unitary y) a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

theorem mul_symm_apply (y : Y) (a c : κ) :
    ∑ b, W.matrix y a b * W.symm.matrix y b c = if a = c then 1 else 0 := by
  have h := congrFun (congrFun (W.mul_conjTranspose y) a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

/-- The n-fold tensor power, a fibre unitary over `n`-tuples of base points with
`n`-tuples of labels. -/
def power (n : ℕ) : FibreUnitary (Fin n → Y) (Fin n → κ) where
  matrix y := Matrix.of fun a b => ∏ i, W.matrix (y i) (a i) (b i)
  measurable a b := Finset.measurable_prod _ fun i _ =>
    (W.measurable (a i) (b i)).comp (measurable_pi_apply i)
  unitary y := by
    ext b c
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]
    exact prod_orth (fun i => W.matrix (y i)) (fun i => W.col_orth (y i)) b c

theorem power_matrix (n : ℕ) (y : Fin n → Y) (a b : Fin n → κ) :
    (W.power n).matrix y a b = ∏ i, W.matrix (y i) (a i) (b i) := rfl

end Basic

end FibreUnitary

section ProdCount

variable {Y κ : Type*} [MeasurableSpace Y] [Fintype κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ] {ρ : Measure Y}

omit [MeasurableSingletonClass κ] in
/-- Almost every point of `Y × κ` has almost every base point, for every label. -/
theorem ae_prod_count_iff {P : Y × κ → Prop} :
    (∀ᵐ w ∂ρ.prod (Measure.count : Measure κ), P w) ↔ ∀ᵐ y ∂ρ, ∀ a, P (y, a) := by
  constructor
  · intro h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with y hy
    exact Measure.ae_count_iff.mp hy
  · intro h
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ρ)
      (ν := (Measure.count : Measure κ))).ae h] with w hw
    exact hw w.2

/-- The integral over `Y × κ` is the base integral of the sum over labels. -/
theorem lintegral_prod_count {g : Y × κ → ℝ≥0∞}
    (hg : AEMeasurable g (ρ.prod (Measure.count : Measure κ))) :
    ∫⁻ w, g w ∂ρ.prod (Measure.count : Measure κ) = ∫⁻ y, ∑ a, g (y, a) ∂ρ := by
  rw [lintegral_prod g hg]
  refine lintegral_congr fun y => ?_
  rw [lintegral_count, tsum_fintype]

end ProdCount

section Fibre

variable {Z Y κ : Type*} [MeasurableSpace Z] [MeasurableSpace Y] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ] {m : Measure Z} {ρ : Measure Y}
  (e : Z ≃ᵐ Y × κ) (he : MeasurePreserving e m (ρ.prod (Measure.count : Measure κ)))

include he

omit [DecidableEq κ] [MeasurableSingletonClass κ] in
theorem ae_fibre_iff {P : Z → Prop} :
    (∀ᵐ z ∂m, P z) ↔ ∀ᵐ y ∂ρ, ∀ a, P (e.symm (y, a)) := by
  constructor
  · intro h
    exact ae_prod_count_iff.mp ((MeasurePreserving.symm e he).quasiMeasurePreserving.ae h)
  · intro h
    have h' := (ae_prod_count_iff (P := fun w => P (e.symm w))).mpr h
    filter_upwards [he.quasiMeasurePreserving.ae h'] with z hz
    rwa [MeasurableEquiv.symm_apply_apply] at hz

omit [DecidableEq κ] [MeasurableSingletonClass κ] in
/-- An almost-everywhere statement survives every change of label. -/
theorem ae_relabel {P : Z → Prop} (h : ∀ᵐ z ∂m, P z) :
    ∀ᵐ z ∂m, ∀ b, P (e.symm ((e z).1, b)) := by
  refine (ae_fibre_iff e he (P := fun z => ∀ b, P (e.symm ((e z).1, b)))).mpr ?_
  filter_upwards [(ae_fibre_iff e he).mp h] with y hy a b
  simp only [MeasurableEquiv.apply_symm_apply]
  exact hy b

omit [Fintype κ] [DecidableEq κ] [MeasurableSingletonClass κ] he in
theorem measurable_relabel (b : κ) : Measurable fun z => e.symm ((e z).1, b) :=
  e.symm.measurable.comp (e.measurable.fst.prodMk measurable_const)

omit [DecidableEq κ] [MeasurableSingletonClass κ] in
theorem quasiMeasurePreserving_relabel (b : κ) :
    Measure.QuasiMeasurePreserving (fun z => e.symm ((e z).1, b)) m m := by
  refine ⟨measurable_relabel e b, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply (measurable_relabel e b) hs, measure_eq_zero_iff_ae_notMem]
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [ae_relabel e he h0] with z hz
  exact hz b

omit [DecidableEq κ] in
theorem lintegral_fibre {g : Z → ℝ≥0∞} (hg : AEMeasurable g m) :
    ∫⁻ z, g z ∂m = ∫⁻ y, ∑ a, g (e.symm (y, a)) ∂ρ := by
  rw [← (MeasurePreserving.symm e he).lintegral_comp_emb e.symm.measurableEmbedding g]
  exact lintegral_prod_count
    (hg.comp_quasiMeasurePreserving (MeasurePreserving.symm e he).quasiMeasurePreserving)

namespace FibreUnitary

variable (W : FibreUnitary Y κ)

omit he in
theorem measurable_entry (b : κ) : Measurable fun z => W.matrix (e z).1 (e z).2 b :=
  (measurable_from_prod_countable_left (f := fun w : Y × κ => W.matrix w.1 w.2 b)
    fun a => W.measurable a b).comp e.measurable

theorem aestronglyMeasurable_apply (f : Lp ℂ 2 m) :
    AEStronglyMeasurable
      (fun z => ∑ b, W.matrix (e z).1 (e z).2 b * f (e.symm ((e z).1, b))) m :=
  Finset.aestronglyMeasurable_fun_sum _ fun b _ =>
    (W.measurable_entry e b).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_relabel e he b))

theorem eLpNorm_apply (f : Lp ℂ 2 m) :
    eLpNorm (fun z => ∑ b, W.matrix (e z).1 (e z).2 b * f (e.symm ((e z).1, b))) 2 m =
      eLpNorm f 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    lintegral_fibre e he ((W.aestronglyMeasurable_apply e he f).enorm.pow_const _),
    lintegral_fibre e he ((Lp.aestronglyMeasurable f).enorm.pow_const _)]
  congr 1
  refine lintegral_congr fun y => ?_
  simp only [MeasurableEquiv.apply_symm_apply]
  exact sum_enorm_sq_mul (W.matrix y) (W.col_orth y) fun b => f (e.symm (y, b))

theorem memLp (f : Lp ℂ 2 m) :
    MemLp (fun z => ∑ b, W.matrix (e z).1 (e z).2 b * f (e.symm ((e z).1, b))) 2 m :=
  ⟨W.aestronglyMeasurable_apply e he f, by
    rw [W.eLpNorm_apply e he f]
    exact Lp.eLpNorm_lt_top f⟩

/-- The fibrewise matrix action as a linear map of L². -/
def toLinear : Lp ℂ 2 m →ₗ[ℂ] Lp ℂ 2 m where
  toFun f := (W.memLp e he f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(W.memLp e he (f + g)).coeFn_toLp, (W.memLp e he f).coeFn_toLp,
      (W.memLp e he g).coeFn_toLp, ae_relabel e he (Lp.coeFn_add f g),
      Lp.coeFn_add ((W.memLp e he f).toLp _) ((W.memLp e he g).toLp _)]
      with z h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, Pi.add_apply, h₂, h₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h₄ b, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(W.memLp e he (c • f)).coeFn_toLp, (W.memLp e he f).coeFn_toLp,
      ae_relabel e he (Lp.coeFn_smul c f),
      Lp.coeFn_smul c ((W.memLp e he f).toLp _)] with z h₁ h₂ h₃ h₄
    rw [h₁, RingHom.id_apply, h₄, Pi.smul_apply, h₂, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h₃ b, Pi.smul_apply, smul_eq_mul]
    ring

theorem toLinear_ae (f : Lp ℂ 2 m) :
    W.toLinear e he f =ᵐ[m] fun z => ∑ b, W.matrix (e z).1 (e z).2 b * f (e.symm ((e z).1, b)) :=
  (W.memLp e he f).coeFn_toLp

theorem norm_toLinear (f : Lp ℂ 2 m) : ‖W.toLinear e he f‖ = ‖f‖ := by
  change ‖(W.memLp e he f).toLp _‖ = ‖f‖
  rw [Lp.norm_toLp, W.eLpNorm_apply e he f, Lp.norm_def]

theorem toLinear_toLinear (V : FibreUnitary Y κ)
    (h : ∀ y a c, ∑ b, W.matrix y a b * V.matrix y b c = if a = c then 1 else 0)
    (f : Lp ℂ 2 m) : W.toLinear e he (V.toLinear e he f) = f := by
  apply Lp.ext
  filter_upwards [W.toLinear_ae e he (V.toLinear e he f),
    ae_relabel e he (V.toLinear_ae e he f)] with z h₁ h₂
  rw [h₁]
  simp only [h₂, MeasurableEquiv.apply_symm_apply]
  refine (sum_mul_sum_inv (W.matrix (e z).1) (V.matrix (e z).1) (h (e z).1)
    (fun c => f (e.symm ((e z).1, c))) (e z).2).trans ?_
  simp only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply]

/-- The fibrewise matrix action as a unitary of L². -/
def lpEquiv : Lp ℂ 2 m ≃ₗᵢ[ℂ] Lp ℂ 2 m where
  toLinearMap := W.toLinear e he
  invFun := W.symm.toLinear e he
  left_inv := W.symm.toLinear_toLinear e he W W.symm_mul_apply
  right_inv := W.toLinear_toLinear e he W.symm W.mul_symm_apply
  norm_map' := W.norm_toLinear e he

theorem lpEquiv_ae (f : Lp ℂ 2 m) :
    W.lpEquiv e he f =ᵐ[m] fun z => ∑ b, W.matrix (e z).1 (e z).2 b * f (e.symm ((e z).1, b)) :=
  W.toLinear_ae e he f

theorem lpEquiv_symm_apply (f : Lp ℂ 2 m) : (W.lpEquiv e he).symm f = W.symm.lpEquiv e he f :=
  rfl

/-- A multiplier which depends only on the base point commutes with the fibrewise action. -/
theorem lpEquiv_mul_ae (a : Z → ℂ) (ha : ∀ z b, a (e.symm ((e z).1, b)) = a z)
    {f g : Lp ℂ 2 m} (h : ∀ᵐ z ∂m, f z = a z * g z) :
    ∀ᵐ z ∂m, W.lpEquiv e he f z = a z * W.lpEquiv e he g z := by
  filter_upwards [W.lpEquiv_ae e he f, W.lpEquiv_ae e he g, ae_relabel e he h]
    with z h₁ h₂ h₃
  rw [h₁, h₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h₃ b, ha z b]
  ring

end FibreUnitary

end Fibre

section Mixing

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {ν : Measure X} [SigmaFinite ν]

omit [DecidableEq ι] in
/-- The product of counting measures is the counting measure. -/
theorem pi_count_eq (n : ℕ) :
    Measure.pi (fun _ : Fin n => (Measure.count : Measure ι)) = Measure.count := by
  refine Measure.ext_of_singleton fun a => ?_
  have h1 : (Measure.count : Measure (Fin n → ι)) {a} = 1 := Measure.count_singleton a
  have h2 : Measure.pi (fun _ : Fin n => (Measure.count : Measure ι)) {a} = 1 := by
    rw [← Set.univ_pi_singleton a, Measure.pi_pi]
    exact Finset.prod_eq_one fun i _ => Measure.count_singleton (a i)
  exact h2.trans h1.symm

omit [DecidableEq ι] in
/-- Splitting n-particle points into base points and labels preserves measure. -/
theorem measurePreserving_sector (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n))
      (SectorMeasure (ν.prod (Measure.count : Measure ι)) n)
      ((Measure.pi fun _ : Fin n => ν).prod (Measure.count : Measure (Fin n → ι))) := by
  have h := measurePreserving_arrowProdEquivProdArrow X ι (Fin n) (fun _ => ν)
    (fun _ => (Measure.count : Measure ι))
  rw [pi_count_eq] at h
  exact h

private theorem mix_piCongrLeft {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (π : Equiv.Perm (Fin n)) (k : Fin n → Ω) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k = fun j => k (π.symm j) := by
  funext j
  obtain ⟨i, rfl⟩ := π.surjective j
  rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

private theorem mix_ae_head {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {n : ℕ} {P : Ω → Prop} (h : ∀ᵐ p ∂μ, P p) :
    ∀ᵐ k ∂SectorMeasure μ (n + 1), P (k 0) :=
  (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n + 1) => μ) (i := 0)).eventually h

private theorem mix_ae_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {n : ℕ} {P : (Fin n → Ω) → Prop} (h : ∀ᵐ v ∂SectorMeasure μ n, P v) :
    ∀ᵐ k ∂SectorMeasure μ (n + 1), P (fun i : Fin n => k i.succ) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  have h2 : ∀ᵐ z ∂μ.prod (SectorMeasure μ n), P z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ)).ae h
  exact hp.quasiMeasurePreserving.ae h2

omit [DecidableEq ι] [MeasurableSingletonClass ι] [SigmaFinite ν] in
/-- An almost-everywhere statement on `X × ι` survives every change of label. -/
theorem ae_label_relabel {P : X × ι → Prop}
    (h : ∀ᵐ p ∂ν.prod (Measure.count : Measure ι), P p) :
    ∀ᵐ p ∂ν.prod (Measure.count : Measure ι), ∀ b, P (p.1, b) := by
  have h' := ae_prod_count_iff.mp h
  exact ae_prod_count_iff.mpr (by
    filter_upwards [h'] with x hx a b
    exact hx b)

omit [DecidableEq ι] in
/-- An almost-everywhere statement on the n-particle space survives every change of
the labels. -/
theorem ae_sector_relabel {n : ℕ} {P : (Fin n → X × ι) → Prop}
    (h : ∀ᵐ k ∂SectorMeasure (ν.prod (Measure.count : Measure ι)) n, P k) :
    ∀ᵐ k ∂SectorMeasure (ν.prod (Measure.count : Measure ι)) n,
      ∀ b : Fin n → ι, P (fun i => ((k i).1, b i)) :=
  ae_relabel (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n))
    (measurePreserving_sector n) h

namespace FibreUnitary

variable (W : FibreUnitary X ι)

/-- The one-particle unitary `(W f)(x, a) = ∑ b, W x a b * f (x, b)`. -/
def oneUnitary :
    Lp ℂ 2 (ν.prod (Measure.count : Measure ι)) ≃ₗᵢ[ℂ] Lp ℂ 2 (ν.prod (Measure.count : Measure ι)) :=
  W.lpEquiv (MeasurableEquiv.refl (X × ι)) (MeasurePreserving.id _)

omit [SigmaFinite ν] in
theorem oneUnitary_ae (f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))) :
    W.oneUnitary f =ᵐ[ν.prod (Measure.count : Measure ι)]
      fun p => ∑ b, W.matrix p.1 p.2 b * f (p.1, b) :=
  W.toLinear_ae (MeasurableEquiv.refl (X × ι)) (MeasurePreserving.id _) f

omit [SigmaFinite ν] in
theorem oneUnitary_symm_apply (f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))) :
    W.oneUnitary.symm f = W.symm.oneUnitary f := rfl

omit [SigmaFinite ν] in
/-- The one-particle formula for any representative of the argument. -/
theorem oneUnitary_eq_ae {f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))} {g : X × ι → ℂ}
    (hf : f =ᵐ[ν.prod (Measure.count : Measure ι)] g) :
    W.oneUnitary f =ᵐ[ν.prod (Measure.count : Measure ι)]
      fun p => ∑ b, W.matrix p.1 p.2 b * g (p.1, b) := by
  filter_upwards [W.oneUnitary_ae f, ae_label_relabel hf] with p h₁ h₂
  rw [h₁]
  exact Finset.sum_congr rfl fun b _ => by rw [h₂ b]

/-- The n-particle unitary
`(Wₙ u)(k) = ∑ b, (∏ i, W (k i).1 (k i).2 (b i)) * u (fun i => ((k i).1, b i))`. -/
def sectorUnitary (n : ℕ) :
    FullSector (ν.prod (Measure.count : Measure ι)) n ≃ₗᵢ[ℂ]
      FullSector (ν.prod (Measure.count : Measure ι)) n :=
  (W.power n).lpEquiv (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n))
    (measurePreserving_sector n)

theorem sectorUnitary_ae (n : ℕ) (u : FullSector (ν.prod (Measure.count : Measure ι)) n) :
    W.sectorUnitary n u =ᵐ[SectorMeasure (ν.prod (Measure.count : Measure ι)) n] fun k =>
      ∑ b : Fin n → ι, (∏ i, W.matrix (k i).1 (k i).2 (b i)) * u (fun i => ((k i).1, b i)) :=
  (W.power n).toLinear_ae (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n))
    (measurePreserving_sector n) u

/-- The n-particle formula for any representative of the argument. -/
theorem sectorUnitary_eq_ae (n : ℕ) {u : FullSector (ν.prod (Measure.count : Measure ι)) n}
    {g : (Fin n → X × ι) → ℂ}
    (hu : u =ᵐ[SectorMeasure (ν.prod (Measure.count : Measure ι)) n] g) :
    W.sectorUnitary n u =ᵐ[SectorMeasure (ν.prod (Measure.count : Measure ι)) n] fun k =>
      ∑ b : Fin n → ι, (∏ i, W.matrix (k i).1 (k i).2 (b i)) * g (fun i => ((k i).1, b i)) := by
  filter_upwards [W.sectorUnitary_ae n u, ae_sector_relabel hu] with k h₁ h₂
  rw [h₁]
  exact Finset.sum_congr rfl fun b _ => by rw [h₂ b]

/-- The n-particle unitary commutes with every coordinate permutation. -/
theorem sectorUnitary_permutation (n : ℕ) (π : Equiv.Perm (Fin n))
    (u : FullSector (ν.prod (Measure.count : Measure ι)) n) :
    W.sectorUnitary n (permutation (ν.prod (Measure.count : Measure ι)) n π u) =
      permutation (ν.prod (Measure.count : Measure ι)) n π (W.sectorUnitary n u) := by
  have hσ := measurePreserving_piCongrLeft
    (fun _ : Fin n => ν.prod (Measure.count : Measure ι)) π
  apply Lp.ext
  filter_upwards [W.sectorUnitary_ae n (permutation (ν.prod (Measure.count : Measure ι)) n π u),
    ae_sector_relabel (permutation_ae (ν.prod (Measure.count : Measure ι)) n π u),
    permutation_ae (ν.prod (Measure.count : Measure ι)) n π (W.sectorUnitary n u),
    hσ.quasiMeasurePreserving.ae (W.sectorUnitary_ae n u)] with k h₁ h₂ h₃ h₄
  rw [h₁, h₃, Function.comp_apply, h₄]
  simp only [h₂, Function.comp_apply, mix_piCongrLeft]
  exact sum_perm_reindex π (fun i β => W.matrix (k i).1 (k i).2 β)
    (fun c => u (fun j => ((k (π.symm j)).1, c j)))

/-- The n-particle unitaries intertwine tensor insertion with the one-particle map. -/
theorem sectorUnitary_tensorInsertion (n : ℕ) (f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι)))
    (u : FullSector (ν.prod (Measure.count : Measure ι)) n) :
    W.sectorUnitary (n + 1) (tensorInsertion (ν.prod (Measure.count : Measure ι)) n f u) =
      tensorInsertion (ν.prod (Measure.count : Measure ι)) n (W.oneUnitary f)
        (W.sectorUnitary n u) := by
  apply Lp.ext
  filter_upwards [W.sectorUnitary_ae (n + 1)
      (tensorInsertion (ν.prod (Measure.count : Measure ι)) n f u),
    ae_sector_relabel (tensorInsertion_ae (ν.prod (Measure.count : Measure ι)) n f u),
    tensorInsertion_ae (ν.prod (Measure.count : Measure ι)) n (W.oneUnitary f)
      (W.sectorUnitary n u),
    mix_ae_head (n := n) (W.oneUnitary_ae f), mix_ae_tail (W.sectorUnitary_ae n u)]
    with k h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₃, h₄, h₅]
  simp only [h₂]
  exact sum_cons_split (fun i β => W.matrix (k i).1 (k i).2 β) (fun β => f ((k 0).1, β))
    (fun c => u (fun i => ((k i.succ).1, c i)))

/-- A fibre unitary is a sector family. -/
def family : SectorFamily (ν.prod (Measure.count : Measure ι)) where
  one := W.oneUnitary
  sector := W.sectorUnitary
  perm := W.sectorUnitary_permutation
  insert := W.sectorUnitary_tensorInsertion

@[simp] theorem family_one (f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))) :
    W.family.one f = W.oneUnitary f := rfl

@[simp] theorem family_sector (n : ℕ) (u : FullSector (ν.prod (Measure.count : Measure ι)) n) :
    W.family.sector n u = W.sectorUnitary n u := rfl

theorem family_one_ae (f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))) :
    W.family.one f =ᵐ[ν.prod (Measure.count : Measure ι)]
      fun p => ∑ b, W.matrix p.1 p.2 b * f (p.1, b) :=
  W.oneUnitary_ae f

theorem family_one_eq {f : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))} {g : X × ι → ℂ}
    (hf : f =ᵐ[ν.prod (Measure.count : Measure ι)] g) :
    W.family.one f =ᵐ[ν.prod (Measure.count : Measure ι)]
      fun p => ∑ b, W.matrix p.1 p.2 b * g (p.1, b) :=
  W.oneUnitary_eq_ae hf

theorem family_sector_ae (n : ℕ) (u : FullSector (ν.prod (Measure.count : Measure ι)) n) :
    W.family.sector n u =ᵐ[SectorMeasure (ν.prod (Measure.count : Measure ι)) n] fun k =>
      ∑ b : Fin n → ι, (∏ i, W.matrix (k i).1 (k i).2 (b i)) * u (fun i => ((k i).1, b i)) :=
  W.sectorUnitary_ae n u

omit [SigmaFinite ν] in
/-- A multiplier depending only on the base point commutes with the one-particle map. -/
theorem oneUnitary_mul_ae (a : X × ι → ℂ) (ha : ∀ p (b : ι), a (p.1, b) = a p)
    {f g : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))}
    (h : ∀ᵐ p ∂ν.prod (Measure.count : Measure ι), f p = a p * g p) :
    ∀ᵐ p ∂ν.prod (Measure.count : Measure ι), W.oneUnitary f p = a p * W.oneUnitary g p :=
  W.lpEquiv_mul_ae (MeasurableEquiv.refl (X × ι)) (MeasurePreserving.id _) a ha h

omit [SigmaFinite ν] in
theorem oneUnitary_symm_mul_ae (a : X × ι → ℂ) (ha : ∀ p (b : ι), a (p.1, b) = a p)
    {f g : Lp ℂ 2 (ν.prod (Measure.count : Measure ι))}
    (h : ∀ᵐ p ∂ν.prod (Measure.count : Measure ι), f p = a p * g p) :
    ∀ᵐ p ∂ν.prod (Measure.count : Measure ι),
      W.oneUnitary.symm f p = a p * W.oneUnitary.symm g p :=
  W.symm.lpEquiv_mul_ae (MeasurableEquiv.refl (X × ι)) (MeasurePreserving.id _) a ha h

/-- A multiplier depending only on the base points commutes with the n-particle map. -/
theorem sectorUnitary_mul_ae (n : ℕ) (a : (Fin n → X × ι) → ℂ)
    (ha : ∀ k (b : Fin n → ι), a (fun i => ((k i).1, b i)) = a k)
    {f g : FullSector (ν.prod (Measure.count : Measure ι)) n}
    (h : ∀ᵐ k ∂SectorMeasure (ν.prod (Measure.count : Measure ι)) n, f k = a k * g k) :
    ∀ᵐ k ∂SectorMeasure (ν.prod (Measure.count : Measure ι)) n,
      W.sectorUnitary n f k = a k * W.sectorUnitary n g k :=
  (W.power n).lpEquiv_mul_ae (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n))
    (measurePreserving_sector n) a ha h

theorem sectorUnitary_symm_mul_ae (n : ℕ) (a : (Fin n → X × ι) → ℂ)
    (ha : ∀ k (b : Fin n → ι), a (fun i => ((k i).1, b i)) = a k)
    {f g : FullSector (ν.prod (Measure.count : Measure ι)) n}
    (h : ∀ᵐ k ∂SectorMeasure (ν.prod (Measure.count : Measure ι)) n, f k = a k * g k) :
    ∀ᵐ k ∂SectorMeasure (ν.prod (Measure.count : Measure ι)) n,
      (W.sectorUnitary n).symm f k = a k * (W.sectorUnitary n).symm g k := by
  have hf : (W.sectorUnitary n).symm f = (W.power n).symm.lpEquiv
      (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n)) (measurePreserving_sector n) f :=
    (W.power n).lpEquiv_symm_apply _ _ f
  have hg : (W.sectorUnitary n).symm g = (W.power n).symm.lpEquiv
      (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n)) (measurePreserving_sector n) g :=
    (W.power n).lpEquiv_symm_apply _ _ g
  rw [hf, hg]
  exact (W.power n).symm.lpEquiv_mul_ae (MeasurableEquiv.arrowProdEquivProdArrow X ι (Fin n))
    (measurePreserving_sector n) a ha h

end FibreUnitary

end Mixing

section Photon

namespace FibreUnitary

/-- The second quantization data of a polarization-mixing photon unitary. -/
def photonFamily (W : FibreUnitary Gaussian.FieldSpace (Fin 2)) : SectorFamily photonMeasure :=
  W.family (ν := volume)

theorem photonFamily_one_ae (W : FibreUnitary Gaussian.FieldSpace (Fin 2))
    (f : Lp ℂ 2 photonMeasure) :
    W.photonFamily.one f =ᵐ[photonMeasure] fun p => ∑ b, W.matrix p.1 p.2 b * f (p.1, b) :=
  W.oneUnitary_ae (ν := volume) f

theorem photonFamily_one_eq (W : FibreUnitary Gaussian.FieldSpace (Fin 2))
    {f : Lp ℂ 2 photonMeasure} {g : PhotonMode → ℂ} (hf : f =ᵐ[photonMeasure] g) :
    W.photonFamily.one f =ᵐ[photonMeasure] fun p => ∑ b, W.matrix p.1 p.2 b * g (p.1, b) :=
  W.oneUnitary_eq_ae (ν := volume) hf

theorem photonFamily_sector_ae (W : FibreUnitary Gaussian.FieldSpace (Fin 2)) (n : ℕ)
    (u : FullSector photonMeasure n) :
    W.photonFamily.sector n u =ᵐ[SectorMeasure photonMeasure n] fun k =>
      ∑ b : Fin n → Fin 2, (∏ i, W.matrix (k i).1 (k i).2 (b i)) * u (fun i => ((k i).1, b i)) :=
  W.sectorUnitary_ae (ν := volume) n u

/-- A polarization-mixing photon unitary gives a dispersive sector family, because
the dispersion depends only on the momenta. -/
theorem photonFamily_dispersive (W : FibreUnitary Gaussian.FieldSpace (Fin 2)) :
    W.photonFamily.Dispersive :=
  ⟨fun n _ _ h => W.sectorUnitary_mul_ae (ν := volume) n
      (fun k => (Real.sqrt (sectorDispersion n k) : ℂ)) (fun _ _ => rfl) h,
    fun n _ _ h => W.sectorUnitary_symm_mul_ae (ν := volume) n
      (fun k => (Real.sqrt (sectorDispersion n k) : ℂ)) (fun _ _ => rfl) h,
    fun _ _ h => W.oneUnitary_mul_ae (ν := volume) (fun p => (Real.sqrt ‖p.1‖ : ℂ))
      (fun _ _ => rfl) h,
    fun _ _ h => W.oneUnitary_symm_mul_ae (ν := volume) (fun p => (Real.sqrt ‖p.1‖ : ℂ))
      (fun _ _ => rfl) h⟩

end FibreUnitary

end Photon

end GptLean.TransformationsFock
