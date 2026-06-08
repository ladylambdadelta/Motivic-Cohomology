import Boundary.LFunctions.ZetaAdmissibleFunction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Boundary admissible bump functions

This file owns the first concrete bump-function machinery on the admissible
carrier. The direct goal is to provide honest compactly supported smooth probes
that can be used as local interpolation data later on.

At the moment we record the centered smooth bump on `ℝ`, its basic support and
value-at-center properties, and the resulting one-point interpolation lemma for
admissible complex-valued test functions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped CompactlySupported

namespace ZetaAdmissibleFunction

/-- Translate an admissible function along the real line. -/
def translate (c : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := f.toZetaTestFunction'.translate c
  smooth := f.smooth.comp (contDiff_id.add contDiff_const)

/-- Reflect an admissible function across the origin. -/
def reflect (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := f.toZetaTestFunction'.reflect
  smooth := f.smooth.comp contDiff_neg

/-- Scale an admissible function by a real scalar on the real variable. -/
def scale (a : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := f.toZetaTestFunction'.scale a
  smooth := f.smooth.comp (contDiff_const.mul contDiff_id)

/-- Affine transport by `x ↦ a * x + c` on the real line. -/
def affineTransport (a c : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  translate c (scale a f)

/-- Sum of admissible functions is admissible. -/
def add (f g : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := f.toZetaTestFunction + g.toZetaTestFunction
  smooth := f.smooth.add g.smooth

/-- Scalar multiples of admissible functions are admissible. -/
def smul (a : ℂ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := a • f.toZetaTestFunction
  smooth := f.smooth.const_smul a

instance : Add ZetaAdmissibleFunction := ⟨add⟩

instance : SMul ℂ ZetaAdmissibleFunction := ⟨smul⟩

/-- The admissible function addition is pointwise. -/
theorem add_apply (f g : ZetaAdmissibleFunction) (x : ℝ) :
    add f g x = f x + g x := by
  rfl

/-- The admissible scalar action is pointwise. -/
theorem smul_apply (a : ℂ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    smul a f x = a * f x := by
  rfl

/-- The translated admissible function is pointwise translated. -/
theorem translate_apply (c : ℝ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    translate c f x = f (x + c) := by
  rfl

/-- Translation is additive in the function variable. -/
theorem translate_add (c : ℝ) (f g : ZetaAdmissibleFunction) :
    translate c (f + g) = translate c f + translate c g := by
  ext x
  simp [translate_apply, add_apply]

/-- The reflected admissible function is pointwise reflected. -/
theorem reflect_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    reflect f x = f (-x) := by
  rfl

/-- The scaled admissible function is pointwise scaled. -/
theorem scale_apply (a : ℝ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    scale a f x = f (a * x) := by
  rfl

/-- Scaling is additive in the function variable. -/
theorem scale_add (a : ℝ) (f g : ZetaAdmissibleFunction) :
    scale a (f + g) = scale a f + scale a g := by
  ext x
  simp [scale_apply, add_apply]

/-- Translation commutes with complex scalar multiplication. -/
theorem translate_smul (c : ℝ) (a : ℂ) (f : ZetaAdmissibleFunction) :
    translate c (a • f) = a • translate c f := by
  ext x
  simp [translate_apply, smul_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Reflection commutes with complex scalar multiplication. -/
theorem reflect_smul (a : ℂ) (f : ZetaAdmissibleFunction) :
    reflect (a • f) = a • reflect f := by
  ext x
  simp [reflect_apply, smul_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Scaling commutes with complex scalar multiplication. -/
theorem scale_smul (t : ℝ) (a : ℂ) (f : ZetaAdmissibleFunction) :
    scale t (a • f) = a • scale t f := by
  ext x
  simp [scale_apply, smul_apply, mul_comm, mul_left_comm, mul_assoc]

/-- The affine transport is pointwise affine. -/
theorem affineTransport_apply (a c : ℝ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c f x = f (a * x + c) := by
  simp [ZetaAdmissibleFunction.affineTransport, translate_apply, scale_apply, mul_add,
    add_comm, add_left_comm, add_assoc]

/-- Affine transport is additive in the function variable. -/
theorem affineTransport_add (a c : ℝ) (f g : ZetaAdmissibleFunction) :
    affineTransport a c (f + g) = affineTransport a c f + affineTransport a c g := by
  simp [ZetaAdmissibleFunction.affineTransport, translate_add, scale_add, add_comm, add_left_comm,
    add_assoc]

/-- Affine transport commutes with complex scalar multiplication. -/
theorem affineTransport_smul (a c : ℝ) (b : ℂ) (f : ZetaAdmissibleFunction) :
    affineTransport a c (b • f) = b • affineTransport a c f := by
  simp [ZetaAdmissibleFunction.affineTransport, translate_smul, scale_smul]

/-- Nonzero scalar multiplication does not change the support of an affine transport. -/
theorem support_affineTransport_smul (a c : ℝ) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (b • f)) = Function.support (affineTransport a c f) := by
  rw [affineTransport_smul, ZetaAdmissibleFunction.support_smul b hb]

/-- The support of an affinely transported nonzero scalar multiple is the affine pullback of the
original support. -/
theorem support_affineTransport_smul_eq (a c : ℝ) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (b • f)) =
      (fun x => a * x + c) ⁻¹' Function.support f := by
  rw [support_affineTransport_smul a c b hb, affineTransport_support]

/-- The support of the affine transport is the affine pullback of the original support. -/
theorem affineTransport_support (a c : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c f) =
      (fun x => a * x + c) ⁻¹' Function.support f := by
  ext x
  simp [Function.mem_support, ZetaAdmissibleFunction.affineTransport, translate_apply,
    scale_apply, mul_add, add_comm, add_left_comm, add_assoc]

/-- Affine transport preserves compact support. -/
theorem hasCompactSupport_affineTransport (a c : ℝ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport (affineTransport a c f) := by
  simpa [ZetaAdmissibleFunction.affineTransport] using hasCompactSupport_translate c (scale a f)

/-- Affine transport commutes with finite sums. -/
theorem affineTransport_sum {α : Type*} (a c : ℝ) (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    affineTransport a c (∑ i in s, f i) = ∑ i in s, affineTransport a c (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [ZetaAdmissibleFunction.affineTransport]
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, ZetaAdmissibleFunction.affineTransport, ih, affineTransport_add,
        add_comm, add_left_comm, add_assoc]

/-- Affine transport commutes with finite linear combinations. -/
theorem affineTransport_sum_smul {α : Type*} (a c : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) :
    affineTransport a c (∑ i in s, c' i • f i) = ∑ i in s, c' i • affineTransport a c (f i) := by
  classical
  simp [Finset.sum_apply, affineTransport_add, affineTransport_smul, Finset.sum_add_distrib,
    add_comm, add_left_comm, add_assoc]

/-- Affine transport of a finite translated/scaled family can be pushed down to the summands. -/
theorem affineTransport_sum_translate_smul {α : Type*} (a c d : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) :
    affineTransport a c (∑ i in s, c' i • translate d (f i)) =
      ∑ i in s, c' i • affineTransport a c (translate d (f i)) := by
  simpa using affineTransport_sum_smul (a := a) (c := c) (s := s) (c' := c')
    (f := fun i => translate d (f i))

/-- The support of an affinely transported finite sum is the affine pullback of the support of the
original finite sum. -/
theorem affineTransport_sum_support {α : Type*} (a c : ℝ) (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (∑ i in s, f i)) =
      (fun x => a * x + c) ⁻¹' Function.support (∑ i in s, f i) := by
  rw [affineTransport_support]

/-- The support of an affinely transported finite linear combination is contained in the affine
pullback of the union of the summands' supports. -/
theorem affineTransport_sum_smul_support_subset {α : Type*} (a c : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (∑ i in s, c' i • f i)) ⊆
      (fun x => a * x + c) ⁻¹' (s.biUnion fun i => Function.support (f i)) := by
  intro x hx
  have hsum :
      x ∈ Function.support (∑ i in s, c' i • f i) := by
    simpa [affineTransport_support] using hx
  exact hsum.trans (support_sum_smul_subset (s := s) (c := c') (f := f))

/-- The support of an affinely transported finite linear combination is the affine pullback of
the support of the untransported finite linear combination, hence is controlled by the union of
the summands' supports. -/
theorem affineTransport_sum_smul_support {α : Type*} (a c : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (∑ i in s, c' i • f i)) =
      (fun x => a * x + c) ⁻¹' Function.support (∑ i in s, c' i • f i) := by
  rw [affineTransport_support]

/-- The support of an affinely transported finite linear combination is controlled by the affine
pullback of the union of the supports of the summands. -/
theorem affineTransport_sum_smul_support_subset' {α : Type*} (a c : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (∑ i in s, c' i • f i)) ⊆
      (fun x => a * x + c) ⁻¹' (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_sum_smul_support]
  exact (support_sum_smul_subset (s := s) (c := c') (f := f))

/-- Transport after a translation is transport with shifted offset. -/
theorem affineTransport_translate (a c d : ℝ) (f : ZetaAdmissibleFunction) :
    affineTransport a c (translate d f) = affineTransport a (c + d) f := by
  ext x
  simp [ZetaAdmissibleFunction.affineTransport, translate_apply, scale_apply, add_comm,
    add_left_comm, add_assoc, mul_add]

/-- Transport after scaling is transport with the scaled affine parameters. -/
theorem affineTransport_scale (a b c : ℝ) (f : ZetaAdmissibleFunction) :
    affineTransport a c (scale b f) = affineTransport (b * a) (b * c) f := by
  ext x
  simp [ZetaAdmissibleFunction.affineTransport, translate_apply, scale_apply, mul_add,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Transport after reflection is transport by the reflected affine map. -/
theorem affineTransport_reflect (a c : ℝ) (f : ZetaAdmissibleFunction) :
    affineTransport a c (reflect f) = affineTransport (-a) (-c) f := by
  ext x
  simp [ZetaAdmissibleFunction.affineTransport, translate_apply, scale_apply, reflect_apply,
    add_comm, add_left_comm, add_assoc, mul_add, mul_comm, mul_left_comm, mul_assoc]

/-- Composing two affine transports is again an affine transport. -/
theorem affineTransport_compose (a c b d : ℝ) (f : ZetaAdmissibleFunction) :
    affineTransport a c (affineTransport b d f) =
      affineTransport (a * b) (b * c + d) f := by
  ext x
  simp [ZetaAdmissibleFunction.affineTransport, translate_apply, scale_apply, mul_add,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- The support of a composed affine transport is the pullback of the support of the original
probe under the composed affine map. -/
theorem affineTransport_compose_support (a c b d : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (affineTransport b d f)) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹' Function.support f := by
  rw [affineTransport_compose, affineTransport_support]

/-- A composed affine transport of a nonzero scalar multiple has the same exact support pullback
as the underlying probe. -/
theorem affineTransport_compose_smul_support (a c b d : ℝ) (t : ℂ) (ht : t ≠ 0)
    (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (affineTransport b d (t • f))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹' Function.support f := by
  rw [affineTransport_smul, affineTransport_compose_support, support_smul t ht]

/-- Affine transport commutes with the basic geometric moves after nonzero scalar multiplication. -/
theorem affineTransport_translate_smul (a c d : ℝ) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (translate d (b • f)) =
      b • affineTransport a (c + d) f := by
  rw [translate_smul, affineTransport_translate, affineTransport_smul, translate_apply]

/-- Affine transport commutes with scaling after nonzero scalar multiplication. -/
theorem affineTransport_scale_smul (a c t : ℝ) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (scale t (b • f)) =
      b • affineTransport (t * a) (t * c) f := by
  rw [scale_smul, affineTransport_scale, affineTransport_smul]

/-- Affine transport commutes with reflection after nonzero scalar multiplication. -/
theorem affineTransport_reflect_smul (a c : ℝ) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (reflect (b • f)) =
      b • affineTransport (-a) (-c) f := by
  rw [reflect_smul, affineTransport_reflect, affineTransport_smul]

/-- The support of an affinely transported finite linear combination of translated nonzero
scalar multiples is the affine pullback of the support of the untransported combination. -/
theorem affineTransport_sum_translate_smul_support {α : Type*} (a c d : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) =
      (fun x => a * x + c) ⁻¹'
        Function.support (∑ i in s, c' i • translate d (f i)) := by
  rw [affineTransport_support]

/-- The support of an affinely transported finite linear combination of translated nonzero
scalar multiples is controlled by the affine pullback of the translated summands' supports. -/
theorem affineTransport_sum_translate_smul_support_subset {α : Type*} (a c d : ℝ) (s : Finset α)
    (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) ⊆
      (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (translate d (f i))) := by
  rw [affineTransport_sum_translate_smul_support (a := a) (c := c) (d := d) (s := s)
      (c' := c') (f := f) hc']
  exact (support_sum_smul_subset (s := s) (c := c') (f := fun i => translate d (f i)))

/-- If all coefficients are nonzero, the transported support of a translated finite linear
combination is controlled by the support of the untranslated summands. -/
theorem affineTransport_sum_translate_smul_support_subset_support {α : Type*} (a c d : ℝ)
    (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) ⊆
      (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  intro x hx
  have hsub :
      x ∈ (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (translate d (f i))) := by
    exact affineTransport_sum_translate_smul_support_subset (a := a) (c := c) (d := d) (s := s)
      (c' := c') (f := f) hc' hx
  rcases Finset.mem_biUnion.mp hsub with ⟨i, hi, hxi⟩
  have htrans : Function.support (translate d (f i)) = (fun x => x - d) ⁻¹' Function.support (f i) :=
    support_translate d (f i)
  rw [htrans] at hxi
  exact Finset.mem_biUnion.2 ⟨i, hi, hxi⟩

/-- If all coefficients are nonzero, the transported translated finite linear combination has
support controlled directly by the original summands. -/
theorem affineTransport_sum_translate_smul_support_subset_original {α : Type*} (a c d : ℝ)
    (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) ⊆
      (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  exact affineTransport_sum_translate_smul_support_subset_support (a := a) (c := c) (d := d)
    (s := s) (c' := c') (f := f) hc'

/-- If all coefficients are nonzero, the transported translated finite linear combination has
support given exactly by the affine pullback of the translated summands' supports. -/
theorem affineTransport_sum_translate_smul_support_eq {α : Type*} (a c d : ℝ)
    (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) =
      (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (translate d (f i))) := by
  rw [affineTransport_sum_translate_smul_support (a := a) (c := c) (d := d) (s := s)
      (c' := c') (f := f) hc']

/-- If all coefficients are nonzero, the transported translated finite linear combination has
support given exactly by the affine pullback of the original summands' supports. -/
theorem affineTransport_sum_translate_smul_support_eq_original {α : Type*} (a c d : ℝ)
    (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) =
      (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_sum_translate_smul_support_eq (a := a) (c := c) (d := d) (s := s)
      (c' := c') (f := f) hc']
  congr with i
  exact support_translate d (f i)

/-- Repeated affine transport of a translated/scaled finite family has a direct support formula
under the composed affine map, written directly in terms of the original summands. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_original {α : Type*}
    (a c b d e : ℝ) (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction)
    (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (affineTransport b d (∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_support]
  exact affineTransport_sum_translate_smul_support_eq_original (a := b * a) (c := b * c + d)
    (d := e) (s := s) (c' := c') (f := f) hc'

/-- Repeated affine transport of a translated/scaled finite family remains support-controlled after
an additional nonzero scalar multiple. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_original_smul {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (affineTransport b d (∑ i in s, c' i • translate e (t • f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_original (a := a) (c := c)
    (b := b) (d := d) (e := e) (s := s) (c' := c') (f := fun i => t • f i) hc']
  congr with i
  exact support_smul t ht (f i)

/-- Repeated affine transport of a translated/scaled finite family with an additional global
nonzero scalar multiple has the same exact support pullback as the original family. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_original_smul_global {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_smul, affineTransport_compose_sum_translate_smul_support_eq_original_smul
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']

/-- The repeated affine transport normal form is stable if the scalar is moved onto the
coefficients instead of the summands. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d (∑ i in s, (t * c' i) • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_original (a := a) (c := c)
    (b := b) (d := d) (e := e) (s := s) (c' := fun i => t * c' i) (f := f)]
  intro i hi
  exact mul_ne_zero ht (hc' i hi)

/-- The repeated affine transport normal form remains valid with an additional global scalar on
the entire translated family, provided the scalar is moved onto the coefficients. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_smul,
    affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']

/-- The support of the globally scaled repeated-transport normal form is controlled directly by
the original summands. -/
theorem affineTransport_compose_sum_translate_smul_support_subset_original_smul_coeffs_global
    {α : Type*} (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  exact support_sum_smul_subset (s := s) (c := c') (f := fun i => translate e (f i))

/-- The repeated transport normal form is stable if the global scalar is absorbed into the
coefficients, with the same exact support pullback. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global' {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (∑ i in s, (t * c' i) • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  exact affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The support of the coefficient-absorbed repeated-transport normal form is controlled directly
by the original summands. -/
theorem affineTransport_compose_sum_translate_smul_support_subset_original_smul_coeffs_global' {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (∑ i in s, (t * c' i) • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global'
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  exact support_sum_smul_subset (s := s) (c := fun i => t * c' i) (f := fun i => translate e (f i))

/-- The coefficient-absorbed repeated-transport normal form also has the corresponding translated
summand support formula. -/
theorem affineTransport_compose_sum_translate_smul_support_eq_translated_coeffs_global {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (∑ i in s, (t * c' i) • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global'
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  congr with i
  exact support_translate e (f i)

/-- The compact quoted form of the normalized repeated-transport support theorem. -/
theorem affineTransport_compose_sum_translate_smul_support_quote {α : Type*} (a c b d e : ℝ)
    (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction)
    (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  simpa using affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The compact quoted form of the normalized repeated-transport support inclusion. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_subset {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_quote (a := a) (c := c) (b := b)
    (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  exact support_sum_smul_subset (s := s) (c := fun i => t * c' i) (f := fun i => translate e (f i))

/-- The compact quoted form of the normalized repeated-transport support theorem in translated
summand form. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_translated {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  simpa using affineTransport_compose_sum_translate_smul_support_eq_translated_coeffs_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The compact quoted form of the globally scaled normalized repeated-transport support theorem in
translated summand form. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_translated_global {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  simpa using affineTransport_compose_sum_translate_smul_support_eq_translated_coeffs_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The compact quoted globally scaled translated form has support controlled directly by the
original summands. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_translated_global_subset_original
    {α : Type*} (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_quote_translated_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  exact support_sum_smul_subset (s := s) (c := fun i => t * c' i) (f := fun i => translate e (f i))

/-- The compact quoted globally scaled translated form also has the exact original-summand support
formula. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_translated_global_original
    {α : Type*} (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_quote_translated_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  congr with i
  exact support_translate e (f i)

/-- The compact quoted globally scaled translated family packages both the exact support formula
and the direct support inclusion in one owner-level theorem. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_translated_global_surfaces {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  constructor
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global_subset_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The compact quoted globally scaled original-summand family packages both the exact support
formula and the direct support inclusion in one owner-level theorem. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_original_global_surfaces {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  constructor
  · exact affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_subset_original_smul_coeffs_global
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The compact quoted globally scaled original-summand family also packages the exact support
formula and direct inclusion in the translated-summand form. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_original_global_translated_surfaces
    {α : Type*} (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  constructor
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global_subset_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The compact quoted globally scaled original-summand family exposes both exact support and
inclusion in the original-summand form as well. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_original_global_original_surfaces
    {α : Type*} (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  constructor
  · exact affineTransport_compose_sum_translate_smul_support_quote_original_global_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_original_global_subset_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The owner-level consolidated repeated-transport package bundles all four compact quoted
surfaces into one theorem. -/
theorem affineTransport_compose_sum_translate_smul_support_quote_bundle {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    ((Function.support
          (affineTransport a c
            (affineTransport b d
              (t • ∑ i in s, c' i • translate e (f i)))) =
        (fun x => (a * b) * x + (b * c + d)) ⁻¹'
          (s.biUnion fun i => Function.support (translate e (f i)))) ∧
      Function.support
          (affineTransport a c
            (affineTransport b d
              (t • ∑ i in s, c' i • translate e (f i)))) ⊆
        (fun x => (a * b) * x + (b * c + d)) ⁻¹'
          (s.biUnion fun i => Function.support (translate e (f i)))) ∧
     (Function.support
          (affineTransport a c
            (affineTransport b d
              (t • ∑ i in s, c' i • translate e (f i)))) =
        (fun x => (a * b) * x + (b * c + d)) ⁻¹'
          (s.biUnion fun i => Function.support (f i))) ∧
      Function.support
          (affineTransport a c
            (affineTransport b d
              (t • ∑ i in s, c' i • translate e (f i)))) ⊆
        (fun x => (a * b) * x + (b * c + d)) ⁻¹'
          (s.biUnion fun i => Function.support (f i)))) := by
  refine ⟨?_, ?_⟩
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global_surfaces
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_original_global_surfaces
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- Projection from the consolidated repeated-transport bundle to the translated exact-support
surface. -/
theorem affineTransport_compose_sum_translate_smul_support_bundle_translated_exact {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  exact (affineTransport_compose_sum_translate_smul_support_quote_bundle (a := a) (c := c)
    (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc').1.1

/-- Projection from the consolidated repeated-transport bundle to the original exact-support
surface. -/
theorem affineTransport_compose_sum_translate_smul_support_bundle_original_exact {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  exact (affineTransport_compose_sum_translate_smul_support_quote_bundle (a := a) (c := c)
    (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc').2.1

/-- Projection from the consolidated repeated-transport bundle to the translated inclusion
surface. -/
theorem affineTransport_compose_sum_translate_smul_support_bundle_translated_subset {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  exact (affineTransport_compose_sum_translate_smul_support_quote_bundle (a := a) (c := c)
    (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc').1.2

/-- Projection from the consolidated repeated-transport bundle to the original inclusion surface. -/
theorem affineTransport_compose_sum_translate_smul_support_bundle_original_subset {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  exact (affineTransport_compose_sum_translate_smul_support_quote_bundle (a := a) (c := c)
    (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc').2.2

/-- A single theorem exposing all four direct projections from the consolidated repeated-transport
bundle. -/
theorem affineTransport_compose_sum_translate_smul_support_bundle_surfaces {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) =
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) ∧
    Function.support
        (affineTransport a c
          (affineTransport b d
            (t • ∑ i in s, c' i • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_translated_global_subset_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_original_global_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'
  · exact affineTransport_compose_sum_translate_smul_support_quote_original_global_subset_original
      (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc'

/-- The coefficient-absorbed repeated-transport normal form also has the direct support inclusion
against the original summands. -/
theorem affineTransport_compose_sum_translate_smul_support_subset_original_smul_coeffs_global'' {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (∑ i in s, (t * c' i) • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (f i)) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_original_smul_coeffs_global'
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  exact support_sum_smul_subset (s := s) (c := fun i => t * c' i) (f := fun i => translate e (f i))

/-- The coefficient-absorbed repeated-transport normal form also has the corresponding translated
summand support inclusion. -/
theorem affineTransport_compose_sum_translate_smul_support_subset_translated_coeffs_global {α : Type*}
    (a c b d e : ℝ) (t : ℂ) (ht : t ≠ 0) (s : Finset α) (c' : α → ℂ)
    (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c
          (affineTransport b d
            (∑ i in s, (t * c' i) • translate e (f i)))) ⊆
      (fun x => (a * b) * x + (b * c + d)) ⁻¹'
        (s.biUnion fun i => Function.support (translate e (f i))) := by
  rw [affineTransport_compose_sum_translate_smul_support_eq_translated_coeffs_global
    (a := a) (c := c) (b := b) (d := d) (e := e) (t := t) (s := s) (c' := c') (f := f) ht hc']
  exact support_sum_smul_subset (s := s) (c := fun i => t * c' i) (f := fun i => translate e (f i))

/-- If all coefficients are nonzero, the transported translated finite linear combination has
support given directly by the affine pullback of the translated summands' supports. -/
theorem affineTransport_sum_translate_smul_support_eq_translated {α : Type*} (a c d : ℝ)
    (s : Finset α) (c' : α → ℂ) (f : α → ZetaAdmissibleFunction) (hc' : ∀ i ∈ s, c' i ≠ 0) :
    Function.support
        (affineTransport a c (∑ i in s, c' i • translate d (f i))) =
      (fun x => a * x + c) ⁻¹'
        (s.biUnion fun i => Function.support (translate d (f i))) := by
  exact affineTransport_sum_translate_smul_support_eq (a := a) (c := c) (d := d) (s := s)
    (c' := c') (f := f) hc'

/-- A centered smooth bump on the real line, packaged as an admissible function.

The function is the usual `ContDiffBump` profile on `ℝ`, viewed as a complex-valued
compactly supported smooth test function.
-/
def admissibleBump (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ZetaAdmissibleFunction where
  toZetaTestFunction :=
    { toFun := fun x => ((ContDiffBump (c := c) ⟨rIn, rOut, hrIn, hr⟩ x : ℝ) : ℂ)
      continuous_toFun := by
        exact (ContDiffBump.continuous (f := (ContDiffBump (c := c) ⟨rIn, rOut, hrIn, hr⟩))
          ).comp Complex.continuous_ofReal }
  smooth := by
    have hreal :
        ContDiff ℝ ⊤ (fun x : ℝ => (ContDiffBump (c := c) ⟨rIn, rOut, hrIn, hr⟩ x : ℝ)) :=
      ContDiffBump.contDiff (f := (ContDiffBump (c := c) ⟨rIn, rOut, hrIn, hr⟩))
    exact hreal.comp Complex.ofRealCLM.contDiff

/-- The admissible bump evaluates to `1` at its center. -/
theorem admissibleBump_apply_center (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    admissibleBump (c := c) rIn rOut hrIn hr c = (1 : ℂ) := by
  simp [admissibleBump, ContDiffBump.one_of_mem_closedBall, hrIn.le]

/-- The admissible bump has compact support. -/
theorem admissibleBump_hasCompactSupport (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    HasCompactSupport (admissibleBump (c := c) rIn rOut hrIn hr) := by
  exact (admissibleBump (c := c) rIn rOut hrIn hr).hasCompactSupport

/-- The admissible bump vanishes outside its outer radius. -/
theorem admissibleBump_zero_of_le_dist (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut)
    {x : ℝ} (hx : rOut ≤ dist x c) :
    admissibleBump (c := c) rIn rOut hrIn hr x = 0 := by
  dsimp [admissibleBump]
  have hb : ContDiffBump (c := c) ⟨rIn, rOut, hrIn, hr⟩ x = 0 := by
    exact ContDiffBump.zero_of_le_dist (f := ContDiffBump (c := c) ⟨rIn, rOut, hrIn, hr⟩) hx
  simp [hb]

/-- The admissible bump vanishes away from the closed `rOut`-ball around its center. -/
theorem admissibleBump_eq_zero_of_not_mem_closedBall (c rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) {x : ℝ} (hx : x ∉ Metric.closedBall c rOut) :
    admissibleBump (c := c) rIn rOut hrIn hr x = 0 := by
  have hdist : rOut < dist x c := by
    exact lt_of_not_ge (fun h => hx (by simpa [Metric.mem_closedBall] using h))
  exact admissibleBump_zero_of_le_dist (c := c) (rIn := rIn) (rOut := rOut) hrIn hr (by
    linarith [le_of_lt hdist])

/-- The admissible bump is smooth. -/
theorem admissibleBump_contDiff (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ContDiff ℝ ⊤ (admissibleBump (c := c) rIn rOut hrIn hr) := by
  exact (admissibleBump (c := c) rIn rOut hrIn hr).contDiff

/-- A one-point interpolation theorem for admissible functions.

Given a target complex value `a`, we can realize it as the value of an admissible
function at any prescribed real point.
-/
theorem exists_admissible_eval_eq (c : ℝ) (a : ℂ) :
    ∃ f : ZetaAdmissibleFunction, f c = a := by
  let b : ZetaAdmissibleFunction := admissibleBump (c := c) 1 2 zero_lt_one one_lt_two
  refine
    ⟨{ toZetaTestFunction := a • b.toZetaTestFunction
      smooth := b.smooth.const_smul a }, ?_⟩
  simp [b, admissibleBump_apply_center]

/-- Two prescribed values can be interpolated at two distinct real points. -/
theorem exists_admissible_eval_pair (c₁ c₂ : ℝ) (hc : c₁ ≠ c₂) (a₁ a₂ : ℂ) :
    ∃ f : ZetaAdmissibleFunction, f c₁ = a₁ ∧ f c₂ = a₂ := by
  have hdist : 0 < dist c₁ c₂ := dist_pos.2 hc
  let rOut : ℝ := dist c₁ c₂ / 2
  have hrOut_pos : 0 < rOut := by dsimp [rOut]; linarith
  have hrOut_lt : rOut < dist c₁ c₂ := by dsimp [rOut]; linarith
  let b₁ : ZetaAdmissibleFunction := admissibleBump (c := c₁) (rOut / 2) rOut (by
    dsimp [rOut]
    linarith) hrOut_lt
  let b₂ : ZetaAdmissibleFunction := admissibleBump (c := c₂) (rOut / 2) rOut (by
    dsimp [rOut]
    linarith) hrOut_lt
  have hb₁₁ : b₁ c₁ = (1 : ℂ) := by simp [b₁, admissibleBump_apply_center]
  have hb₁₂ : b₁ c₂ = 0 := by
    dsimp [b₁]
    apply admissibleBump_zero_of_le_dist
    · dsimp [rOut]
      linarith
    · dsimp [rOut]
      linarith [dist_nonneg c₁ c₂]
  have hb₂₂ : b₂ c₂ = (1 : ℂ) := by simp [b₂, admissibleBump_apply_center]
  have hb₂₁ : b₂ c₁ = 0 := by
    dsimp [b₂]
    apply admissibleBump_zero_of_le_dist
    · dsimp [rOut]
      linarith
    · dsimp [rOut]
      linarith [dist_nonneg c₁ c₂]
  refine
    ⟨smul a₁ b₁ + smul (a₂ - a₁ * b₁ c₂) b₂, ?_⟩
  constructor
  · simp [add_apply, smul_apply, hb₁₁, hb₂₁]
  · simp [add_apply, smul_apply, hb₁₂, hb₂₂]

/-- The support of the admissible bump is contained in the closed outer ball. -/
theorem admissibleBump_support_subset_closedBall (c rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) :
    Function.support (admissibleBump (c := c) rIn rOut hrIn hr) ⊆ Metric.closedBall c rOut := by
  intro x hx
  by_contra hx'
  exact hx (by
    simpa [Function.mem_support] using
      admissibleBump_eq_zero_of_not_mem_closedBall (c := c) (rIn := rIn) (rOut := rOut) hrIn hr hx')

/-- A finite set of real points can be separated from a new point by a positive radius. -/
theorem exists_radius_separating_finset {s : Finset ℝ} {x : ℝ} (hx : x ∉ s) :
    ∃ rOut : ℝ, 0 < rOut ∧ ∀ y ∈ s, rOut ≤ dist y x := by
  classical
  by_cases hs : s = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    simpa [hs] using hy
  · let t : Finset ℝ := s.image fun y => dist y x
    have ht : t.Nonempty := by
      rcases s.nonempty_iff_ne_empty.2 hs with ⟨y, hy⟩
      refine ⟨dist y x, ?_⟩
      exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    have hpos : 0 < t.min' ht := by
      have hm : t.min' ht ∈ t := Finset.min'_mem _ _
      rcases Finset.mem_image.1 hm with ⟨y, hy, hy'⟩
      have hyx : y ≠ x := by
        intro hxy
        apply hx
        simpa [hxy] using hy
      simpa [hy'] using dist_pos.2 hyx
    refine ⟨t.min' ht / 2, by linarith, ?_⟩
    intro y hy
    have hmem : dist y x ∈ t := by
      exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    have hle : t.min' ht ≤ dist y x := Finset.min'_le _ _ hmem
    linarith

/-- A finite collection of complex values can be interpolated at a finite set
of real points by an admissible function. -/
theorem exists_admissible_eval_finset {s : Finset ℝ} (a : ℝ → ℂ) :
    ∃ f : ZetaAdmissibleFunction, ∀ x ∈ s, f x = a x := by
  classical
  refine Finset.induction_on s ?base ?step
  · refine ⟨{ toZetaTestFunction := 0, smooth := by simpa using (contDiff_const : ContDiff ℝ ⊤ fun x : ℝ => (0 : ℂ)) }, ?_⟩
    intro x hx
    exact False.elim (by simpa using hx)
  · intro x s hx hs ih
    rcases ih with ⟨f0, hf0⟩
    have hsep : ∃ rOut : ℝ, 0 < rOut ∧ ∀ y ∈ s, rOut ≤ dist y x := by
      exact exists_radius_separating_finset (s := s) (x := x) (by simpa using hx)
    rcases hsep with ⟨rOut, hrOut_pos, hrSep⟩
    let b : ZetaAdmissibleFunction := admissibleBump (c := x) (rOut / 2) rOut (by linarith) (by
      have : rOut / 2 < rOut := by linarith
      exact this)
    have hb_x : b x = (1 : ℂ) := by
      simp [b, admissibleBump_apply_center]
    have hb_y : ∀ y ∈ s, b y = 0 := by
      intro y hy
      apply admissibleBump_zero_of_le_dist
      · linarith
      · exact hrSep y hy
    refine ⟨add f0 (smul (a x - f0 x) b), ?_⟩
    intro y hy'
    rcases Finset.mem_insert.1 hy' with rfl | hy
    · simp [add_apply, smul_apply, hf0, hb_x]
    · simp [add_apply, smul_apply, hf0 y hy, hb_y y hy]

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
