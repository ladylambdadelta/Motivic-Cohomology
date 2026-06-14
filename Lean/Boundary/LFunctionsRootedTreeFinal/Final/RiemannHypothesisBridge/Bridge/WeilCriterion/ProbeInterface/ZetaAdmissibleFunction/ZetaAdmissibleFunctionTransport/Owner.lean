import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunctionCore.Owner

/-!
# Boundary admissible test functions transport lemmas

This file owns the primitive compact-support transport lemmas for translate,
reflect, and scale, together with the support identities that downstream files
consume directly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The sum of two admissible functions has compact support. -/
theorem hasCompactSupport_add (f g : ZetaAdmissibleFunction) :
    HasCompactSupport (f + g) := by
  exact f.toZetaTestFunction.hasCompactSupport.add g.toZetaTestFunction.hasCompactSupport

/-- Scalar multiples of admissible functions have compact support. -/
theorem hasCompactSupport_smul (a : ℂ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport (a • f) := by
  exact f.toZetaTestFunction.hasCompactSupport.smul_left (f := fun _ : ℝ => a)
    (f' := f.toZetaTestFunction)

/-- A finite sum of admissible functions has compact support. -/
theorem hasCompactSupport_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    HasCompactSupport (∑ a in s, f a) := by
  induction s using Finset.induction_on with
  | empty =>
      exact HasCompactSupport.zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hleft : HasCompactSupport (f a).toZetaTestFunction := (f a).toZetaTestFunction.hasCompactSupport
      have hright : HasCompactSupport (∑ b in s, (f b).toZetaTestFunction) := by
        change HasCompactSupport (∑ b in s, (f b).toZetaTestFunction)
        exact ih
      exact hleft.add hright

/-- The support of a finite sum is contained in the union of the supports. -/
theorem support_sum_subset {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    Function.support (∑ a in s, f a) ⊆ ⋃ a ∈ s, Function.support (f a) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hsum : (∑ a in s, f a x) ≠ 0 := by
    rw [Finset.sum_apply] at hx
    exact hx
  have hne : ∃ a ∈ s, f a x ≠ 0 := by
    exact Finset.exists_ne_zero_of_sum_ne_zero (s := s) (f := fun a => f a x) hsum
  rcases hne with ⟨a, ha, hax⟩
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hax⟩⟩

/-- The support of a sum is contained in the union of the summands' supports. -/
theorem support_add_subset (f g : ZetaAdmissibleFunction) :
    Function.support (f + g) ⊆ Function.support f ∪ Function.support g := by
  intro x hx
  by_cases hfx : f x = 0
  · right
    by_cases hgx : g x = 0
    · exfalso
      rw [Function.mem_support] at hx
      rw [add_apply, hfx, hgx] at hx
      have hsum : (0 : ℂ) + 0 = 0 := by
        rw [zero_add]
      exact hx hsum
    · exact hgx
  · left
    exact hfx

/-- If two admissible functions have disjoint supports, the support of their sum is the union of
their supports. -/
theorem support_add_eq (f g : ZetaAdmissibleFunction)
    (hfg : Disjoint (Function.support f) (Function.support g)) :
    Function.support (f + g) = Function.support f ∪ Function.support g := by
  ext x
  constructor
  · intro hx
    exact support_add_subset f g hx
  · intro hx
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · rw [Function.mem_support] at hx
      have hgx : g x = 0 := by
        by_contra hgx
        have hgx' : x ∈ Function.support g := by
          exact hgx
        exact (Set.disjoint_left.mp hfg) hx hgx'
      rw [Function.mem_support]
      rw [add_apply, hgx]
      intro hsum
      rw [add_zero] at hsum
      exact hx hsum
    · rw [Function.mem_support] at hx
      have hfx : f x = 0 := by
        by_contra hfx
        have hfx' : x ∈ Function.support f := by
          exact hfx
        exact (Set.disjoint_left.mp hfg) hfx' hx
      rw [Function.mem_support]
      rw [add_apply, hfx]
      intro hsum
      rw [zero_add] at hsum
      exact hx hsum

/-- Scalar multiplication does not enlarge support. -/
theorem support_smul_subset (a : ℂ) (f : ZetaAdmissibleFunction) :
    Function.support (a • f) ⊆ Function.support f := by
  intro x hx
  intro hfx
  exact hx
    (Eq.trans
      (smul_apply a f x)
      (Eq.trans (congrArg (fun y : ℂ => a * y) hfx) (mul_zero a)))

/-- Nonzero scalar multiplication preserves support exactly. -/
theorem support_smul (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (a • f) = Function.support f := by
  ext x
  constructor
  · intro hx
    intro hfx
    exact hx
      (Eq.trans
        (smul_apply a f x)
        (Eq.trans (congrArg (fun y : ℂ => a * y) hfx) (mul_zero a)))
  · intro hx
    intro hzero
    exact (mul_ne_zero ha hx) (Eq.trans (smul_apply a f x).symm hzero)

/-- A nonzero scale acts pointwise by precomposition. -/
theorem scale_apply_nonzero (t : ℝ) (ht : t ≠ 0) (f : ZetaAdmissibleFunction) (x : ℝ) :
    (scale t f).toZetaTestFunction x = f.toZetaTestFunction (t * x) :=
  Eq.trans
    (ZetaAdmissibleFunction.scale_apply t f x)
    (dif_neg ht)

/-- The zero scale is identically zero. -/
theorem scale_apply_zero (f : ZetaAdmissibleFunction) (x : ℝ) :
    (scale 0 f).toZetaTestFunction x = 0 :=
  Eq.trans
    (ZetaAdmissibleFunction.scale_apply 0 f x)
    (dif_pos rfl)

/-- Translation shifts support by the translation parameter. -/
theorem support_translate (c : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (translate c f) = (fun x => x + c) ⁻¹' Function.support f := by
  ext x
  constructor
  · intro hx
    intro hzero
    exact hx (Eq.trans (translate_apply c f x) hzero)
  · intro hx
    intro hzero
    exact hx (Eq.trans (translate_apply c f x).symm hzero)

/-- Translation does not change support after nonzero scalar multiplication. -/
theorem support_translate_smul (c : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (a • f)) = Function.support (translate c f) :=
  Eq.trans
    (support_translate c (a • f))
    (Eq.trans
      (congrArg ((fun s => (fun x : ℝ => x + c) ⁻¹' s)) (support_smul a ha f))
      (support_translate c f).symm)

/-- The support of a translated nonzero scalar multiple is the translated support of the
original function. -/
theorem support_translate_smul_eq (c : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (a • f)) =
      (fun x => x + c) ⁻¹' Function.support f :=
  Eq.trans
    (support_translate_smul c a ha f)
    (support_translate c f)

/-- Reflection does not change support after nonzero scalar multiplication. -/
theorem support_reflect (f : ZetaAdmissibleFunction) :
    Function.support (reflect f) = (fun x => -x) ⁻¹' Function.support f := by
  ext x
  constructor
  · intro hx
    intro hzero
    exact hx (Eq.trans (reflect_apply f x) hzero)
  · intro hx
    intro hzero
    exact hx (Eq.trans (reflect_apply f x).symm hzero)

/-- Reflection does not change support after nonzero scalar multiplication. -/
theorem support_reflect_smul (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (reflect (a • f)) = Function.support (reflect f) :=
  Eq.trans
    (support_reflect (a • f))
    (Eq.trans
      (congrArg ((fun s => (fun x : ℝ => -x) ⁻¹' s)) (support_smul a ha f))
      (support_reflect f).symm)

/-- The support of a reflected nonzero scalar multiple is the reflected support of the
original function. -/
theorem support_reflect_smul_eq (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (reflect (a • f)) = (fun x => -x) ⁻¹' Function.support f :=
  Eq.trans
    (support_reflect_smul a ha f)
    (support_reflect f)

/-- Scaling does not change support after nonzero scalar multiplication. -/
theorem support_scale (t : ℝ) (ht : t ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (scale t f) = (fun x => t * x) ⁻¹' Function.support f := by
  ext x
  constructor
  · intro hx
    intro hzero
    exact hx (Eq.trans (scale_apply_nonzero t ht f x) hzero)
  · intro hx
    intro hzero
    exact hx (Eq.trans (scale_apply_nonzero t ht f x).symm hzero)

/-- Scaling does not change support after nonzero scalar multiplication. -/
theorem support_scale_smul (t : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (scale t (a • f)) = Function.support (scale t f) := by
  by_cases ht : t = 0
  · subst ht
    ext x
    constructor
    · intro hx
      rw [Function.mem_support] at hx
      have h0 : (scale 0 (a • f)).toZetaTestFunction x = 0 := by
        exact scale_apply_zero (a • f) x
      exfalso
      exact hx h0
    · intro hx
      rw [Function.mem_support] at hx
      have h0 : (scale 0 f).toZetaTestFunction x = 0 := by
        exact scale_apply_zero f x
      exfalso
      exact hx h0
  · rw [support_scale t ht (a • f), support_scale t ht f, support_smul a ha]

/-- The support of a scaled nonzero scalar multiple is the scaled support of the original
function. -/
theorem support_scale_smul_eq (t : ℝ) (ht : t ≠ 0) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (scale t (a • f)) = (fun x => t * x) ⁻¹' Function.support f :=
  Eq.trans
    (support_scale_smul t a ha f)
    (support_scale t ht f)

theorem translate_add_apply (c : ℝ) (f g : ZetaAdmissibleFunction) (x : ℝ) :
    translate c (f + g) x = (translate c f + translate c g) x :=
  Eq.trans
    (translate_apply c (f + g) x)
    (Eq.trans
      (add_apply f g (x + c))
      (Eq.trans
        (congrArg₂ HAdd.hAdd
          (translate_apply c f x).symm
          (translate_apply c g x).symm)
        (add_apply (translate c f) (translate c g) x).symm))

theorem scale_add_apply (a : ℝ) (ha : a ≠ 0)
    (f g : ZetaAdmissibleFunction) (x : ℝ) :
    scale a (f + g) x = (scale a f + scale a g) x :=
  Eq.trans
    (scale_apply_nonzero a ha (f + g) x)
    (Eq.trans
      (add_apply f g (a * x))
      (Eq.trans
        (congrArg₂ HAdd.hAdd
          (scale_apply_nonzero a ha f x).symm
          (scale_apply_nonzero a ha g x).symm)
        (add_apply (scale a f) (scale a g) x).symm))

theorem translate_smul_apply (c : ℝ) (a : ℂ)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    translate c (a • f) x = (a • translate c f) x :=
  Eq.trans
    (translate_apply c (a • f) x)
    (Eq.trans
      (smul_apply a f (x + c))
      (Eq.trans
        (congrArg (fun y : ℂ => a * y) (translate_apply c f x).symm)
        (smul_apply a (translate c f) x).symm))

theorem scale_smul_apply (t : ℝ) (ht : t ≠ 0) (a : ℂ)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    scale t (a • f) x = (a • scale t f) x :=
  Eq.trans
    (scale_apply_nonzero t ht (a • f) x)
    (Eq.trans
      (smul_apply a f (t * x))
      (Eq.trans
        (congrArg (fun y : ℂ => a * y) (scale_apply_nonzero t ht f x).symm)
        (smul_apply a (scale t f) x).symm))

theorem reflect_smul_apply (a : ℂ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    reflect (a • f) x = (a • reflect f) x :=
  Eq.trans
    (reflect_apply (a • f) x)
    (Eq.trans
      (smul_apply a f (-x))
      (Eq.trans
        (congrArg (fun y : ℂ => a * y) (reflect_apply f x).symm)
        (smul_apply a (reflect f) x).symm))

/-- Translation is additive in the function variable. -/
theorem translate_add (c : ℝ) (f g : ZetaAdmissibleFunction) :
    translate c (f + g) = translate c f + translate c g := by
  ext x
  exact translate_add_apply c f g x

/-- Nonzero scaling is additive in the function variable. -/
theorem scale_add (a : ℝ) (ha : a ≠ 0) (f g : ZetaAdmissibleFunction) :
    scale a (f + g) = scale a f + scale a g := by
  ext x
  exact scale_add_apply a ha f g x

/-- Translation commutes with complex scalar multiplication. -/
theorem translate_smul (c : ℝ) (a : ℂ) (f : ZetaAdmissibleFunction) :
    translate c (a • f) = a • translate c f := by
  ext x
  exact translate_smul_apply c a f x

/-- Nonzero scaling commutes with complex scalar multiplication. -/
theorem scale_smul (t : ℝ) (ht : t ≠ 0) (a : ℂ) (f : ZetaAdmissibleFunction) :
    scale t (a • f) = a • scale t f := by
  ext x
  exact scale_smul_apply t ht a f x

/-- Reflection commutes with complex scalar multiplication. -/
theorem reflect_smul (a : ℂ) (f : ZetaAdmissibleFunction) :
    reflect (a • f) = a • reflect f := by
  ext x
  exact reflect_smul_apply a f x

/-- Affine transport by `x ↦ a * x + c` on the real line. -/
def affineTransport (a c : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  translate c (scale a f)

/-- Nonzero affine transport is pointwise affine. -/
theorem affineTransport_apply_nonzero (a c : ℝ) (ha : a ≠ 0)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c f x = f (a * x + a * c) :=
  Eq.trans
    (translate_apply c (scale a f) x)
    (Eq.trans
      (scale_apply_nonzero a ha f (x + c))
      (congrArg f (mul_add a x c)))

theorem affine_offset_add_div_mul (a c d : ℝ) (ha : a ≠ 0) :
    a * (c + d / a) = a * c + d :=
  Eq.trans
    (mul_add a c (d / a))
    (congrArg (fun y : ℝ => a * c + y) (mul_div_cancel₀ d ha))

theorem affine_translate_argument_eq (a c d x : ℝ) (ha : a ≠ 0) :
    a * x + a * c + d = a * x + a * (c + d / a) :=
  Eq.trans
    (add_assoc (a * x) (a * c) d)
    (congrArg (fun y : ℝ => a * x + y) (affine_offset_add_div_mul a c d ha).symm)

theorem affine_scale_argument_eq (a c t x : ℝ) :
    t * (a * x + a * c) = (t * a) * x + (t * a) * c :=
  Eq.trans
    (mul_add t (a * x) (a * c))
    (congrArg₂ HAdd.hAdd (mul_assoc t a x).symm (mul_assoc t a c).symm)

theorem affine_reflect_argument_eq (a c x : ℝ) :
    -(a * x + a * c) = (-a) * x + (-a) * c :=
  Eq.trans
    (neg_add (a * x) (a * c))
    (congrArg₂ HAdd.hAdd (neg_mul_eq_neg_mul a x) (neg_mul_eq_neg_mul a c))

theorem affine_compose_div_term_eq (a b d : ℝ) (ha : a ≠ 0) :
    (b * a) * (d / a) = b * d :=
  Eq.trans
    (mul_assoc b a (d / a))
    (congrArg (fun y : ℝ => b * y) (mul_div_cancel₀ d ha))

theorem affine_compose_offset_eq (a c b d : ℝ) (ha : a ≠ 0) :
    (b * a) * (c + d / a) = (b * a) * c + b * d :=
  Eq.trans
    (mul_add (b * a) c (d / a))
    (congrArg (fun y : ℝ => (b * a) * c + y) (affine_compose_div_term_eq a b d ha))

theorem affine_compose_argument_left (a c b d x : ℝ) :
    b * (a * x + a * c) + b * d = (b * a) * x + (b * a) * c + b * d :=
  congrArg (fun y : ℝ => y + b * d) (affine_scale_argument_eq a c b x)

theorem affine_compose_argument_eq (a c b d x : ℝ) (ha : a ≠ 0) :
    b * (a * x + a * c) + b * d =
      (b * a) * x + (b * a) * (c + d / a) :=
  Eq.trans
    (affine_compose_argument_left a c b d x)
    (Eq.trans
      (add_assoc ((b * a) * x) ((b * a) * c) (b * d))
      (congrArg (fun y : ℝ => (b * a) * x + y)
        (affine_compose_offset_eq a c b d ha).symm))

theorem affineTransport_add_apply (a c : ℝ) (ha : a ≠ 0)
    (f g : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c (f + g) x = (affineTransport a c f + affineTransport a c g) x :=
  Eq.trans
    (affineTransport_apply_nonzero a c ha (f + g) x)
    (Eq.trans
      (add_apply f g (a * x + a * c))
      (Eq.trans
        (congrArg₂ HAdd.hAdd
          (affineTransport_apply_nonzero a c ha f x).symm
          (affineTransport_apply_nonzero a c ha g x).symm)
        (add_apply (affineTransport a c f) (affineTransport a c g) x).symm))

theorem affineTransport_smul_apply (a c : ℝ) (ha : a ≠ 0)
    (b : ℂ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c (b • f) x = (b • affineTransport a c f) x :=
  Eq.trans
    (affineTransport_apply_nonzero a c ha (b • f) x)
    (Eq.trans
      (smul_apply b f (a * x + a * c))
      (Eq.trans
        (congrArg (fun y : ℂ => b * y)
          (affineTransport_apply_nonzero a c ha f x).symm)
        (smul_apply b (affineTransport a c f) x).symm))

theorem affineTransport_translate_apply (a c d : ℝ) (ha : a ≠ 0)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c (translate d f) x = affineTransport a (c + d / a) f x :=
  Eq.trans
    (affineTransport_apply_nonzero a c ha (translate d f) x)
    (Eq.trans
      (translate_apply d f (a * x + a * c))
      (Eq.trans
        (congrArg f (affine_translate_argument_eq a c d x ha))
        (affineTransport_apply_nonzero a (c + d / a) ha f x).symm))

theorem affineTransport_scale_apply (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c (scale b f) x = affineTransport (b * a) c f x :=
  Eq.trans
    (affineTransport_apply_nonzero a c ha (scale b f) x)
    (Eq.trans
      (scale_apply_nonzero b hb f (a * x + a * c))
      (Eq.trans
        (congrArg f (affine_scale_argument_eq a c b x))
        (affineTransport_apply_nonzero (b * a) c (mul_ne_zero hb ha) f x).symm))

theorem affineTransport_reflect_apply (a c : ℝ) (ha : a ≠ 0)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c (reflect f) x = affineTransport (-a) c f x :=
  Eq.trans
    (affineTransport_apply_nonzero a c ha (reflect f) x)
    (Eq.trans
      (reflect_apply f (a * x + a * c))
      (Eq.trans
        (congrArg f (affine_reflect_argument_eq a c x))
        (affineTransport_apply_nonzero (-a) c (neg_ne_zero.mpr ha) f x).symm))

theorem affineTransport_compose_apply (a c b d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    affineTransport a c (affineTransport b d f) x =
      affineTransport (b * a) (c + d / a) f x :=
  Eq.trans
    (affineTransport_apply_nonzero a c ha (affineTransport b d f) x)
    (Eq.trans
      (affineTransport_apply_nonzero b d hb f (a * x + a * c))
      (Eq.trans
        (congrArg f (affine_compose_argument_eq a c b d x ha))
        (affineTransport_apply_nonzero (b * a) (c + d / a) (mul_ne_zero hb ha) f x).symm))

/-- Affine transport is additive in the function variable for nonzero scale. -/
theorem affineTransport_add (a c : ℝ) (ha : a ≠ 0) (f g : ZetaAdmissibleFunction) :
    affineTransport a c (f + g) = affineTransport a c f + affineTransport a c g := by
  ext x
  exact affineTransport_add_apply a c ha f g x

/-- Affine transport commutes with complex scalar multiplication for nonzero scale. -/
theorem affineTransport_smul (a c : ℝ) (ha : a ≠ 0) (b : ℂ) (f : ZetaAdmissibleFunction) :
    affineTransport a c (b • f) = b • affineTransport a c f := by
  ext x
  exact affineTransport_smul_apply a c ha b f x

/-- Nonzero scalar multiplication does not change the support of an affine transport. -/
theorem support_affineTransport_smul (a c : ℝ) (ha : a ≠ 0) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (b • f)) = Function.support (affineTransport a c f) :=
  Eq.trans
    (congrArg (fun g : ZetaAdmissibleFunction => Function.support g)
      (affineTransport_smul a c ha b f))
    (support_smul b hb (affineTransport a c f))

theorem affine_preimage_compose_eq (a c : ℝ) (s : Set ℝ) :
    (fun x : ℝ => x + c) ⁻¹' ((fun x : ℝ => a * x) ⁻¹' s) =
      (fun x : ℝ => a * x + a * c) ⁻¹' s := by
  ext x
  constructor
  · intro hx
    exact Eq.mp (congrArg (fun y : ℝ => y ∈ s) (mul_add a x c)) hx
  · intro hx
    exact Eq.mp (congrArg (fun y : ℝ => y ∈ s) (mul_add a x c).symm) hx

/-- The support of a nonzero affine transport is the affine pullback of the original support. -/
theorem affineTransport_support (a c : ℝ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c f) =
      (fun x => a * x + a * c) ⁻¹' Function.support f :=
  Eq.trans
    (support_translate c (scale a f))
    (Eq.trans
      (congrArg ((fun s => (fun x : ℝ => x + c) ⁻¹' s)) (support_scale a ha f))
      (affine_preimage_compose_eq a c (Function.support f)))

/-- The support of an affinely transported nonzero scalar multiple is the affine pullback of the
original support. -/
theorem support_affineTransport_smul_eq (a c : ℝ) (ha : a ≠ 0) (b : ℂ) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (b • f)) =
      (fun x => a * x + a * c) ⁻¹' Function.support f :=
  Eq.trans
    (support_affineTransport_smul a c ha b hb f)
    (affineTransport_support a c ha f)

/-- Affine transport preserves compact support. -/
theorem hasCompactSupport_affineTransport (a c : ℝ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport (affineTransport a c f) := by
  exact (affineTransport a c f).hasCompactSupport

/-- Transport after a translation is transport with shifted offset for nonzero scale. -/
theorem affineTransport_translate (a c d : ℝ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    affineTransport a c (translate d f) = affineTransport a (c + d / a) f := by
  ext x
  exact affineTransport_translate_apply a c d ha f x

/-- Transport after scaling composes the affine parameters, for nonzero scales. -/
theorem affineTransport_scale (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (scale b f) = affineTransport (b * a) c f := by
  ext x
  exact affineTransport_scale_apply a b c ha hb f x

/-- Transport after reflection is transport by the reflected affine map. -/
theorem affineTransport_reflect (a c : ℝ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    affineTransport a c (reflect f) = affineTransport (-a) c f := by
  ext x
  exact affineTransport_reflect_apply a c ha f x

/-- Composing two affine transports is again an affine transport. -/
theorem affineTransport_compose (a c b d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (affineTransport b d f) =
      affineTransport (b * a) (c + d / a) f := by
  ext x
  exact affineTransport_compose_apply a c b d ha hb f x

/-- The support of a composed nonzero affine transport is the pullback of the support of the
original probe under the composed affine map. -/
theorem affineTransport_compose_support (a c b d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (affineTransport b d f)) =
      (fun x => (b * a) * x + (b * a) * (c + d / a)) ⁻¹' Function.support f :=
  Eq.trans
    (congrArg (fun g : ZetaAdmissibleFunction => Function.support g)
      (affineTransport_compose a c b d ha hb f))
    (affineTransport_support (b * a) (c + d / a) (mul_ne_zero hb ha) f)

/-- A composed affine transport of a nonzero scalar multiple has the same exact support pullback
as the underlying probe. -/
theorem affineTransport_compose_smul_support (a c b d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (t : ℂ) (ht : t ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (affineTransport a c (affineTransport b d (t • f))) =
      (fun x => (b * a) * x + (b * a) * (c + d / a)) ⁻¹' Function.support f :=
  Eq.trans
    (affineTransport_compose_support a c b d ha hb (t • f))
    (congrArg ((fun s => (fun x => (b * a) * x + (b * a) * (c + d / a)) ⁻¹' s))
      (support_smul t ht f))

/-- Affine transport commutes with the basic translation move after nonzero scalar multiplication. -/
theorem affineTransport_translate_smul (a c d : ℝ) (ha : a ≠ 0) (b : ℂ) (_hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (translate d (b • f)) =
      b • affineTransport a (c + d / a) f :=
  Eq.trans
    (affineTransport_translate a c d ha (b • f))
    (affineTransport_smul a (c + d / a) ha b f)

/-- Affine transport commutes with scaling after nonzero scalar multiplication. -/
theorem affineTransport_scale_smul (a c t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0)
    (b : ℂ) (_hb : b ≠ 0) (f : ZetaAdmissibleFunction) :
    affineTransport a c (scale t (b • f)) =
      b • affineTransport (t * a) c f :=
  Eq.trans
    (affineTransport_scale a t c ha ht (b • f))
    (affineTransport_smul (t * a) c (mul_ne_zero ht ha) b f)

/-- Affine transport commutes with reflection after nonzero scalar multiplication. -/
theorem affineTransport_reflect_smul (a c : ℝ) (ha : a ≠ 0) (b : ℂ) (_hb : b ≠ 0)
    (f : ZetaAdmissibleFunction) :
    affineTransport a c (reflect (b • f)) =
      b • affineTransport (-a) c f :=
  Eq.trans
    (affineTransport_reflect a c ha (b • f))
    (affineTransport_smul (-a) c (neg_ne_zero.mpr ha) b f)

end ZetaAdmissibleFunction
