import Boundary.LFunctions.ZetaAdmissibleFunctionCore

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
  rw [Function.mem_support] at hx
  rw [smul_apply] at hx
  intro hfx
  rw [hfx, mul_zero] at hx
  exact hx rfl

/-- Nonzero scalar multiplication preserves support exactly. -/
theorem support_smul (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (a • f) = Function.support f := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_support] at hx
    rw [smul_apply] at hx
    intro hfx
    rw [hfx, mul_zero] at hx
    exact hx rfl
  · intro hx
    rw [Function.mem_support]
    exact mul_ne_zero ha hx

/-- A nonzero scale acts pointwise by precomposition. -/
theorem scale_apply_nonzero (t : ℝ) (ht : t ≠ 0) (f : ZetaAdmissibleFunction) (x : ℝ) :
    (scale t f).toZetaTestFunction x = f.toZetaTestFunction (t * x) := by
  have hscale := ZetaAdmissibleFunction.scale_apply t f x
  by_cases h0 : t = 0
  · exact (ht h0).elim
  · have hcase : (if h : t = 0 then (0 : ℂ) else f.toZetaTestFunction (t * x)) =
        f.toZetaTestFunction (t * x) := by
      by_cases h : t = 0
      · exact (h0 h).elim
      · exact dif_neg h
    rw [hscale]
    exact hcase

/-- The zero scale is identically zero. -/
theorem scale_apply_zero (f : ZetaAdmissibleFunction) (x : ℝ) :
    (scale 0 f).toZetaTestFunction x = 0 := by
  have hscale := ZetaAdmissibleFunction.scale_apply 0 f x
  have hcase : (if h : (0 : ℝ) = 0 then (0 : ℂ) else f.toZetaTestFunction (0 * x)) = 0 := by
    by_cases h : (0 : ℝ) = 0
    · exact dif_pos h
    · exact (h rfl).elim
  rw [hscale]
  exact hcase

/-- Translation shifts support by the translation parameter. -/
theorem support_translate (c : ℝ) (f : ZetaAdmissibleFunction) :
    Function.support (translate c f) = (fun x => x + c) ⁻¹' Function.support f := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_support] at hx
    rw [translate_apply] at hx
    exact hx
  · intro hx
    rw [Function.mem_support, translate_apply]
    exact hx

/-- Translation does not change support after nonzero scalar multiplication. -/
theorem support_translate_smul (c : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (a • f)) = Function.support (translate c f) := by
  rw [support_translate c (a • f), support_translate c f, support_smul a ha]

/-- The support of a translated nonzero scalar multiple is the translated support of the
original function. -/
theorem support_translate_smul_eq (c : ℝ) (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (translate c (a • f)) =
      (fun x => x + c) ⁻¹' Function.support f := by
  rw [support_translate_smul c a ha, support_translate c f]

/-- Reflection does not change support after nonzero scalar multiplication. -/
theorem support_reflect (f : ZetaAdmissibleFunction) :
    Function.support (reflect f) = (fun x => -x) ⁻¹' Function.support f := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_support] at hx
    rw [reflect_apply] at hx
    exact hx
  · intro hx
    rw [Function.mem_support, reflect_apply]
    exact hx

/-- Reflection does not change support after nonzero scalar multiplication. -/
theorem support_reflect_smul (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (reflect (a • f)) = Function.support (reflect f) := by
  rw [support_reflect (a • f), support_reflect f, support_smul a ha]

/-- The support of a reflected nonzero scalar multiple is the reflected support of the
original function. -/
theorem support_reflect_smul_eq (a : ℂ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (reflect (a • f)) = (fun x => -x) ⁻¹' Function.support f := by
  rw [support_reflect (a • f), support_smul a ha]

/-- Scaling does not change support after nonzero scalar multiplication. -/
theorem support_scale (t : ℝ) (ht : t ≠ 0) (f : ZetaAdmissibleFunction) :
    Function.support (scale t f) = (fun x => t * x) ⁻¹' Function.support f := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_support] at hx
    rw [scale_apply_nonzero t ht f x] at hx
    exact hx
  · intro hx
    rw [Function.mem_support]
    rw [scale_apply_nonzero t ht f x]
    exact hx

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
    Function.support (scale t (a • f)) = (fun x => t * x) ⁻¹' Function.support f := by
  rw [support_scale_smul t a ha, support_scale t ht f]

end ZetaAdmissibleFunction
