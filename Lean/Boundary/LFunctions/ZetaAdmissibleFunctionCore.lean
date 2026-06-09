import Boundary.LFunctions.ZetaTestFunction
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Boundary admissible test functions core

This file owns the admissible carrier and its primitive algebra/transport
operations. More substantial support calculus lives in dedicated companion
files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped CompactlySupported

/-- The admissible test-function carrier for the explicit-formula route.

It packages a compactly supported continuous function on the logarithmic line
together with the smoothness data required by the Paley--Wiener model.
-/
structure ZetaAdmissibleFunction where
  toZetaTestFunction : ℝ →C_c ℂ
  smooth : ContDiff ℝ ⊤ (fun x => toZetaTestFunction x)

namespace ZetaAdmissibleFunction

instance : CoeFun ZetaAdmissibleFunction (fun _ => ℝ → ℂ) :=
  ⟨fun f => f.toZetaTestFunction⟩

instance : Zero ZetaAdmissibleFunction :=
  ⟨CompactlySupportedContinuousMap.mk
      (ContinuousMap.mk (fun _ => (0 : ℂ)) continuous_const)
      (HasCompactSupport.zero),
    contDiff_const⟩

instance : Add ZetaAdmissibleFunction :=
  ⟨fun f g =>
    ⟨CompactlySupportedContinuousMap.mk
      (ContinuousMap.mk (fun x => f x + g x)
        (f.toZetaTestFunction.continuous.add g.toZetaTestFunction.continuous))
      (by
        exact f.toZetaTestFunction.hasCompactSupport.add
          g.toZetaTestFunction.hasCompactSupport),
      f.smooth.add g.smooth⟩⟩

@[ext]
theorem ext {f g : ZetaAdmissibleFunction} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk tf sf =>
    cases g with
    | mk tg sg =>
      have h' : tf = tg := by
        ext x
        exact h x
      cases h'
      rfl

instance : AddCommMonoid ZetaAdmissibleFunction where
  zero := 0
  add := (· + ·)
  add_assoc := by
    intro f g h
    ext x
    change (f x + g x) + h x = f x + (g x + h x)
    exact add_assoc (f x) (g x) (h x)
  zero_add := by
    intro f
    ext x
    change 0 + f x = f x
    exact zero_add (f x)
  add_zero := by
    intro f
    ext x
    change f x + 0 = f x
    exact add_zero (f x)
  add_comm := by
    intro f g
    ext x
    change f x + g x = g x + f x
    exact add_comm (f x) (g x)
  nsmul := fun n f => nsmulRec n f
  nsmul_zero := by
    intro f
    ext x
    rfl
  nsmul_succ := by
    intro n f
    ext x
    rfl

instance : SMul ℂ ZetaAdmissibleFunction :=
  ⟨fun a f =>
    ⟨CompactlySupportedContinuousMap.mk
      (ContinuousMap.mk (fun x => a * f x) (continuous_const.mul f.toZetaTestFunction.continuous))
      (by
        exact
          (HasCompactSupport.smul_left (f := fun _ : ℝ => a)
            (f' := f.toZetaTestFunction) f.toZetaTestFunction.hasCompactSupport)),
      f.smooth.const_smul a⟩⟩

/-- Forget the admissible structure and retain the underlying test function. -/
def toZetaTestFunction' (f : ZetaAdmissibleFunction) : ZetaTestFunction :=
  ⟨f.toZetaTestFunction, f.toZetaTestFunction.continuous⟩

theorem toZetaTestFunction'_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    f.toZetaTestFunction' x = f x := by
  rfl

theorem add_apply (f g : ZetaAdmissibleFunction) (x : ℝ) :
    (f + g) x = f x + g x := by
  rfl

theorem smul_apply (a : ℂ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    (a • f) x = a * f x := by
  rfl

theorem sum_apply {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ZetaAdmissibleFunction) (x : ℝ) :
    (∑ a in s, f a) x = ∑ a in s, f a x := by
  induction s using Finset.induction_on with
  | empty =>
      rfl
  | @insert a s ha ih =>
      calc
        (∑ a in insert a s, f a) x = (f a + ∑ b in s, f b) x := by
          rw [Finset.sum_insert ha]
        _ = f a x + (∑ b in s, f b) x := by rfl
        _ = f a x + ∑ b in s, f b x := by rw [ih]
        _ = ∑ a in insert a s, f a x := by
          rw [Finset.sum_insert ha]

/-- The coercion of a finite sum is the pointwise finite sum. -/
theorem coeFn_sum_apply {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    ⇑(∑ a in s, f a) = fun x => ∑ a in s, f a x := by
  ext x
  exact sum_apply (s := s) (f := f) x

theorem support_sum_apply {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    Function.support ⇑(∑ a in s, f a).toZetaTestFunction =
      Function.support (fun x => ∑ a in s, f a x) := by
  rw [coeFn_sum_apply (s := s) (f := f)]

/-- The support of a finite sum is the support of its pointwise sum expression. -/
theorem support_sum_toZetaTestFunction {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    Function.support ⇑(∑ a in s, f a).toZetaTestFunction =
      Function.support (fun x => ∑ a in s, f a x) := by
  exact support_sum_apply (s := s) (f := f)

/-- The underlying compactly supported continuous map. -/
theorem hasCompactSupport (f : ZetaAdmissibleFunction) :
    HasCompactSupport f := by
  exact f.toZetaTestFunction.hasCompactSupport

/-- The admissible carrier is smooth on the logarithmic line. -/
theorem contDiff (f : ZetaAdmissibleFunction) : ContDiff ℝ ⊤ f := by
  exact f.smooth

/-- Reflection across the origin. -/
def reflect (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      ⟨fun x => f (-x), f.toZetaTestFunction.continuous.comp continuous_neg⟩
      (by
        exact f.toZetaTestFunction.hasCompactSupport.comp_isClosedEmbedding
          (Homeomorph.neg ℝ).isClosedEmbedding)
  smooth := by
    change ContDiff ℝ ⊤ (fun x => f.toZetaTestFunction (-x))
    exact f.smooth.comp contDiff_neg

/-- Translation by a real parameter. -/
def translate (c : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      ⟨fun x => f (x + c), f.toZetaTestFunction.continuous.comp
        (continuous_id.add continuous_const)⟩
      (by
        exact f.toZetaTestFunction.hasCompactSupport.comp_isClosedEmbedding
          (Homeomorph.addRight c).isClosedEmbedding)
  smooth := by
    change ContDiff ℝ ⊤ (fun x => f.toZetaTestFunction (x + c))
    exact f.smooth.comp (contDiff_id.add contDiff_const)

/-- The zero scale is the zero function. -/
def scaleZero (_ : ZetaAdmissibleFunction) : ZetaAdmissibleFunction := 0

/-- The nonzero scale acts pointwise by precomposition. -/
def scaleNonzero (a : ℝ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      ⟨fun x => f (a * x), f.toZetaTestFunction.continuous.comp
        (continuous_const.mul continuous_id)⟩
      (by
        exact f.toZetaTestFunction.hasCompactSupport.comp_isClosedEmbedding
          (Homeomorph.mulLeft₀ a ha).isClosedEmbedding)
  smooth := by
    have hmul : ContDiff ℝ ⊤ (fun x : ℝ => a * x) := contDiff_const.mul contDiff_id
    exact f.smooth.comp hmul

/-- Scaling by a real parameter. -/
def scale (a : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  if ha : a = 0 then
    0
  else
    scaleNonzero a ha f

/-- The zero scale is the zero function. -/
theorem scale_zero (f : ZetaAdmissibleFunction) :
    scale 0 f = 0 := by
  unfold scale
  split_ifs with h
  · rfl
  · exfalso
    exact h rfl

/-- A nonzero scale acts pointwise by multiplication. -/
theorem scale_nonzero_apply (a : ℝ) (ha : a ≠ 0) (f : ZetaAdmissibleFunction) (x : ℝ) :
    scale a f x = f (a * x) := by
  unfold scale
  split_ifs with h
  · exfalso
    exact ha h
  · rfl

theorem reflect_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    reflect f x = f (-x) := rfl

theorem translate_apply (c : ℝ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    translate c f x = f (x + c) := rfl

theorem scale_apply (a : ℝ) (f : ZetaAdmissibleFunction) (x : ℝ) :
    scale a f x = if a = 0 then 0 else f (a * x) := by
  unfold scale
  split_ifs with ha
  · rfl
  · rfl

end ZetaAdmissibleFunction
