import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic

/-!
# Boundary zeta test functions

This file fixes a concrete test-function carrier for the explicit-formula route.
The carrier is intentionally lightweight: continuous complex-valued functions on `ℝ`,
with the basic reflection, translation, and scaling operations proved directly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The basic test-function carrier on the additive line. -/
structure ZetaTestFunction where
  toFun : ℝ → ℂ
  continuous : Continuous toFun
  hasCompactSupport : HasCompactSupport toFun

namespace ZetaTestFunction

instance : CoeFun ZetaTestFunction (fun _ => ℝ → ℂ) :=
  ⟨ZetaTestFunction.toFun⟩

instance : Zero ZetaTestFunction :=
  ⟨⟨0, continuous_const, HasCompactSupport.zero⟩⟩

instance : Add ZetaTestFunction :=
  ⟨fun f g =>
    ⟨fun x => f x + g x,
      f.continuous.add g.continuous,
      f.hasCompactSupport.add g.hasCompactSupport⟩⟩

instance : SMul ℂ ZetaTestFunction :=
  ⟨fun a f =>
    ⟨fun x => a * f x,
      continuous_const.mul f.continuous,
      (show HasCompactSupport (fun x : ℝ => (fun _ : ℝ => a) x * f x) from
        HasCompactSupport.mul_left f.hasCompactSupport)⟩⟩

theorem ext' {f g : ZetaTestFunction} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk ff fc =>
    cases g with
    | mk gf gc =>
      have hfun : ff = gf := by
        funext x
        exact h x
      cases hfun
      rfl

instance : AddCommMonoid ZetaTestFunction where
  zero := 0
  add := (· + ·)
  add_assoc := by
    intro f g h
    apply ext'
    intro x
    exact add_assoc (f x) (g x) (h x)
  zero_add := by
    intro f
    apply ext'
    intro x
    exact zero_add (f x)
  add_zero := by
    intro f
    apply ext'
    intro x
    exact add_zero (f x)
  add_comm := by
    intro f g
    apply ext'
    intro x
    exact add_comm (f x) (g x)
  nsmul := fun n f =>
    ⟨fun x => n • f x,
      f.continuous.nsmul n,
      (show HasCompactSupport (fun x : ℝ => (fun _ : ℝ => n) x • f x) from
        HasCompactSupport.smul_left f.hasCompactSupport)⟩
  nsmul_zero := by
    intro f
    apply ext'
    intro x
    exact zero_nsmul (f x)
  nsmul_succ := by
    intro n f
    apply ext'
    intro x
    exact succ_nsmul (f x) n

@[ext]
theorem ext {f g : ZetaTestFunction} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  funext x
  exact h x

/-- Reflection across the origin. -/
def reflect (f : ZetaTestFunction) : ZetaTestFunction where
  toFun := fun x => f (-x)
  continuous := f.continuous.comp continuous_neg
  hasCompactSupport := by
    exact f.hasCompactSupport.comp_isClosedEmbedding
      (Homeomorph.neg ℝ).isClosedEmbedding

/-- Translation by a real parameter. -/
def translate (c : ℝ) (f : ZetaTestFunction) : ZetaTestFunction where
  toFun := fun x => f (x + c)
  continuous := f.continuous.comp (continuous_id.add continuous_const)
  hasCompactSupport := by
    exact f.hasCompactSupport.comp_isClosedEmbedding
      (Homeomorph.addRight c).isClosedEmbedding

/-- Nonzero scaling by a real parameter. -/
def scaleNonzero (a : ℝ) (ha : a ≠ 0) (f : ZetaTestFunction) : ZetaTestFunction where
  toFun := fun x => f (a * x)
  continuous := f.continuous.comp (continuous_const.mul continuous_id)
  hasCompactSupport := by
    exact
      (show HasCompactSupport
          (f.toFun ∘ (Homeomorph.mulLeft₀ a ha : ℝ ≃ₜ ℝ)) from
        f.hasCompactSupport.comp_isClosedEmbedding
          (Homeomorph.mulLeft₀ a ha).isClosedEmbedding)

/-- Scaling by a real parameter.  The zero scale is the zero test function, since
precomposition by the zero map does not preserve compact support in general. -/
def scale (a : ℝ) (f : ZetaTestFunction) : ZetaTestFunction :=
  if ha : a = 0 then
    0
  else
    scaleNonzero a ha f

theorem reflect_apply (f : ZetaTestFunction) (x : ℝ) :
    reflect f x = f (-x) := rfl

theorem translate_apply (c : ℝ) (f : ZetaTestFunction) (x : ℝ) :
    translate c f x = f (x + c) := rfl

/-- The zero scale is the zero test function. -/
theorem scale_zero (f : ZetaTestFunction) :
    scale 0 f = 0 := by
  unfold scale
  exact dif_pos rfl

/-- A nonzero scale acts pointwise by precomposition. -/
theorem scale_apply_nonzero (a : ℝ) (ha : a ≠ 0) (f : ZetaTestFunction) (x : ℝ) :
    scale a f x = f (a * x) := by
  unfold scale
  exact congrArg (fun g : ZetaTestFunction => g x) (dif_neg ha)

/-- The zero scale vanishes pointwise. -/
theorem scale_apply_zero (f : ZetaTestFunction) (x : ℝ) :
    scale 0 f x = 0 := by
  exact congrArg (fun g : ZetaTestFunction => g x) (scale_zero f)

theorem reflect_reflect (f : ZetaTestFunction) : reflect (reflect f) = f := by
  ext x
  calc
    reflect (reflect f) x = f (-(-x)) := by rfl
    _ = f x := by
      exact congrArg f (neg_neg x)

theorem translate_zero (f : ZetaTestFunction) : translate 0 f = f := by
  ext x
  calc
    translate 0 f x = f (x + 0) := by rfl
    _ = f x := by
      exact congrArg f (add_zero x)

theorem translate_add (c d : ℝ) (f : ZetaTestFunction) :
    translate c (translate d f) = translate (c + d) f := by
  ext x
  calc
    translate c (translate d f) x = f ((x + c) + d) := by rfl
    _ = f (x + (c + d)) := by
      exact congrArg f (add_assoc x c d)

theorem scale_one (f : ZetaTestFunction) : scale 1 f = f := by
  ext x
  calc
    scale 1 f x = f (1 * x) := by
      exact scale_apply_nonzero 1 one_ne_zero f x
    _ = f x := by
      exact congrArg f (one_mul x)

theorem scale_mul (a b : ℝ) (f : ZetaTestFunction) :
    scale a (scale b f) = scale (a * b) f := by
  by_cases ha : a = 0
  · ext x
    have hab_zero : a * b = 0 := by
      exact Eq.trans
        (congrArg (fun r : ℝ => r * b) ha)
        (zero_mul b)
    calc
      scale a (scale b f) x = scale 0 (scale b f) x := by
        exact congrArg (fun r : ℝ => scale r (scale b f) x) ha
      _ = 0 := by
        exact scale_apply_zero (scale b f) x
      _ = scale 0 f x := by
        exact (scale_apply_zero f x).symm
      _ = scale (a * b) f x := by
        exact congrArg (fun r : ℝ => scale r f x) hab_zero.symm
  · by_cases hb : b = 0
    · ext x
      have hab_zero : a * b = 0 := by
        exact Eq.trans
          (congrArg (fun r : ℝ => a * r) hb)
          (mul_zero a)
      calc
        scale a (scale b f) x = scale a (scale 0 f) x := by
          exact congrArg (fun g : ZetaTestFunction => scale a g x)
            (congrArg (fun r : ℝ => scale r f) hb)
        _ = scale a 0 x := by
          exact congrArg (fun g : ZetaTestFunction => scale a g x)
            (scale_zero f)
        _ = (0 : ZetaTestFunction) (a * x) := by
          exact scale_apply_nonzero a ha 0 x
        _ = 0 := by
          rfl
        _ = scale 0 f x := by
          exact (scale_apply_zero f x).symm
        _ = scale (a * b) f x := by
          exact congrArg (fun r : ℝ => scale r f x) hab_zero.symm
    · ext x
      calc
        scale a (scale b f) x = scale b f (a * x) := by
          exact scale_apply_nonzero a ha (scale b f) x
        _ = f (b * (a * x)) := by
          exact scale_apply_nonzero b hb f (a * x)
        _ = f ((a * b) * x) := by
          exact congrArg f
            (calc
              b * (a * x) = (b * a) * x := by
                exact (mul_assoc b a x).symm
              _ = (a * b) * x := by
                exact congrArg (fun t : ℝ => t * x) (mul_comm b a))
        _ = scale (a * b) f x := by
          exact (scale_apply_nonzero (a * b)
            (mul_ne_zero ha hb) f x).symm

end ZetaTestFunction
