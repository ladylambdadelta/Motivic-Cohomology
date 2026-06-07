import Mathlib.Topology.Algebra.Group.Basic
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

namespace ZetaTestFunction

instance : CoeFun ZetaTestFunction (fun _ => ℝ → ℂ) :=
  ⟨ZetaTestFunction.toFun⟩

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

/-- Translation by a real parameter. -/
def translate (c : ℝ) (f : ZetaTestFunction) : ZetaTestFunction where
  toFun := fun x => f (x + c)
  continuous := f.continuous.comp (continuous_id.add continuous_const)

/-- Scaling by a real parameter. -/
def scale (a : ℝ) (f : ZetaTestFunction) : ZetaTestFunction where
  toFun := fun x => f (a * x)
  continuous := f.continuous.comp (continuous_const.mul continuous_id)

theorem reflect_apply (f : ZetaTestFunction) (x : ℝ) :
    reflect f x = f (-x) := rfl

theorem translate_apply (c : ℝ) (f : ZetaTestFunction) (x : ℝ) :
    translate c f x = f (x + c) := rfl

theorem scale_apply (a : ℝ) (f : ZetaTestFunction) (x : ℝ) :
    scale a f x = f (a * x) := rfl

theorem reflect_reflect (f : ZetaTestFunction) : reflect (reflect f) = f := by
  ext x
  change f (-(-x)) = f x
  have hx : -(-x) = x := neg_neg x
  rw [hx]

theorem translate_zero (f : ZetaTestFunction) : translate 0 f = f := by
  ext x
  change f (x + 0) = f x
  rw [add_zero]

theorem translate_add (c d : ℝ) (f : ZetaTestFunction) :
    translate c (translate d f) = translate (c + d) f := by
  ext x
  change f ((x + c) + d) = f (x + (c + d))
  have h : (x + c) + d = x + (c + d) := add_assoc x c d
  rw [h]

theorem scale_one (f : ZetaTestFunction) : scale 1 f = f := by
  ext x
  change f (1 * x) = f x
  rw [one_mul]

theorem scale_mul (a b : ℝ) (f : ZetaTestFunction) :
    scale a (scale b f) = scale (a * b) f := by
  ext x
  change f (b * (a * x)) = f ((a * b) * x)
  have h : b * (a * x) = (a * b) * x := by
    rw [← mul_assoc, mul_comm b a, mul_assoc]
  rw [h]

end ZetaTestFunction
