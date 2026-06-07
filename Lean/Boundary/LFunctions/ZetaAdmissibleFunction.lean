import Boundary.LFunctions.ZetaTestFunction
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Boundary admissible test functions

This file introduces the owner-level admissible carrier for the explicit-formula
route. The committed model is the Paley--Wiener style compactly supported smooth
class on the logarithmic line, bundled on top of the existing `ZetaTestFunction`
continuity layer.

The analytic transform and zero-separation theorems will consume this carrier.
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

/-- Forget the admissible structure and retain the underlying test function. -/
def toZetaTestFunction' (f : ZetaAdmissibleFunction) : ZetaTestFunction :=
  ⟨f.toZetaTestFunction, f.toZetaTestFunction.continuous⟩

theorem toZetaTestFunction'_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    f.toZetaTestFunction' x = f x := by
  rfl

/-- The underlying compactly supported continuous map. -/
theorem hasCompactSupport (f : ZetaAdmissibleFunction) :
    HasCompactSupport f := by
  exact f.toZetaTestFunction.hasCompactSupport

/-- The admissible carrier is smooth on the logarithmic line. -/
theorem contDiff (f : ZetaAdmissibleFunction) : ContDiff ℝ ⊤ f := by
  exact f.smooth

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
