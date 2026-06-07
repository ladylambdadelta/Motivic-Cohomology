import Boundary.LFunctions.ZetaAdmissibleFunction

/-!
# Boundary autocorrelation core

This file owns the raw pointwise autocorrelation constructor for admissible
test functions. It stays below the transform and explicit-formula stack.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The pointwise autocorrelation attached to an admissible function. -/
def autocorrelation (f : ZetaAdmissibleFunction) : ZetaTestFunction where
  toFun := fun x => f x * star (f x)
  continuous := by
    have hf : Continuous fun x : ℝ => f x := f.toZetaTestFunction.continuous
    exact hf.mul (continuous_star.comp hf)

/-- The admissible autocorrelation agrees with the underlying test-function autocorrelation. -/
theorem autocorrelation_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    autocorrelation f x = f x * star (f x) := by
  rfl

/-- The admissible autocorrelation is the pointwise conjugate square. -/
theorem autocorrelation_eq (f : ZetaAdmissibleFunction) :
    autocorrelation f = (fun x => f x * star (f x)) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
