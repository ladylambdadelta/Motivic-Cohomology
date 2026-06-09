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

/-- The autocorrelation of the daggered probe is the reflection of the original autocorrelation. -/
theorem autocorrelation_dagger_eq_reflect (f : ZetaAdmissibleFunction) :
    autocorrelation (ZetaAdmissibleFunction.reflect f) =
      ZetaTestFunction.reflect (autocorrelation f) := by
  ext t
  rfl

/-- The autocorrelation kernel is even under reflection of the underlying probe. -/
theorem autocorrelation_reflect_eq (f : ZetaAdmissibleFunction) :
    autocorrelation (ZetaAdmissibleFunction.reflect f) =
      fun t => autocorrelation f (-t) := by
  rw [autocorrelation_dagger_eq_reflect]
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
