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
    autocorrelation
        { toZetaTestFunction :=
            ⟨fun t => star (f (-t)),
              by continuity,
              by
                simpa using
                  f.toZetaTestFunction.hasCompactSupport.comp_isClosedEmbedding
                    (Homeomorph.neg ℝ).isClosedEmbedding⟩
          smooth := by
            simpa using f.smooth.comp contDiff_neg } =
      ZetaTestFunction.reflect (autocorrelation f) := by
  ext t
  unfold autocorrelation
  rw [ZetaTestFunction.reflect_apply]
  rw [star_star]
  rw [mul_comm]

/-- The autocorrelation kernel is even under reflection of the underlying probe. -/
theorem autocorrelation_reflect_eq (f : ZetaAdmissibleFunction) :
    autocorrelation
        { toZetaTestFunction :=
            ⟨fun t => star (f (-t)),
              by continuity,
              by
                simpa using
                  f.toZetaTestFunction.hasCompactSupport.comp_isClosedEmbedding
                    (Homeomorph.neg ℝ).isClosedEmbedding⟩
          smooth := by
            simpa using f.smooth.comp contDiff_neg } =
      fun t => autocorrelation f (-t) := by
  rw [autocorrelation_dagger_eq_reflect]
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
