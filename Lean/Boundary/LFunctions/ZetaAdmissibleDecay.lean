import Boundary.LFunctions.ZetaAdmissibleSpectralModel

/-!
# Boundary admissible decay data

This file exports the compact support and smoothness data carried by the
admissible test-function structure. It is the honest decay-side input currently
available for the Paley--Wiener model.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- The admissible function has compact support. -/
theorem admissible_hasCompactSupport (f : ZetaAdmissibleFunction) :
    HasCompactSupport f := by
  exact hasCompactSupport f

/-- The admissible function is smooth on the logarithmic line. -/
theorem admissible_contDiff (f : ZetaAdmissibleFunction) : ContDiff ℝ ∞ f := by
  exact contDiff f

/-- The admissible function retains the underlying test-function carrier. -/
theorem admissible_toTestFunction (f : ZetaAdmissibleFunction) :
    f.toZetaTestFunction' = ZetaAdmissibleFunction.toZetaTestFunction' f := by
  rfl

/-- The admissible carrier keeps the underlying test function. -/
theorem admissible_carrier (f : ZetaAdmissibleFunction) :
    f.toZetaTestFunction' = ZetaAdmissibleFunction.toZetaTestFunction' f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
