import Boundary.LFunctions.ZetaAdmissibleAutocorrelation

/-!
# Boundary admissible probe

This file names the concrete admissible probe built from the autocorrelation
of an admissible test function.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The admissible separating probe attached to an admissible function. -/
def separatingProbe (f : ZetaAdmissibleFunction) : ZetaTestFunction :=
  autocorrelation f

/-- The separating probe is pointwise the autocorrelation. -/
theorem separatingProbe_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The separating probe is the admissible autocorrelation. -/
theorem separatingProbe_eq (f : ZetaAdmissibleFunction) :
    separatingProbe f = autocorrelation f := by
  rfl

/-- The admissible probe is the pointwise conjugate square. -/
theorem separatingProbe_conjSq (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The admissible probe is the pointwise conjugate square. -/
theorem separatingProbe_pointwise (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The admissible probe is pointwise the conjugate square. -/
theorem separatingProbe_square (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The admissible probe is the autocorrelation square. -/
theorem admissible_probe_square (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
