import Boundary.LFunctions.ZetaAdmissibleTransform

/-!
# Boundary admissible spectral model

This file names the spectral model attached to the admissible carrier and
records that it is built from the explicit-formula transform already attached
to the underlying test function.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The admissible spectral model attached to an admissible function. -/
def spectralModel (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.explicitFormulaDefectPackage :=
  toZetaExplicitFormulaTransform f

/-- The admissible spectral model is exactly the admissible explicit-formula transform. -/
theorem spectralModel_eq (f : ZetaAdmissibleFunction) :
    spectralModel f = toZetaExplicitFormulaTransform f := by
  rfl

/-- The admissible spectral model on the underlying test-function carrier. -/
theorem spectralModel_toTestFunction (f : ZetaAdmissibleFunction) :
    spectralModel f = ZetaTestFunction.toZetaExplicitFormulaTransform f.toZetaTestFunction' := by
  rfl

/-- The admissible spectral model is the explicit-formula transform of the underlying test
function. -/
theorem spectralModel_pair (f : ZetaAdmissibleFunction) :
    spectralModel f = ZetaTestFunction.toZetaExplicitFormulaTransform f.toZetaTestFunction' := by
  rfl

/-- The admissible spectral model is the transform of the underlying test function. -/
theorem admissible_spectralModel (f : ZetaAdmissibleFunction) :
    spectralModel f = ZetaTestFunction.toZetaExplicitFormulaTransform f.toZetaTestFunction' := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
