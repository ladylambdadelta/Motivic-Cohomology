import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleTransform.Owner

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
    ZetaTestFunction.zetaExplicitFormulaLinearTransform :=
  toZetaExplicitFormulaLinearTransform f

/-- The admissible spectral model is exactly the admissible explicit-formula transform. -/
theorem spectralModel_eq (f : ZetaAdmissibleFunction) :
    spectralModel f = toZetaExplicitFormulaLinearTransform f := by
  rfl

/-- The admissible spectral model of a sum is the sum of the spectral models. -/
theorem spectralModel_add (f g : ZetaAdmissibleFunction) :
    spectralModel (f + g) = spectralModel f + spectralModel g := by
  exact ZetaAdmissibleFunction.toZetaExplicitFormulaLinearTransform_add f g

/-- The admissible spectral model of a scalar multiple is the scalar multiple of the spectral
model. -/
theorem spectralModel_smul (a : ℂ) (f : ZetaAdmissibleFunction) :
    spectralModel (a • f) = a • spectralModel f := by
  exact ZetaAdmissibleFunction.toZetaExplicitFormulaLinearTransform_smul a f

/-- The admissible spectral model commutes with finite sums. -/
theorem spectralModel_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    spectralModel (∑ a in s, f a) = ∑ a in s, spectralModel (f a) := by
  exact ZetaAdmissibleFunction.toZetaExplicitFormulaLinearTransform_sum (s := s) f

/-- The admissible spectral model on the underlying test-function carrier. -/
theorem spectralModel_toTestFunction (f : ZetaAdmissibleFunction) :
    spectralModel f = ZetaTestFunction.toZetaExplicitFormulaLinearTransform f.toZetaTestFunction' := by
  rfl

/-- The admissible spectral model is the explicit-formula transform of the underlying test
function. -/
theorem spectralModel_pair (f : ZetaAdmissibleFunction) :
    spectralModel f = ZetaTestFunction.toZetaExplicitFormulaLinearTransform f.toZetaTestFunction' := by
  rfl

/-- The admissible spectral model is the transform of the underlying test function. -/
theorem admissible_spectralModel (f : ZetaAdmissibleFunction) :
    spectralModel f = ZetaTestFunction.toZetaExplicitFormulaLinearTransform f.toZetaTestFunction' := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
