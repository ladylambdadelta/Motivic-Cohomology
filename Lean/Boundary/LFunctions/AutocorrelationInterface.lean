import Boundary.LFunctions.ProbeInterface
import Boundary.LFunctions.AutocorrelationCore

/-!
# Boundary autocorrelation interface

This file names the autocorrelation-generated probes without pulling the
criterion layer into the transform/probe construction stack.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The probe is an autocorrelation-generated admissible function. -/
def IsZetaAutocorrelationProbe (φ : ZetaProbe) : Prop :=
  ∃ f : ZetaAdmissibleFunction,
    φ.toZetaTestFunction' = ZetaAdmissibleFunction.autocorrelation f

end
end LFunctions
end Boundary
