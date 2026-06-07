import Boundary.LFunctions.ZetaAdmissibleProbe

/-!
# Boundary admissible interpolation

This file names the admissible-side interpolation surface available at the
moment: the spectral model and the separating probe.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The admissible interpolation surface is the pair of spectral model and probe. -/
def interpolationSurface (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.zetaExplicitFormulaTransform × ZetaTestFunction :=
  (spectralModel f, separatingProbe f)

/-- The interpolation surface has the admissible spectral model as first component. -/
theorem interpolationSurface_fst (f : ZetaAdmissibleFunction) :
    (interpolationSurface f).1 = spectralModel f := by
  rfl

/-- The interpolation surface has the admissible probe as second component. -/
theorem interpolationSurface_snd (f : ZetaAdmissibleFunction) :
    (interpolationSurface f).2 = separatingProbe f := by
  rfl

/-- The interpolation surface is built from the spectral model and probe. -/
theorem interpolationSurface_eq (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The admissible interpolation surface is the spectral model/probe pair. -/
theorem interpolationSurface_pair (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The admissible interpolation surface is exactly the model/probe pair. -/
theorem interpolationSurface_components (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
