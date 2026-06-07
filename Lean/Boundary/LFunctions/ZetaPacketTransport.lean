import Boundary.LFunctions.ZetaAdmissibleInterpolation
import Boundary.LFunctions.ZetaPacketEnergy

/-!
# Boundary zeta packet transport

This file packages the admissible-side transport surface that will eventually
feed the packet-energy comparison theorems. It only records the canonical
spectral/probe pair already available on the admissible side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The admissible transport data: spectral model together with the probe. -/
def packetTransportSurface (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.zetaExplicitFormulaTransform × ZetaTestFunction :=
  interpolationSurface f

/-- The admissible packet transport surface has the spectral model as first component. -/
theorem packetTransportSurface_fst (f : ZetaAdmissibleFunction) :
    (packetTransportSurface f).1 = spectralModel f := by
  rfl

/-- The admissible packet transport surface has the probe as second component. -/
theorem packetTransportSurface_snd (f : ZetaAdmissibleFunction) :
    (packetTransportSurface f).2 = separatingProbe f := by
  rfl

/-- The admissible packet transport surface is the interpolation surface. -/
theorem packetTransportSurface_eq (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = interpolationSurface f := by
  rfl

/-- The admissible packet transport surface is the spectral-model/probe pair. -/
theorem packetTransportSurface_pair (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = (spectralModel f, separatingProbe f) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
