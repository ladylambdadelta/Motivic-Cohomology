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

/-- The admissible packet transport surface is the spectral model together with
the autocorrelation probe. -/
theorem packetTransportSurface_eq_spectralModel_autocorrelation (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = (spectralModel f, autocorrelation f) := by
  rw [packetTransportSurface_eq, interpolationSurface_eq_spectralModel_autocorrelation]

/-- The admissible packet transport surface is the spectral-model/probe pair. -/
theorem packetTransportSurface_pair (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The spectral-model component of a finite transport sum is the finite sum of spectral models. -/
theorem packetTransportSurface_fst_sum {α : Type*} (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    (packetTransportSurface (∑ a in s, f a)).1 = ∑ a in s, spectralModel (f a) := by
  rw [packetTransportSurface_fst, ZetaAdmissibleFunction.spectralModel_sum]

/-- The transport surface of a finite sum exposes the finite spectral sum in the first
component and the probe of the sum in the second component. -/
theorem packetTransportSurface_sum {α : Type*} (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    packetTransportSurface (∑ a in s, f a) =
      (∑ a in s, spectralModel (f a), separatingProbe (∑ a in s, f a)) := by
  ext <;> simp [packetTransportSurface_fst_sum, packetTransportSurface_snd, ZetaAdmissibleFunction.spectralModel_sum]

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
