import Boundary.LFunctions.ZetaAdmissibleFunction

/-!
# Boundary probe interface

This file owns the ambient probe carrier used by the Weil criterion layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The probe carrier used by the hard branch. -/
abbrev ZetaProbe := ZetaAdmissibleFunction

end
end LFunctions
end Boundary
