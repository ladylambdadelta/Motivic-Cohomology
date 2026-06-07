import Boundary.LFunctions.ZetaPacketComparison

/-!
# Boundary zeta purity / normalization

This file isolates the positivity upgrade from signed boundary transport to
the packet norm square. It does not introduce any new analytic content; it
packages the existing packet-comparison theorem under a purity-shaped name so
the explicit-formula DAG has a clean owner node for the normalization step.

The intended classical route is:

```text
signed boundary defect
→ packet comparison
→ packet norm square
→ positivity
```

The file is deliberately small and explicit.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Purity / normalization for the boundary defect: the boundary-defect Gram
form agrees with the packet norm square. -/
abbrev ZetaBoundaryPurity (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f

/-- The boundary-defect Gram satisfies the purity / normalization condition. -/
theorem zetaBoundaryPurity_of_packetComparison (f : ZetaAdmissibleFunction) :
    ZetaBoundaryPurity f := by
  exact zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The boundary-defect Gram is nonnegative by purity / normalization. -/
theorem zetaBoundaryPurity_nonnegative (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectGram f := by
  rw [zetaBoundaryPurity_of_packetComparison f]
  exact zetaCompletedPacketNormSq_nonnegative f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
