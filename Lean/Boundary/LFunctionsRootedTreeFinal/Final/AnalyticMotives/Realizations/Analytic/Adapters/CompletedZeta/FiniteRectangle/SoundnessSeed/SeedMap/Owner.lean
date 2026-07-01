import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.Channels.Owner

/-!
# Completed-zeta finite-rectangle seed map

This file records the first concrete analytic theorem chosen as a soundness
seed for the synthetic trace computad.

## First seed

Imported theorem:

```text
zetaCompletedExplicitFormulaCorrectionZeroPole_finiteSquareBoundaryIntegral_eq_residue
```

Imported owner:

```text
ZetaExplicitFormulaVerticalChannels/OwnerParts/CorrectionPoleResidues.lean
```

Computadic role:

```text
TraceRewriteKind.residue
```

Analytic meaning:

```text
finite square boundary integral around the zero correction pole
=
2*pi*i times the normalized local residue
```

This is the first safe bridge because the theorem already performs the real
analytic work: deleted-coefficient continuity, differentiability off the pole,
local residue convergence, and the finite-square Cauchy residue theorem.

The next Lean step is not to invent a new theorem statement.  It is to define
the analytic trace-value interpretation narrow enough that this imported
theorem can be applied directly as generator soundness.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
