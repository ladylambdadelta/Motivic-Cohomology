import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

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
analytic work: punctured-coefficient continuity, differentiability off the pole,
local residue convergence, and the finite-square Cauchy residue theorem.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The rewrite role of the first completed-zeta finite-rectangle soundness seed. -/
def completedZetaFiniteRectangleSeedMap.kind :
    TraceRewriteKind :=
  TraceRewriteKind.residue

/-- The first completed-zeta soundness seed has residue-generator role. -/
theorem completedZetaFiniteRectangleSeedMap.kind_eq_residue :
    completedZetaFiniteRectangleSeedMap.kind =
      TraceRewriteKind.residue :=
  rfl

/--
The first completed-zeta soundness seed, before packaging the two sides as
named analytic trace values.
-/
theorem completedZetaFiniteRectangleSeedMap.zeroPole_raw
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ)
        R =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_finiteSquareBoundaryIntegral_eq_residue
    f
    hPhi
    hR

end AnalyticMotives
end LFunctions
end Boundary
