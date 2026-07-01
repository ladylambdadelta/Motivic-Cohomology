import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelDecomposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Owner

/-!
# Zero-pole scheduled channel generator

This file owns the synthetic channel generator realized by the scheduled
zero-pole rectangle algebra theorem.

The generator records the finite computadic shape of the equality

```text
left vertical = right vertical + horizontal - boundary.
```

The analytic soundness theorem is exactly the concrete trace-value equality
from `ZeroPoleChannelDecomposition`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The synthetic stage index for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleChannelStage : TraceStageIndex :=
  1

/-- The left vertical channel index for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleLeftVerticalChannel : TraceChannelIndex :=
  0

/-- The right vertical channel index for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleRightVerticalChannel : TraceChannelIndex :=
  1

/-- The horizontal remainder channel index for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleHorizontalChannel : TraceChannelIndex :=
  2

/-- The rectangle-boundary face index for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleRectangleBoundaryFace : TraceFaceIndex :=
  0

/-- The left vertical source atom for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleLeftVerticalAtom : TraceAtom :=
  TraceAtom.channel
    completedZetaZeroPoleChannelStage
    completedZetaZeroPoleLeftVerticalChannel

/-- The right vertical output atom for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleRightVerticalAtom : TraceAtom :=
  TraceAtom.channel
    completedZetaZeroPoleChannelStage
    completedZetaZeroPoleRightVerticalChannel

/-- The horizontal remainder output atom for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleHorizontalAtom : TraceAtom :=
  TraceAtom.channel
    completedZetaZeroPoleChannelStage
    completedZetaZeroPoleHorizontalChannel

/-- The rectangle-boundary output atom for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleRectangleBoundaryAtom : TraceAtom :=
  TraceAtom.boundary
    completedZetaZeroPoleChannelStage
    completedZetaZeroPoleRectangleBoundaryFace

/-- The source expression for the zero-pole scheduled channel generator. -/
def completedZetaZeroPoleChannelSourceExpression : QTraceExpression :=
  QTraceExpression.singleton
    1
    completedZetaZeroPoleLeftVerticalAtom

/-- The target expression for the zero-pole scheduled channel generator. -/
def completedZetaZeroPoleChannelTargetExpression : QTraceExpression :=
  QTraceExpression.add
    (QTraceExpression.singleton
      1
      completedZetaZeroPoleRightVerticalAtom)
    (QTraceExpression.add
      (QTraceExpression.singleton
        1
        completedZetaZeroPoleHorizontalAtom)
      (QTraceExpression.singleton
        (-1)
        completedZetaZeroPoleRectangleBoundaryAtom))

/-- The synthetic channel generator realized by scheduled zero-pole rectangle algebra. -/
def completedZetaZeroPoleChannelGenerator : TraceRewriteGenerator :=
  TraceRewriteGenerator.channel
    completedZetaZeroPoleChannelSourceExpression
    completedZetaZeroPoleChannelTargetExpression

/-- The zero-pole scheduled channel generator is a channel rewrite. -/
theorem completedZetaZeroPoleChannelGenerator_kind :
    completedZetaZeroPoleChannelGenerator.kind =
      TraceRewriteKind.channel :=
  rfl

/-- The zero-pole scheduled channel generator starts at the left channel. -/
theorem completedZetaZeroPoleChannelGenerator_source :
    completedZetaZeroPoleChannelGenerator.source =
      completedZetaZeroPoleChannelSourceExpression :=
  rfl

/-- The zero-pole scheduled channel generator targets the right/horizontal/boundary expression. -/
theorem completedZetaZeroPoleChannelGenerator_target :
    completedZetaZeroPoleChannelGenerator.target =
      completedZetaZeroPoleChannelTargetExpression :=
  rfl

/--
Analytic soundness of the zero-pole scheduled channel generator.

The proof is exactly the concrete scheduled rectangle algebra theorem exposed
as an analytic trace-value equality.
-/
theorem completedZetaZeroPoleChannelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleLeftVerticalTrace_eq_channels
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
