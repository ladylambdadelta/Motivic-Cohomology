import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTraceValue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Owner

/-!
# Zero-pole finite-square residue generator

This file owns the synthetic residue generator realized by the zero-pole
finite-square analytic theorem.

The generator is deliberately narrow: one boundary trace atom rewrites to one
residue trace atom.  The analytic soundness theorem for this generator is
proved in the same file from the concrete finite-square residue theorem exposed
by `ZeroPoleTraceValue`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The synthetic stage index for the zero-pole finite-square seed. -/
def completedZetaZeroPoleFiniteSquareStage : TraceStageIndex :=
  0

/-- The synthetic boundary-face index for the zero-pole finite-square seed. -/
def completedZetaZeroPoleFiniteSquareFace : TraceFaceIndex :=
  0

/-- The synthetic boundary atom for the zero-pole finite-square seed. -/
def completedZetaZeroPoleFiniteSquareBoundaryAtom : TraceAtom :=
  TraceAtom.boundary
    completedZetaZeroPoleFiniteSquareStage
    completedZetaZeroPoleFiniteSquareFace

/-- The synthetic residue atom for the zero-pole finite-square seed. -/
def completedZetaZeroPoleFiniteSquareResidueAtom : TraceAtom :=
  TraceAtom.residue
    completedZetaZeroPoleFiniteSquareStage
    completedZetaZeroPoleFiniteSquareFace

/-- The source expression for the zero-pole finite-square residue generator. -/
def completedZetaZeroPoleFiniteSquareBoundaryExpression : QTraceExpression :=
  QTraceExpression.singleton
    1
    completedZetaZeroPoleFiniteSquareBoundaryAtom

/-- The target expression for the zero-pole finite-square residue generator. -/
def completedZetaZeroPoleFiniteSquareResidueExpression : QTraceExpression :=
  QTraceExpression.singleton
    1
    completedZetaZeroPoleFiniteSquareResidueAtom

/-- The synthetic residue generator realized by the zero-pole finite-square theorem. -/
def completedZetaZeroPoleFiniteSquareResidueGenerator : TraceRewriteGenerator :=
  TraceRewriteGenerator.residue
    completedZetaZeroPoleFiniteSquareBoundaryExpression
    completedZetaZeroPoleFiniteSquareResidueExpression

/-- The zero-pole finite-square generator is a residue rewrite. -/
theorem completedZetaZeroPoleFiniteSquareResidueGenerator_kind :
    completedZetaZeroPoleFiniteSquareResidueGenerator.kind =
      TraceRewriteKind.residue :=
  rfl

/-- The zero-pole finite-square generator starts at the boundary expression. -/
theorem completedZetaZeroPoleFiniteSquareResidueGenerator_source :
    completedZetaZeroPoleFiniteSquareResidueGenerator.source =
      completedZetaZeroPoleFiniteSquareBoundaryExpression :=
  rfl

/-- The zero-pole finite-square generator targets the residue expression. -/
theorem completedZetaZeroPoleFiniteSquareResidueGenerator_target :
    completedZetaZeroPoleFiniteSquareResidueGenerator.target =
      completedZetaZeroPoleFiniteSquareResidueExpression :=
  rfl

/--
Analytic soundness of the zero-pole finite-square residue generator.

The proof is exactly the concrete finite-square boundary/residue equality
imported from the RH lane and exposed as an analytic trace-value equality.
-/
theorem completedZetaZeroPoleFiniteSquareResidueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleFiniteSquareBoundaryTrace_eq_residueTrace
    f hPhi hR

end AnalyticMotives
end LFunctions
end Boundary
