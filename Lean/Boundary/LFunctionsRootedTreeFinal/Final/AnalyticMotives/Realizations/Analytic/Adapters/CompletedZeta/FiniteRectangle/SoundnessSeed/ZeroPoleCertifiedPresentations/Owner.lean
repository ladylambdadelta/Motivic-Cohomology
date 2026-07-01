import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPolePresentationSpines.Owner

/-!
# Zero-pole certified presentations

This file is the first concrete certified-presentation layer.

It does not introduce a generic certificate carrier.  Instead, it attaches the
already proved completed-zeta analytic soundness theorems to the two raw
zero-pole presentation spines.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue seed presentation is certified by the finite-square residue theorem. -/
theorem completedZetaZeroPoleResiduePresentationSpine_certified
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleFiniteSquareResidueGenerator_sound
    f hPhi hR

/-- The certified residue presentation has the expected source expression. -/
theorem completedZetaZeroPoleResiduePresentationSpine_certified_source :
    completedZetaZeroPoleResiduePresentationSpine.source =
      completedZetaZeroPoleFiniteSquareBoundaryExpression :=
  completedZetaZeroPoleResiduePresentationSpine_source

/-- The certified residue presentation has the expected residue ledger. -/
theorem completedZetaZeroPoleResiduePresentationSpine_certified_ledger :
    completedZetaZeroPoleResiduePresentationSpine.ledger =
      completedZetaZeroPoleResidueLedger :=
  completedZetaZeroPoleResiduePresentationSpine_ledger

/-- The certified residue presentation has the expected residue schedule. -/
theorem completedZetaZeroPoleResiduePresentationSpine_certified_schedule :
    completedZetaZeroPoleResiduePresentationSpine.schedule =
      TraceSchedule.cons
        TraceRewriteKind.residue
        TraceSchedule.empty :=
  completedZetaZeroPoleResiduePresentationSpine_schedule

/-- The channel seed presentation is certified by scheduled rectangle algebra. -/
theorem completedZetaZeroPoleChannelPresentationSpine_certified
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelGenerator_sound
    f F h u

/-- The certified channel presentation has the expected source expression. -/
theorem completedZetaZeroPoleChannelPresentationSpine_certified_source :
    completedZetaZeroPoleChannelPresentationSpine.source =
      completedZetaZeroPoleChannelSourceExpression :=
  completedZetaZeroPoleChannelPresentationSpine_source

/-- The certified channel presentation has the expected visible channels. -/
theorem completedZetaZeroPoleChannelPresentationSpine_certified_channels :
    completedZetaZeroPoleChannelPresentationSpine.channels =
      completedZetaZeroPoleChannelExpressionList :=
  completedZetaZeroPoleChannelPresentationSpine_channels

/-- The certified channel presentation has the expected channel schedule. -/
theorem completedZetaZeroPoleChannelPresentationSpine_certified_schedule :
    completedZetaZeroPoleChannelPresentationSpine.schedule =
      TraceSchedule.cons
        TraceRewriteKind.channel
        TraceSchedule.empty :=
  completedZetaZeroPoleChannelPresentationSpine_schedule

end AnalyticMotives
end LFunctions
end Boundary
