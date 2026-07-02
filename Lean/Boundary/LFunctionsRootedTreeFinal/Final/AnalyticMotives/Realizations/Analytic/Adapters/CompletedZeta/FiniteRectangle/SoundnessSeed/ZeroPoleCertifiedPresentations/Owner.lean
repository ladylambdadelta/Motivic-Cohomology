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

/-- The certified residue presentation for the zero-pole finite-square seed. -/
def completedZetaZeroPoleResiduePresentation :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    completedZetaZeroPoleResiduePresentationSpine

/-- The certified channel presentation for the zero-pole scheduled-channel seed. -/
def completedZetaZeroPoleChannelPresentation :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    completedZetaZeroPoleChannelPresentationSpine

/-- The zero-pole residue presentation has the expected raw spine. -/
theorem completedZetaZeroPoleResiduePresentation_spine :
    completedZetaZeroPoleResiduePresentation.spine =
      completedZetaZeroPoleResiduePresentationSpine :=
  rfl

/-- The current residue presentation has no imported finite-rectangle certificate atom. -/
theorem completedZetaZeroPoleResiduePresentation_importedRectangleCount :
    completedZetaZeroPoleResiduePresentation.importedRectangleCount =
      0 :=
  rfl

/-- The current residue presentation records its four component certificates. -/
theorem completedZetaZeroPoleResiduePresentation_traceBookkeepingCount :
    completedZetaZeroPoleResiduePresentation.traceBookkeepingCount =
      4 :=
  rfl

/-- The zero-pole channel presentation has the expected raw spine. -/
theorem completedZetaZeroPoleChannelPresentation_spine :
    completedZetaZeroPoleChannelPresentation.spine =
      completedZetaZeroPoleChannelPresentationSpine :=
  rfl

/-- The current channel presentation has no imported finite-rectangle certificate atom. -/
theorem completedZetaZeroPoleChannelPresentation_importedRectangleCount :
    completedZetaZeroPoleChannelPresentation.importedRectangleCount =
      0 :=
  rfl

/-- The current channel presentation records its four component certificates. -/
theorem completedZetaZeroPoleChannelPresentation_traceBookkeepingCount :
    completedZetaZeroPoleChannelPresentation.traceBookkeepingCount =
      4 :=
  rfl

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

/-- The certified residue presentation has the expected source expression. -/
theorem completedZetaZeroPoleResiduePresentation_source :
    completedZetaZeroPoleResiduePresentation.source =
      completedZetaZeroPoleFiniteSquareBoundaryExpression :=
  completedZetaZeroPoleResiduePresentationSpine_source

/-- The certified residue presentation has the expected residue ledger. -/
theorem completedZetaZeroPoleResiduePresentationSpine_certified_ledger :
    completedZetaZeroPoleResiduePresentationSpine.ledger =
      completedZetaZeroPoleResidueLedger :=
  completedZetaZeroPoleResiduePresentationSpine_ledger

/-- The certified residue presentation has the expected residue ledger. -/
theorem completedZetaZeroPoleResiduePresentation_ledger :
    completedZetaZeroPoleResiduePresentation.ledger =
      completedZetaZeroPoleResidueLedger :=
  completedZetaZeroPoleResiduePresentationSpine_ledger

/-- The certified residue presentation has the expected residue schedule. -/
theorem completedZetaZeroPoleResiduePresentationSpine_certified_schedule :
    completedZetaZeroPoleResiduePresentationSpine.schedule =
      TraceSchedule.cons
        TraceRewriteKind.residue
        TraceSchedule.empty :=
  completedZetaZeroPoleResiduePresentationSpine_schedule

/-- The certified residue presentation has the expected residue schedule. -/
theorem completedZetaZeroPoleResiduePresentation_schedule :
    completedZetaZeroPoleResiduePresentation.schedule =
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

/-- The certified channel presentation has the expected source expression. -/
theorem completedZetaZeroPoleChannelPresentation_source :
    completedZetaZeroPoleChannelPresentation.source =
      completedZetaZeroPoleChannelSourceExpression :=
  completedZetaZeroPoleChannelPresentationSpine_source

/-- The certified channel presentation has the expected visible channels. -/
theorem completedZetaZeroPoleChannelPresentationSpine_certified_channels :
    completedZetaZeroPoleChannelPresentationSpine.channels =
      completedZetaZeroPoleChannelExpressionList :=
  completedZetaZeroPoleChannelPresentationSpine_channels

/-- The certified channel presentation has the expected visible channels. -/
theorem completedZetaZeroPoleChannelPresentation_channels :
    completedZetaZeroPoleChannelPresentation.channels =
      completedZetaZeroPoleChannelExpressionList :=
  completedZetaZeroPoleChannelPresentationSpine_channels

/-- The certified channel presentation has the expected channel schedule. -/
theorem completedZetaZeroPoleChannelPresentationSpine_certified_schedule :
    completedZetaZeroPoleChannelPresentationSpine.schedule =
      TraceSchedule.cons
        TraceRewriteKind.channel
        TraceSchedule.empty :=
  completedZetaZeroPoleChannelPresentationSpine_schedule

/-- The certified channel presentation has the expected channel schedule. -/
theorem completedZetaZeroPoleChannelPresentation_schedule :
    completedZetaZeroPoleChannelPresentation.schedule =
      TraceSchedule.cons
        TraceRewriteKind.channel
        TraceSchedule.empty :=
  completedZetaZeroPoleChannelPresentationSpine_schedule

end AnalyticMotives
end LFunctions
end Boundary
