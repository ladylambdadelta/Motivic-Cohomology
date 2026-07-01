import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleAnalyticChain.Owner

/-!
# Zero-pole residue-channel coherence

This file names the first higher cell supported by the completed-zeta
finite-rectangle adapter.

The cell is deliberately narrow: it relates the residue and channel one-step
paths already certified by the analytic trace chain.  It does not assert a
general categorical composition theorem.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The raw residue-channel coherence cell present in the zero-pole seed. -/
def completedZetaZeroPoleResidueChannelCoherenceCell :
    TraceCoherenceCell :=
  TraceCoherenceCell.residueChannel
    completedZetaZeroPoleResiduePath
    completedZetaZeroPoleChannelPath

/-- The zero-pole coherence cell has residue-channel kind. -/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_kind :
    completedZetaZeroPoleResidueChannelCoherenceCell.kind =
      TraceCoherenceKind.residueChannel :=
  rfl

/-- The source path of the zero-pole coherence cell is the residue path. -/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_source :
    completedZetaZeroPoleResidueChannelCoherenceCell.source =
      completedZetaZeroPoleResiduePath :=
  rfl

/-- The target path of the zero-pole coherence cell is the channel path. -/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_target :
    completedZetaZeroPoleResidueChannelCoherenceCell.target =
      completedZetaZeroPoleChannelPath :=
  rfl

/--
The source path of the zero-pole coherence cell is backed by the residue
soundness theorem from the analytic chain.
-/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_source_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleAnalyticChain_residue_sound
    f hPhi hR

/--
The target path of the zero-pole coherence cell is backed by the channel
soundness theorem from the analytic chain.
-/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_target_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleAnalyticChain_channel_sound
    f F h u

/--
The zero-pole coherence cell is compatible with the tangent-boundary limit
which identifies the local tangent boundary with the finite-square residue
trace.
-/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_tangentBoundary_tendsto
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
      atTop
      (𝓝 (completedZetaZeroPoleFiniteSquareResidueTrace f)) :=
  completedZetaZeroPoleAnalyticChain_tangentBoundary_tendsto
    f F h

/--
The zero-pole coherence cell is compatible with the resulting right vertical
channel limit.
-/
theorem completedZetaZeroPoleResidueChannelCoherenceCell_rightVertical_tendsto
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledRightVerticalTraceFunction f F h)
      atTop
      (𝓝 (-(completedZetaZeroPoleFiniteSquareResidueTrace f * Complex.I))) :=
  completedZetaZeroPoleAnalyticChain_rightVertical_tendsto
    f F h

end AnalyticMotives
end LFunctions
end Boundary
