import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleTypedClass.Owner

/-!
# Core zero-pole scheduled-rectangle channel pipeline data

This file owns the named data of the scheduled-rectangle channel
trace-correspondence pipeline.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The scheduled rectangle certificate used by the zero-pole channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  completedZetaZeroPoleScheduledChannelRectangle f F h u

/-- The source presentation of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQObject :=
  completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u

/-- The target presentation of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_target :
    TraceCorQObject :=
  completedZetaZeroPoleChannelScheduledRectangleHomTarget

/-- The transport used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceTransport :=
  completedZetaZeroPoleChannelTransportWithScheduledRectangle f F h u

/-- The generator used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQGenerator :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator f F h u

/-- The typed term used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomTerm
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
    f F h u

/-- The typed singleton formal sum used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomFormalSum
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
    f F h u

/-- The typed hom of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_hom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHom
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom f F h u

/-- The explicit representative of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomRepresentative
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
    f F h u

/-- The ambient candidate of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotientCandidate :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate f F h u

/-- The ambient quotient class of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_quotient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotient :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u

/-- The rectangle ledger used by the pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ResidueChannelCertificateLedger :=
  completedZetaZeroPoleScheduledChannelRectangleCertificateLedger
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
