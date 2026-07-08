import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectangleTypedClass.Owner

/-!
# Core zero-pole rectangle-certified pipeline data

This file owns the named data of the first rectangle-certified completed-zeta
residue trace-correspondence pipeline.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The rectangle certificate used by the completed-zeta zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_rectangle
    (R : ℝ) :
    ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  completedZetaZeroPoleFiniteSquareRectangle R

/-- The source presentation of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_source
    (R : ℝ) :
    TraceCorQObject :=
  completedZetaZeroPoleResidueRectangleHomSource R

/-- The target presentation of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_target :
    TraceCorQObject :=
  completedZetaZeroPoleResidueRectangleHomTarget

/-- The transport used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_transport
    (R : ℝ) :
    TraceTransport :=
  completedZetaZeroPoleResidueTransportWithRectangle R

/-- The generator used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_generator
    (R : ℝ) :
    TraceCorQGenerator :=
  completedZetaZeroPoleResidueRectangleTraceCorQGenerator R

/-- The typed term used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_term
    (R : ℝ) :
    TraceCorQHomTerm
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomTerm R

/-- The typed formal sum used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_formalSum
    (R : ℝ) :
    TraceCorQHomFormalSum
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R

/-- The typed hom of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_hom
    (R : ℝ) :
    TraceCorQHom
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHom R

/-- The explicit representative of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_representative
    (R : ℝ) :
    TraceCorQHomRepresentative
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R

/-- The ambient candidate of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_candidate
    (R : ℝ) :
    TraceCorQQuotientCandidate :=
  completedZetaZeroPoleResidueRectangleTraceCorQCandidate R

/-- The ambient quotient class of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_quotient
    (R : ℝ) :
    TraceCorQQuotient :=
  completedZetaZeroPoleResidueRectangleTraceCorQQuotient R

end AnalyticMotives
end LFunctions
end Boundary
