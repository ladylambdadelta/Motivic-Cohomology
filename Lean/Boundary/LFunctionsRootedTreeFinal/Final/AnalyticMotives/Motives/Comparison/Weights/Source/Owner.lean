import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.Owner

/-!
# Source weights for analytic comparison

This file exposes the concrete analytic weight profile used on the source side
of the comparison.  It does not package a weight structure; it records the
numeric source weights already constructed in the weights lane.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Comparison-facing atom weight. -/
def TraceAnalyticMotiveComparison.sourceAtomWeight
    (atom : TraceAtom) :
    Nat :=
  atom.weightLevel

/-- The comparison-facing atom weight is the analytic atom weight level. -/
theorem TraceAnalyticMotiveComparison.sourceAtomWeight_eq_weightLevel
    (atom : TraceAtom) :
    TraceAnalyticMotiveComparison.sourceAtomWeight atom =
      atom.weightLevel :=
  rfl

/-- Boundary atoms have comparison-source weight zero. -/
theorem TraceAnalyticMotiveComparison.sourceAtomWeight_boundary
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    TraceAnalyticMotiveComparison.sourceAtomWeight
        (TraceAtom.boundary stage face) =
      0 :=
  TraceAtom.weightLevel_boundary stage face

/-- Residue atoms have comparison-source weight zero. -/
theorem TraceAnalyticMotiveComparison.sourceAtomWeight_residue
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    TraceAnalyticMotiveComparison.sourceAtomWeight
        (TraceAtom.residue stage face) =
      0 :=
  TraceAtom.weightLevel_residue stage face

/-- Channel atoms have comparison-source weight zero. -/
theorem TraceAnalyticMotiveComparison.sourceAtomWeight_channel
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    TraceAnalyticMotiveComparison.sourceAtomWeight
        (TraceAtom.channel stage channel) =
      0 :=
  TraceAtom.weightLevel_channel stage channel

/-- Weight-truncation atoms have their displayed comparison-source weight. -/
theorem TraceAnalyticMotiveComparison.sourceAtomWeight_weightTruncation
    (stage : TraceStageIndex)
    (level : Nat) :
    TraceAnalyticMotiveComparison.sourceAtomWeight
        (TraceAtom.weightTruncation stage level) =
      level :=
  TraceAtom.weightLevel_weightTruncation stage level

/-- Comparison-facing Q-linear trace-expression weight. -/
def TraceAnalyticMotiveComparison.sourceExpressionWeight
    (expression : QTraceExpression) :
    Nat :=
  expression.weightLevel

/-- The comparison-facing expression weight is the analytic expression weight
level. -/
theorem TraceAnalyticMotiveComparison.sourceExpressionWeight_eq_weightLevel
    (expression : QTraceExpression) :
    TraceAnalyticMotiveComparison.sourceExpressionWeight expression =
      expression.weightLevel :=
  rfl

/-- The zero expression has comparison-source weight zero. -/
theorem TraceAnalyticMotiveComparison.sourceExpressionWeight_zero :
    TraceAnalyticMotiveComparison.sourceExpressionWeight
        QTraceExpression.zero =
      0 :=
  QTraceExpression.weightLevel_zero

/-- A singleton expression records the comparison-source weight of its atom. -/
theorem TraceAnalyticMotiveComparison.sourceExpressionWeight_singleton
    (coefficient : Rat)
    (atom : TraceAtom) :
    TraceAnalyticMotiveComparison.sourceExpressionWeight
        (QTraceExpression.singleton coefficient atom) =
      Nat.max
        (TraceAnalyticMotiveComparison.sourceAtomWeight atom)
        0 :=
  QTraceExpression.weightLevel_singleton coefficient atom

/-- A cons expression records the maximum of head and tail comparison-source
weights. -/
theorem TraceAnalyticMotiveComparison.sourceExpressionWeight_cons
    (term : QTraceTerm)
    (tail : QTraceExpression) :
    TraceAnalyticMotiveComparison.sourceExpressionWeight
        (term :: tail) =
      Nat.max
        term.weightLevel
        (TraceAnalyticMotiveComparison.sourceExpressionWeight tail) :=
  QTraceExpression.weightLevel_cons term tail

/-- Comparison-facing certified trace-object weight. -/
def TraceAnalyticMotiveComparison.sourceTraceObjectWeight
    (object : TraceCorQObject) :
    Nat :=
  object.weightLevel

/-- Certified trace-object comparison-source weight is its source-expression
weight. -/
theorem TraceAnalyticMotiveComparison.sourceTraceObjectWeight_eq_source
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceObjectWeight object =
      TraceAnalyticMotiveComparison.sourceExpressionWeight object.source :=
  TraceCorQObject.weightLevel_eq_source object

/-- Adding certificates preserves comparison-source trace-object weight. -/
theorem TraceAnalyticMotiveComparison.sourceTraceObjectWeight_withAdditionalCertificates
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    TraceAnalyticMotiveComparison.sourceTraceObjectWeight
        (object.withAdditionalCertificates certificates) =
      TraceAnalyticMotiveComparison.sourceTraceObjectWeight object :=
  TraceCorQObject.withAdditionalCertificates_weightLevel object certificates

/-- Comparison-facing additive-object weight. -/
def TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight
    (object : TraceAnalyticAdditiveObject) :
    Nat :=
  object.weightLevel

/-- The zero additive object has comparison-source weight zero. -/
theorem TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight_zero :
    TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight
        TraceAnalyticAdditiveObject.zero =
      0 :=
  TraceAnalyticAdditiveObject.weightLevel_zero

/-- A nonempty additive object records the maximum of head and tail
comparison-source weights. -/
theorem TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight_cons
    (object : TraceCorQObject)
    (tail : TraceAnalyticAdditiveObject) :
    TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight
        (object :: tail) =
      Nat.max
        (TraceAnalyticMotiveComparison.sourceTraceObjectWeight object)
        (TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight tail) :=
  TraceAnalyticAdditiveObject.weightLevel_cons object tail

/-- Direct sum with an empty right family preserves comparison-source additive
weight. -/
theorem TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight_directSum_nil
    (left : TraceAnalyticAdditiveObject) :
    TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight
        (TraceAnalyticAdditiveObject.directSum left []) =
      TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight left :=
  TraceAnalyticAdditiveObject.weightLevel_directSum_nil left

end AnalyticMotives
end LFunctions
end Boundary
