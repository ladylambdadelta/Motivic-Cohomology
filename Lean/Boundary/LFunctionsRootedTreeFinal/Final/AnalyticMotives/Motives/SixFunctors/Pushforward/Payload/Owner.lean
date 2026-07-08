import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Payload for compact-generator pushforward functional

This file records the concrete endpoint payload attached to compact-generator
pushforward.  Unlike pullback on sections, pushforward on compact
representables is covariant, so source endpoint payload remains source payload
and target endpoint payload remains target payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint imported rectangles of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  morphism.sourceImportedRectangles

/-- Target endpoint imported rectangles of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  morphism.targetImportedRectangles

/-- Source endpoint imported-rectangle count of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  morphism.sourceImportedRectangleCount

/-- Target endpoint imported-rectangle count of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  morphism.targetImportedRectangleCount

/-- Source endpoint bookkeeping count of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  morphism.sourceTraceBookkeepingCount

/-- Target endpoint bookkeeping count of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  morphism.targetTraceBookkeepingCount

/-- Source endpoint rewrite count of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  morphism.sourceRewriteStepCount

/-- Target endpoint rewrite count of the compact-generator pushforward functional. -/
def TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  morphism.targetRewriteStepCount

/-- Pushforward source payload count is counted by its rectangle list. -/
theorem TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount morphism =
      (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
    morphism

/-- Pushforward target payload count is counted by its rectangle list. -/
theorem TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount morphism =
      (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
    morphism

/-- Identity pushforward has matching source and target imported rectangles. -/
theorem TraceSixFunctorPushforward.compactGenerator_id_sourceTargetImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
        (𝟙 generator) =
      TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
        (𝟙 generator) :=
  rfl

/-- Identity pushforward has matching source and target imported-rectangle counts. -/
theorem TraceSixFunctorPushforward.compactGenerator_id_sourceTargetImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount
        (𝟙 generator) =
      TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount
        (𝟙 generator) :=
  rfl

/-- Identity pushforward has matching source and target bookkeeping counts. -/
theorem TraceSixFunctorPushforward.compactGenerator_id_sourceTargetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount
        (𝟙 generator) =
      TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount
        (𝟙 generator) :=
  rfl

/-- Identity pushforward has matching source and target rewrite counts. -/
theorem TraceSixFunctorPushforward.compactGenerator_id_sourceTargetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount
        (𝟙 generator) =
      TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount
        (𝟙 generator) :=
  rfl

/-- Composed pushforward source payload is the left morphism source endpoint payload. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_sourceImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
        (left ≫ right) =
      left.sourceImportedRectangles :=
  rfl

/-- Composed pushforward target payload is the right morphism target endpoint payload. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_targetImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
        (left ≫ right) =
      right.targetImportedRectangles :=
  rfl

/-- Composed pushforward source count is the left morphism source endpoint count. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_sourceImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount
        (left ≫ right) =
      left.sourceImportedRectangleCount :=
  rfl

/-- Composed pushforward target count is the right morphism target endpoint count. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_targetImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount
        (left ≫ right) =
      right.targetImportedRectangleCount :=
  rfl

/-- Composed pushforward source bookkeeping count is the left source endpoint count. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_sourceTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount
        (left ≫ right) =
      left.sourceTraceBookkeepingCount :=
  rfl

/-- Composed pushforward target bookkeeping count is the right target endpoint count. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_targetTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount
        (left ≫ right) =
      right.targetTraceBookkeepingCount :=
  rfl

/-- Composed pushforward source rewrite count is the left source endpoint count. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_sourceRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount
        (left ≫ right) =
      left.sourceRewriteStepCount :=
  rfl

/-- Composed pushforward target rewrite count is the right target endpoint count. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp_targetRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount
        (left ≫ right) =
      right.targetRewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
