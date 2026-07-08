import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Owner

/-!
# Endpoint represented objects and maps in the comparison source

This file exposes the object and morphism projections from additive analytic
homotopy motives into the stable analytic comparison source at endpoint names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Endpoint represented source object obtained by applying the stable analytic
quotient. -/
def TraceAnalyticMotiveComparison.sourceObjectOf
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf object

/-- Endpoint represented source object is the comparison-source owner object
projection. -/
theorem TraceAnalyticMotiveComparison.sourceObjectOf_eq_source
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticMotiveComparison.sourceObjectOf object =
      TraceAnalyticDMgmComparisonSource.objectOf object :=
  rfl

/-- Endpoint represented source object is the stable homotopy comparison object
projection. -/
theorem TraceAnalyticMotiveComparison.sourceObjectOf_eq_stableHomotopy
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticMotiveComparison.sourceObjectOf object =
      TraceAnalyticStableHomotopyComparisonSource.objectOf object :=
  rfl

/-- Endpoint represented source object is the stable analytic quotient object
projection. -/
theorem TraceAnalyticMotiveComparison.sourceObjectOf_eq_stable
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticMotiveComparison.sourceObjectOf object =
      TraceAnalyticStableMotiveCategory.objectOf object :=
  TraceAnalyticDMgmComparisonSource.objectOf_eq_stable object

/-- Stable-homotopy endpoint represented source object. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceObjectOf
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticStableHomotopyComparisonSource.objectOf object

/-- Stable-homotopy endpoint represented source object is the stable homotopy
comparison object projection. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceObjectOf_eq_stableHomotopy
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticMotiveComparison.stableHomotopySourceObjectOf object =
      TraceAnalyticStableHomotopyComparisonSource.objectOf object :=
  rfl

/-- Endpoint represented source morphism obtained by applying the stable
analytic quotient. -/
def TraceAnalyticMotiveComparison.sourceMapOf
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceObjectOf source ⟶
      TraceAnalyticMotiveComparison.sourceObjectOf target :=
  TraceAnalyticDMgmComparisonSource.mapOf hom

/-- Endpoint represented source morphism is the comparison-source owner
morphism projection. -/
theorem TraceAnalyticMotiveComparison.sourceMapOf_eq_source
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceMapOf hom =
      TraceAnalyticDMgmComparisonSource.mapOf hom :=
  rfl

/-- Endpoint represented source morphism is the stable homotopy comparison
morphism projection. -/
theorem TraceAnalyticMotiveComparison.sourceMapOf_eq_stableHomotopy
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceMapOf hom =
      TraceAnalyticStableHomotopyComparisonSource.mapOf hom :=
  rfl

/-- Endpoint represented source morphism is the stable analytic quotient
morphism projection. -/
theorem TraceAnalyticMotiveComparison.sourceMapOf_eq_stable
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceMapOf hom =
      TraceAnalyticStableMotiveCategory.mapOf hom :=
  TraceAnalyticDMgmComparisonSource.mapOf_eq_stable hom

/-- Stable-homotopy endpoint represented source morphism. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceMapOf
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.stableHomotopySourceObjectOf source ⟶
      TraceAnalyticMotiveComparison.stableHomotopySourceObjectOf target :=
  TraceAnalyticStableHomotopyComparisonSource.mapOf hom

/-- Stable-homotopy endpoint represented source morphism is the stable homotopy
comparison morphism projection. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceMapOf_eq_stableHomotopy
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.stableHomotopySourceMapOf hom =
      TraceAnalyticStableHomotopyComparisonSource.mapOf hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
