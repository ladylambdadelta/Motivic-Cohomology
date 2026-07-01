import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.ContourCorQConstruction.Owner

/-!
# Constructed compact generators

This owner defines compact generators for the constructed analytic motive lane:
a contour-admissible source bulk together with its constructed
Tate-stabilized presheaf.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact generator in the constructed analytic motive lane. -/
structure ConstructedCompactAnalyticGenerator where
  sourceBulk : ContourAdmissibleBulk
  stabilizedPresheaf : ConstructedTateStabilizedAnalyticPresheaf

namespace ConstructedCompactAnalyticGenerator

/-- The contour-admissible bulk underlying a constructed compact generator. -/
def source (G : ConstructedCompactAnalyticGenerator) :
    ContourAdmissibleBulk :=
  G.sourceBulk

/-- The constructed Tate-stabilized presheaf carried by a generator. -/
def stabilized (G : ConstructedCompactAnalyticGenerator) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  G.stabilizedPresheaf

/-- The source bulk core of a constructed compact generator. -/
def sourceCore (G : ConstructedCompactAnalyticGenerator) :
    AnalyticBulkCore :=
  G.sourceBulk.core

/-- The interval-local level at one Tate weight. -/
def levelAt (G : ConstructedCompactAnalyticGenerator)
    (n : Int) :
    ConstructedIntervalLocalAnalyticPresheaf :=
  G.stabilizedPresheaf.levelAt n

/-- The plus-one Tate twist of a constructed compact generator. -/
def twistPlus (G : ConstructedCompactAnalyticGenerator) :
    ConstructedCompactAnalyticGenerator where
  sourceBulk := G.sourceBulk
  stabilizedPresheaf := G.stabilizedPresheaf.twistPlus

/-- The minus-one Tate twist of a constructed compact generator. -/
def twistBackward (G : ConstructedCompactAnalyticGenerator) :
    ConstructedCompactAnalyticGenerator where
  sourceBulk := G.sourceBulk
  stabilizedPresheaf := G.stabilizedPresheaf.twistBackward

/-- The plus-one twist level is the next Tate level. -/
theorem twistPlus_levelAt
    (G : ConstructedCompactAnalyticGenerator)
    (n : Int) :
    G.twistPlus.levelAt n = G.levelAt (n + 1) :=
  ConstructedTateStabilizedAnalyticPresheaf.twistPlus_levelAt
    G.stabilizedPresheaf n

/-- The minus-one twist level is the previous Tate level. -/
theorem twistBackward_levelAt
    (G : ConstructedCompactAnalyticGenerator)
    (n : Int) :
    G.twistBackward.levelAt n = G.levelAt (n - 1) :=
  ConstructedTateStabilizedAnalyticPresheaf.twistBackward_levelAt
    G.stabilizedPresheaf n

end ConstructedCompactAnalyticGenerator

end AnalyticMotives
end LFunctions
end Boundary
