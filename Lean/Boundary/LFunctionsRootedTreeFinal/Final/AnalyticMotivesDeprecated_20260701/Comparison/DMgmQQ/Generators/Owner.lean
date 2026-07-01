import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner

/-!
# Generator comparison with `DM_gm(ℚ)_ℚ`

This file owns the generator-level comparison between compact geometric
analytic motives and geometric motives over `ℚ`.  It is downstream from the
analytic stable category and does not define analytic motives by reference to
Voevodsky motives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An abstract target interface for `DM_gm(ℚ)_ℚ` used by the comparison layer.
Analytic motives are not defined by this interface; it is only the downstream
comparison target.
-/
structure DMgmQQTargetInterface where
  Object : Type
  compactGenerator : Object → Type

/--
Generator-level comparison from compact analytic motives to the abstract
`DM_gm(ℚ)_ℚ` target interface.
-/
structure DMgmQQGeneratorComparison
    (T : DMgmQQTargetInterface) where
  analyticGenerator : CompactAnalyticGenerator
  targetObject : T.Object
  targetGenerator : T.compactGenerator targetObject

namespace DMgmQQGeneratorComparison

/-- The analytic compact generator in a generator comparison. -/
def analytic {T : DMgmQQTargetInterface}
    (C : DMgmQQGeneratorComparison T) : CompactAnalyticGenerator :=
  C.analyticGenerator

/-- The target motivic object in a generator comparison. -/
def target {T : DMgmQQTargetInterface}
    (C : DMgmQQGeneratorComparison T) : T.Object :=
  C.targetObject

/-- The source bulk of the analytic compact generator in a generator comparison. -/
def analyticSource {T : DMgmQQTargetInterface}
    (C : DMgmQQGeneratorComparison T) :
    ContourAdmissibleBulk :=
  C.analyticGenerator.sourceBulk

/-- The stabilized presheaf of the analytic compact generator in a comparison. -/
def analyticStabilized {T : DMgmQQTargetInterface}
    (C : DMgmQQGeneratorComparison T) :
    TateStabilizedAnalyticPresheaf :=
  C.analyticGenerator.stabilizedPresheaf

/-- The target object is a compact generator in the comparison target. -/
def targetGeneratorData {T : DMgmQQTargetInterface}
    (C : DMgmQQGeneratorComparison T) :
    T.compactGenerator C.targetObject :=
  C.targetGenerator

end DMgmQQGeneratorComparison

end AnalyticMotives
end LFunctions
end Boundary
