import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.ContourCorQConstruction.CechObjects.Owner

/-!
# Constructed descent local equivalences

This owner records the local-equivalence datum for constructed Cech objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Local-equivalence data for one constructed Cech object. -/
structure ConstructedContourDescentLocalEquivalence
    {F : ConstructedContourPresheafObject}
    {C : ConstructedContourPresheafDescentCover F}
    (K : ConstructedContourCechObject C) where
  targetValue : ConstructedContourPresheafObject.valueAt F C.target
  target_eq_glued : targetValue = K.glued

namespace ConstructedContourDescentLocalEquivalence

/-- The target value selected by a local-equivalence datum. -/
def target {F : ConstructedContourPresheafObject}
    {C : ConstructedContourPresheafDescentCover F}
    {K : ConstructedContourCechObject C}
    (E : ConstructedContourDescentLocalEquivalence K) :
    ConstructedContourPresheafObject.valueAt F C.target :=
  E.targetValue

/-- The selected target agrees with the glued Cech value. -/
theorem target_eq_glued_value {F : ConstructedContourPresheafObject}
    {C : ConstructedContourPresheafDescentCover F}
    {K : ConstructedContourCechObject C}
    (E : ConstructedContourDescentLocalEquivalence K) :
    E.target = K.glued :=
  E.target_eq_glued

end ConstructedContourDescentLocalEquivalence

end AnalyticMotives
end LFunctions
end Boundary
