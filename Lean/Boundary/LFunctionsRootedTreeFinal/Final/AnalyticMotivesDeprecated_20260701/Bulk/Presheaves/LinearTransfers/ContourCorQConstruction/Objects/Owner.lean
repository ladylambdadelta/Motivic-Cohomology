import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.CategoryInput.Owner

/-!
# Constructed `ContourCor_Q` linear presheaf objects

This owner names the presheaf objects used by the constructive transfer lane.
The objects are the already-built linear presheaves on the constructed
`ContourCor_Q` input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects in the constructed linear presheaf transfer lane. -/
abbrev ConstructedContourPresheafObject :=
  ContourCorQLinearPresheafObject

namespace ConstructedContourPresheafObject

/-- The value type of a constructed contour presheaf on a bulk object. -/
def valueAt (F : ConstructedContourPresheafObject)
    (X : ContourCorQPresheafObject) : Type :=
  F.valueAt X

/-- Pullback along a constructed `ContourCor_Q` hom. -/
def pullbackAlong (F : ConstructedContourPresheafObject)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y) :
    F.valueAt Y → F.valueAt X :=
  F.pullbackAlong f

/-- The zero element in the value over a bulk object. -/
def zeroAt (F : ConstructedContourPresheafObject)
    (X : ContourCorQPresheafObject) : F.valueAt X :=
  F.zeroAt X

/-- Addition in the value over a bulk object. -/
def addAt (F : ConstructedContourPresheafObject)
    (X : ContourCorQPresheafObject) :
    F.valueAt X → F.valueAt X → F.valueAt X :=
  F.addAt X

/-- Scalar multiplication in the value over a bulk object. -/
def scaleAt (F : ConstructedContourPresheafObject)
    (X : ContourCorQPresheafObject) :
    ℚ → F.valueAt X → F.valueAt X :=
  F.linearValues.scaleAt X

end ConstructedContourPresheafObject

end AnalyticMotives
end LFunctions
end Boundary
