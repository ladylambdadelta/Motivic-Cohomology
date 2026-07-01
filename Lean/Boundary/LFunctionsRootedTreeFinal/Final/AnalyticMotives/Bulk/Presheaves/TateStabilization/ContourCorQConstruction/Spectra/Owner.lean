import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.ContourCorQConstruction.Owner

/-!
# Constructed formal Tate spectra

This owner defines the formal Tate-stabilized objects available from the
constructed interval-local presheaf layer: bi-infinite towers whose index is
the integer Tate weight.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A formal Tate spectrum of constructed interval-local presheaves. -/
structure ConstructedTateSpectrum where
  level : Int → ConstructedIntervalLocalAnalyticPresheaf

namespace ConstructedTateSpectrum

/-- The constructed interval-local presheaf at one Tate weight. -/
def levelAt (E : ConstructedTateSpectrum) (n : Int) :
    ConstructedIntervalLocalAnalyticPresheaf :=
  E.level n

/-- The descent-local object at one Tate weight. -/
def descentLevelAt (E : ConstructedTateSpectrum) (n : Int) :
    ConstructedDescentLocalAnalyticPresheaf :=
  (E.levelAt n).descentLocal

/-- The interval-locality data at one Tate weight. -/
def intervalLocalityAt (E : ConstructedTateSpectrum) (n : Int) :
    ConstructedIntervalLocalObject (E.descentLevelAt n) :=
  (E.levelAt n).intervalLocality

/-- Build a constant formal Tate spectrum from one interval-local presheaf. -/
def constant (F : ConstructedIntervalLocalAnalyticPresheaf) :
    ConstructedTateSpectrum where
  level := fun _ => F

/-- A constant formal Tate spectrum has the selected value at every weight. -/
theorem constant_levelAt
    (F : ConstructedIntervalLocalAnalyticPresheaf)
    (n : Int) :
    (constant F).levelAt n = F :=
  rfl

end ConstructedTateSpectrum

end AnalyticMotives
end LFunctions
end Boundary
