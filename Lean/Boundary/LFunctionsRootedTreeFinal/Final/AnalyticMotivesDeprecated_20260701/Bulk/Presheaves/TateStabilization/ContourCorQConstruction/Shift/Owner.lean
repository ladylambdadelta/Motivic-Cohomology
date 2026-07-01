import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.ContourCorQConstruction.Spectra.Owner

/-!
# Formal Tate shifts

This owner defines Tate shift operations on constructed formal Tate spectra
through reindexing of the integer Tate-weight tower.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedTateSpectrum

/-- The plus-one formal Tate shift. -/
def shiftPlus (E : ConstructedTateSpectrum) :
    ConstructedTateSpectrum where
  level := fun n => E.levelAt (n + 1)

/-- The backward formal Tate shift. -/
def shiftBackward (E : ConstructedTateSpectrum) :
    ConstructedTateSpectrum where
  level := fun n => E.levelAt (n - 1)

/-- The plus-one shift at a given weight. -/
theorem shiftPlus_levelAt
    (E : ConstructedTateSpectrum) (n : Int) :
    E.shiftPlus.levelAt n = E.levelAt (n + 1) :=
  rfl

/-- The backward shift at a given weight. -/
theorem shiftBackward_levelAt
    (E : ConstructedTateSpectrum) (n : Int) :
    E.shiftBackward.levelAt n = E.levelAt (n - 1) :=
  rfl

/-- The plus-one shift of a constant spectrum is pointwise constant. -/
theorem shiftPlus_constant_levelAt
    (F : ConstructedIntervalLocalAnalyticPresheaf)
    (n : Int) :
    (constant F).shiftPlus.levelAt n = F :=
  rfl

/-- The backward shift of a constant spectrum is pointwise constant. -/
theorem shiftBackward_constant_levelAt
    (F : ConstructedIntervalLocalAnalyticPresheaf)
    (n : Int) :
    (constant F).shiftBackward.levelAt n = F :=
  rfl

end ConstructedTateSpectrum

end AnalyticMotives
end LFunctions
end Boundary
