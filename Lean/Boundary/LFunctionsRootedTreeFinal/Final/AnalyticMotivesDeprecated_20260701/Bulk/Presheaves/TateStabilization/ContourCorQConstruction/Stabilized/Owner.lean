import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.ContourCorQConstruction.Shift.Owner

/-!
# Constructed Tate-stabilized presheaves

This owner packages formal Tate spectra as the concrete constructed
Tate-stabilized presheaf layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A constructed Tate-stabilized analytic presheaf. -/
structure ConstructedTateStabilizedAnalyticPresheaf where
  spectrum : ConstructedTateSpectrum

namespace ConstructedTateStabilizedAnalyticPresheaf

/-- The formal Tate spectrum carried by a constructed stabilized presheaf. -/
def underlyingSpectrum
    (F : ConstructedTateStabilizedAnalyticPresheaf) :
    ConstructedTateSpectrum :=
  F.spectrum

/-- The interval-local presheaf at one Tate weight. -/
def levelAt
    (F : ConstructedTateStabilizedAnalyticPresheaf)
    (n : Int) :
    ConstructedIntervalLocalAnalyticPresheaf :=
  F.spectrum.levelAt n

/-- The plus-one Tate twist of a constructed stabilized presheaf. -/
def twistPlus
    (F : ConstructedTateStabilizedAnalyticPresheaf) :
    ConstructedTateStabilizedAnalyticPresheaf where
  spectrum := F.spectrum.shiftPlus

/-- The backward Tate twist of a constructed stabilized presheaf. -/
def twistBackward
    (F : ConstructedTateStabilizedAnalyticPresheaf) :
    ConstructedTateStabilizedAnalyticPresheaf where
  spectrum := F.spectrum.shiftBackward

/-- Build a stabilized presheaf from a single interval-local presheaf. -/
def constant
    (F : ConstructedIntervalLocalAnalyticPresheaf) :
    ConstructedTateStabilizedAnalyticPresheaf where
  spectrum := ConstructedTateSpectrum.constant F

/-- The plus-one twist at one Tate weight. -/
theorem twistPlus_levelAt
    (F : ConstructedTateStabilizedAnalyticPresheaf)
    (n : Int) :
    F.twistPlus.levelAt n = F.levelAt (n + 1) :=
  rfl

/-- The backward twist at one Tate weight. -/
theorem twistBackward_levelAt
    (F : ConstructedTateStabilizedAnalyticPresheaf)
    (n : Int) :
    F.twistBackward.levelAt n = F.levelAt (n - 1) :=
  rfl

/-- Constant stabilized presheaves have the selected value at every weight. -/
theorem constant_levelAt
    (F : ConstructedIntervalLocalAnalyticPresheaf)
    (n : Int) :
    (constant F).levelAt n = F :=
  rfl

end ConstructedTateStabilizedAnalyticPresheaf

end AnalyticMotives
end LFunctions
end Boundary
