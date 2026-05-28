import Geometry.Schemes
import Geometry.Cycles
import Geometry.Correspondences
import Geometry.Localization
import Geometry.Generators

/-!
# Geometry

This root namespace will house the algebraic-geometric input to the project: schemes, cycle
theory, finite correspondences, localization packages, and geometric generator families. The goal
is to isolate the geometric mathematics from the trace-specific and period-specific comparison
layers.

TODO: code will be added in later extraction slices.
-/

namespace Geometry

abbrev ChapterLoaded : Type := PUnit

def chapterLoaded : ChapterLoaded := PUnit.unit

end Geometry
