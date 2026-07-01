import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.Bulks.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.Soundness.ObjectsToBulks.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.Soundness.CorrespondencesToContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.Soundness.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.Soundness.Interval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.Soundness.Tate.Owner

/-!
# Soundness of analytification

This owner is reserved for the functorial direction from algebraic geometric
motives to contour analytic motives.  The intended chain is:

* smooth algebraic objects over `Q` give contour-admissible analytic bulks;
* finite algebraic correspondences give contour-compatible analytic
  correspondences;
* Nisnevich descent maps to conservative contour descent;
* `A1` maps to the chosen analytic interval object;
* Tate twists map to analytic Tate stabilization.

No functor is declared here until those component constructions exist.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
