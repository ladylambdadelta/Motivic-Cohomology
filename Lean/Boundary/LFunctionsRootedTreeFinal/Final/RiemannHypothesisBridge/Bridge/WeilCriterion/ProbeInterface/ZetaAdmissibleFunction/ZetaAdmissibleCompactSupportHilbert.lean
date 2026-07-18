import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunctionCore.Owner
import Mathlib.MeasureTheory.Function.LpSpace

/-!
# Compact-support Hilbert fibers for admissible probes

The Paley-Wiener interpolation argument works in a fixed compact-support
fiber, rather than in unrestricted `L²(ℝ)`: Laplace evaluations are bounded
on the former and are not bounded on the latter.  This file owns the concrete
`L²` carrier and the canonical embedding of admissible probes into each such
fiber.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The Hilbert carrier on a prescribed compact-support fiber. -/
def zetaCompactSupportHilbert (K : Set ℝ) : Type :=
  Lp ℂ (2 : ℝ≥0∞) (volume.restrict K)

/-- Every admissible probe is square-integrable for every restricted locally finite
measure; compact support supplies the integrability. -/
theorem zetaAdmissible_memLp_compactSupportHilbert
    (K : Set ℝ) (f : ZetaAdmissibleFunction) :
    Memℒp f (2 : ℝ≥0∞) (volume.restrict K) := by
  exact
    f.toZetaTestFunction.continuous.memℒp_of_hasCompactSupport
      f.toZetaTestFunction.hasCompactSupport

/-- The canonical admissible-probe representative in a compact-support Hilbert fiber. -/
def toZetaCompactSupportHilbert
    (K : Set ℝ) (f : ZetaAdmissibleFunction) :
    zetaCompactSupportHilbert K :=
  Memℒp.toLp f (zetaAdmissible_memLp_compactSupportHilbert K f)

/-- The Hilbert representative agrees almost everywhere with the original admissible
probe on the prescribed support fiber. -/
theorem coeFn_toZetaCompactSupportHilbert
    (K : Set ℝ) (f : ZetaAdmissibleFunction) :
    toZetaCompactSupportHilbert K f =ᵐ[volume.restrict K] f := by
  exact
    Memℒp.coeFn_toLp
      (zetaAdmissible_memLp_compactSupportHilbert K f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
