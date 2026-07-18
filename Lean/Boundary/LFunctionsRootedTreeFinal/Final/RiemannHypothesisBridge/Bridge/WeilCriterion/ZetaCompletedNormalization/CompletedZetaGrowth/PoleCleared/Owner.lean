import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part05_NonCircularAssembly

/-!
# Pole-cleared zeta growth owner
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Unconditional pole-cleared zero-one strip canonical self-reflected vertical tail envelope.

This theorem is the genuine analytical leaf.  It first proves ordinary growth
without a bootstrap assumption by splitting at `Re z = 1/2`: direct
Euler--Maclaurin on the positive half and one functional-equation transport on
the left half.

The proof uses:
- direct Euler--Maclaurin growth on `1/2 ≤ Re z ≤ 1`;
- the completed functional equation and Gamma/Stirling multiplier on the left;
- compact-height patching;
- explicit reflection transport. -/
theorem poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner :
    PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope := by
  exact poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_nonCircular

end
end LFunctions
end Boundary
