import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Owner

/-!
# Monotonicity of derived analytic homological bounds

This file proves the nesting laws for the concrete homology-vanishing
predicates that underlie the analytic derived t-structure.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The `≤ cut` homological bound is covariant in the cut: increasing the cut
weakens the vanishing requirement. -/
theorem homologicalLE_mono
    {lowerCut upperCut : ℤ}
    (hcut : lowerCut ≤ upperCut)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hobject :
      TraceAnalyticDerivedMotiveCategory.HomologicalLE lowerCut object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE upperCut object :=
  fun degree hdegree =>
    hobject degree (lt_of_le_of_lt hcut hdegree)

/-- The `≥ cut` homological bound is contravariant in the cut: decreasing the
cut weakens the vanishing requirement. -/
theorem homologicalGE_antitone
    {lowerCut upperCut : ℤ}
    (hcut : lowerCut ≤ upperCut)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hobject :
      TraceAnalyticDerivedMotiveCategory.HomologicalGE upperCut object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE lowerCut object :=
  fun degree hdegree =>
    hobject degree (lt_of_lt_of_le hdegree hcut)

/-- An object bounded between `lowerCut` and `upperCut` is also bounded between
any narrower pair of cuts whose lower edge moves down and upper edge moves up. -/
theorem homological_window_mono
    {sourceLower targetLower sourceUpper targetUpper : ℤ}
    (hlower : targetLower ≤ sourceLower)
    (hupper : sourceUpper ≤ targetUpper)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hle :
      TraceAnalyticDerivedMotiveCategory.HomologicalLE sourceUpper object)
    (hge :
      TraceAnalyticDerivedMotiveCategory.HomologicalGE sourceLower object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE targetUpper object ∧
      TraceAnalyticDerivedMotiveCategory.HomologicalGE targetLower object :=
  ⟨TraceAnalyticDerivedMotiveCategory.homologicalLE_mono
      hupper
      object
      hle,
    TraceAnalyticDerivedMotiveCategory.homologicalGE_antitone
      hlower
      object
      hge⟩

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
