import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Owner

/-!
# Monotonicity of analytic motivic aisles and coaisles

This file proves the first closure facts for the concrete analytic motivic
aisle and coaisle predicates: enlarging the aisle cut preserves aisle
membership, and lowering the coaisle cut preserves coaisle membership.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Aisle membership is monotone in the cut. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_mono
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.aisleLE lower object) :
    TraceAnalyticMotivicTStructure.aisleLE upper object :=
  match membership with
  | Exists.intro bound boundMembership =>
      match boundMembership with
      | Exists.intro complex complexMembership =>
          match complexMembership with
          | Exists.intro degree degreeMembership =>
              Exists.intro
                bound
                (Exists.intro
                  complex
                  (Exists.intro
                    degree
                    (And.intro
                      (le_trans degreeMembership.1 cut_le)
                      degreeMembership.2)))

/-- Coaisle membership is monotone contravariantly in the cut. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_mono
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGE upper object) :
    TraceAnalyticMotivicTStructure.coaisleGE lower object :=
  match membership with
  | Exists.intro bound boundMembership =>
      match boundMembership with
      | Exists.intro complex complexMembership =>
          match complexMembership with
          | Exists.intro degree degreeMembership =>
              Exists.intro
                bound
                (Exists.intro
                  complex
                  (Exists.intro
                    degree
                    (And.intro
                      (le_trans cut_le degreeMembership.1)
                      degreeMembership.2)))

/-- The aisle at a cut is contained in the same aisle at that cut. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_mono_refl
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.aisleLE cut object) :
    TraceAnalyticMotivicTStructure.aisleLE cut object :=
  TraceAnalyticMotivicTStructure.aisleLE_mono
    (le_rfl)
    membership

/-- The coaisle at a cut is contained in the same coaisle at that cut. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_mono_refl
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGE cut object) :
    TraceAnalyticMotivicTStructure.coaisleGE cut object :=
  TraceAnalyticMotivicTStructure.coaisleGE_mono
    (le_rfl)
    membership

end AnalyticMotives
end LFunctions
end Boundary
