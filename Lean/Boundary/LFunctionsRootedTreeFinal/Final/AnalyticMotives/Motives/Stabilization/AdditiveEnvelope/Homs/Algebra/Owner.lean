import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Identity.Owner

/-!
# Hom algebra in the analytic additive envelope

Fixed-source and fixed-target matrix homs inherit their additive commutative
group and rational module structures entrywise from `TraceCorQHom`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Fixed-endpoint additive-envelope matrix homs form an additive commutative group. -/
def TraceAnalyticAdditiveHom.addCommGroupStructure
    (source target : TraceAnalyticAdditiveObject) :
    AddCommGroup (TraceAnalyticAdditiveHom source target) :=
  inferInstance

/-- Fixed-endpoint additive-envelope matrix homs form a rational module. -/
def TraceAnalyticAdditiveHom.ratModuleStructure
    (source target : TraceAnalyticAdditiveObject) :
    Module Rat (TraceAnalyticAdditiveHom source target) :=
  inferInstance

/-- The standard zero matrix agrees with the additive zero. -/
theorem TraceAnalyticAdditiveHom.zero_eq_zero
    (source target : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom.zero source target =
      0 :=
  rfl

/-- The standard matrix addition agrees with additive-envelope hom addition. -/
theorem TraceAnalyticAdditiveHom.add_eq_add
    {source target : TraceAnalyticAdditiveObject}
    (left right : TraceAnalyticAdditiveHom source target) :
    TraceAnalyticAdditiveHom.add left right =
      left + right :=
  rfl

/-- The standard matrix negation agrees with additive-envelope hom negation. -/
theorem TraceAnalyticAdditiveHom.neg_eq_neg
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target) :
    TraceAnalyticAdditiveHom.neg hom =
      -hom :=
  rfl

/-- The standard matrix scalar action agrees with additive-envelope hom scalar multiplication. -/
theorem TraceAnalyticAdditiveHom.smul_eq_smul
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target) :
    TraceAnalyticAdditiveHom.smul coefficient hom =
      coefficient • hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
