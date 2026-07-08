import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Owner

/-!
# Degreewise Yoneda embedding of analytic additive complexes

This file prolongs the fully faithful Q-linear Yoneda embedding of the concrete
analytic additive category to integer cochain complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The degreewise Yoneda functor from concrete analytic additive cochain
complexes to cochain complexes in the abelian envelope. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctor :
    TraceAnalyticAdditiveCochainComplex ⥤
      TraceAnalyticAbelianCochainComplex :=
  (TraceAnalyticAdditiveAbelianEnvelope.yoneda).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The abelian-envelope complex represented by a concrete analytic additive
cochain complex. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAbelianCochainComplex :=
  (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctor).obj
    complex

/-- The abelian-envelope chain map represented by a concrete analytic additive
chain map. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex source ⟶
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex target :=
  (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctor).map hom

/-- Degree objects of a represented complex are represented degree objects. -/
theorem TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex_X
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
      complex).X degree =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X degree) :=
  rfl

/-- Differentials of a represented complex are Yoneda images of the concrete
differentials. -/
theorem TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex_d
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
      complex).d sourceDegree targetDegree =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d sourceDegree targetDegree) :=
  rfl

/-- Degree components of represented chain maps are Yoneda images of concrete
chain-map components. -/
theorem TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap_f
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap hom).f degree =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map (hom.f degree) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
