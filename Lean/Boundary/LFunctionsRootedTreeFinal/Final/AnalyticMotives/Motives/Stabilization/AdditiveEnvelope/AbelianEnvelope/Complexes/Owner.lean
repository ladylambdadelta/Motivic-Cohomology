import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Owner

/-!
# Complexes in the abelian envelope of the analytic additive category

This file owns the abelian cochain-complex category used for exact truncation
arguments.  The concrete analytic additive complexes embed into this category
through the Q-linear Yoneda embedding degreewise.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Integer cochain complexes in the abelian envelope of the analytic additive
category. -/
abbrev TraceAnalyticAbelianCochainComplex :=
  CochainComplex TraceAnalyticAdditiveAbelianEnvelope ℤ

/-- The category of abelian-envelope analytic cochain complexes. -/
def TraceAnalyticAbelianCochainComplex.categoryStructure :
    Category TraceAnalyticAbelianCochainComplex :=
  inferInstance

/-- The abelian-envelope cochain-complex category is abelian, pointwise in the
abelian envelope. -/
def TraceAnalyticAbelianCochainComplex.abelianStructure :
    Abelian TraceAnalyticAbelianCochainComplex :=
  inferInstance

/-- The abelian-envelope cochain-complex category has homology. -/
def TraceAnalyticAbelianCochainComplex.categoryWithHomologyStructure :
    CategoryWithHomology TraceAnalyticAbelianCochainComplex :=
  inferInstance

/-- Object evaluation in an abelian-envelope cochain complex. -/
def TraceAnalyticAbelianCochainComplex.objectAt
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ) :
    TraceAnalyticAdditiveAbelianEnvelope :=
  complex.X degree

/-- Differentials in abelian-envelope analytic cochain complexes. -/
def TraceAnalyticAbelianCochainComplex.differential
    (complex : TraceAnalyticAbelianCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.objectAt sourceDegree ⟶ complex.objectAt targetDegree :=
  complex.d sourceDegree targetDegree

/-- Abelian-envelope analytic differentials square to zero. -/
theorem TraceAnalyticAbelianCochainComplex.differential_comp_differential
    (complex : TraceAnalyticAbelianCochainComplex)
    (first second third : ℤ) :
    complex.differential first second ≫
        complex.differential second third =
      0 :=
  HomologicalComplex.d_comp_d complex first second third

end AnalyticMotives
end LFunctions
end Boundary
