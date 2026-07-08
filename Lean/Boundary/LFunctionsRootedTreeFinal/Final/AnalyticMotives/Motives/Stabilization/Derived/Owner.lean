import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Owner

/-!
# Derived stabilization of the analytic abelian envelope

This file anchors the quasi-isomorphism localization used by the truncation
calculus.  The category is Mathlib's derived category of the concrete
abelian-envelope category of analytic additive trace objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The standard Mathlib derived-category localization exists for the analytic
abelian envelope. -/
def TraceAnalyticDerivedMotiveCategory.hasDerivedCategory :
    HasDerivedCategory TraceAnalyticAdditiveAbelianEnvelope :=
  HasDerivedCategory.standard TraceAnalyticAdditiveAbelianEnvelope

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The derived stabilization of analytic motives: cochain complexes in the
analytic abelian envelope localized at quasi-isomorphisms. -/
abbrev TraceAnalyticDerivedMotiveCategory :=
  DerivedCategory TraceAnalyticAdditiveAbelianEnvelope

/-- The derived localization functor from analytic abelian-envelope cochain
complexes. -/
def TraceAnalyticDerivedMotiveCategory.localizationFunctor :
    TraceAnalyticAbelianCochainComplex ⥤
      TraceAnalyticDerivedMotiveCategory :=
  DerivedCategory.Q

/-- The derived motive represented by an analytic abelian-envelope cochain
complex. -/
def TraceAnalyticDerivedMotiveCategory.objectOf
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj complex

/-- The derived morphism represented by a cochain map in the analytic abelian
envelope. -/
def TraceAnalyticDerivedMotiveCategory.mapOf
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticDerivedMotiveCategory.objectOf source ⟶
      TraceAnalyticDerivedMotiveCategory.objectOf target :=
  TraceAnalyticDerivedMotiveCategory.localizationFunctor.map hom

/-- The localization functor is Mathlib's derived-category quotient functor. -/
theorem TraceAnalyticDerivedMotiveCategory.localizationFunctor_eq :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor =
      DerivedCategory.Q :=
  rfl

/-- The object map is the object part of the derived localization functor. -/
theorem TraceAnalyticDerivedMotiveCategory.objectOf_eq
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticDerivedMotiveCategory.objectOf complex =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.obj complex :=
  rfl

/-- The morphism map is the morphism part of the derived localization functor. -/
theorem TraceAnalyticDerivedMotiveCategory.mapOf_eq
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticDerivedMotiveCategory.mapOf hom =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map hom :=
  rfl

/-- A quasi-isomorphism of analytic abelian-envelope complexes becomes an
isomorphism in the derived analytic motive category. -/
theorem TraceAnalyticDerivedMotiveCategory.mapOf_isIso_of_quasiIso
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target)
    [QuasiIso hom] :
    IsIso (TraceAnalyticDerivedMotiveCategory.mapOf hom) :=
  let qiso : QuasiIso hom := ‹QuasiIso hom›
  CategoryTheory.Localization.inverts
    DerivedCategory.Q
    (HomologicalComplex.quasiIso
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ))
    hom
    qiso

/-- Stable derived analytic motives inherit integer shifts from Mathlib's
derived category. -/
def TraceAnalyticDerivedMotiveCategory.hasShiftStructure :
    CategoryTheory.HasShift TraceAnalyticDerivedMotiveCategory ℤ :=
  inferInstance

/-- Stable derived analytic motives inherit a pretriangulated structure from
Mathlib's derived category. -/
def TraceAnalyticDerivedMotiveCategory.pretriangulatedStructure :
    CategoryTheory.Pretriangulated TraceAnalyticDerivedMotiveCategory :=
  inferInstance

/-- Stable derived analytic motives inherit a triangulated structure from
Mathlib's derived category. -/
def TraceAnalyticDerivedMotiveCategory.triangulatedStructure :
    CategoryTheory.IsTriangulated TraceAnalyticDerivedMotiveCategory :=
  inferInstance

end AnalyticMotives
end LFunctions
end Boundary
