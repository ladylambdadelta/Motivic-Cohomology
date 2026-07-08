import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Owner

/-!
# Abelian envelope of the analytic additive category

The finite matrix additive hull of trace correspondences is the concrete
analytic source category.  Exactness for truncation sequences is owned by its
Q-linear presheaf envelope, where kernels, cokernels, and homology are computed
pointwise in `ModuleCat Rat`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The Q-linear presheaf abelian envelope of the analytic additive category. -/
abbrev TraceAnalyticAdditiveAbelianEnvelope :=
  (Opposite TraceAnalyticAdditiveCategoryObject) ⥤ ModuleCat Rat

/-- The abelian-envelope category structure is the functor-category structure. -/
def TraceAnalyticAdditiveAbelianEnvelope.categoryStructure :
    Category TraceAnalyticAdditiveAbelianEnvelope :=
  inferInstance

/-- The abelian-envelope preadditive structure is inherited pointwise from
`ModuleCat Rat`. -/
def TraceAnalyticAdditiveAbelianEnvelope.preadditiveStructure :
    Preadditive TraceAnalyticAdditiveAbelianEnvelope :=
  inferInstance

/-- The abelian-envelope rational linear structure is inherited pointwise from
`ModuleCat Rat`. -/
def TraceAnalyticAdditiveAbelianEnvelope.linearRatStructure :
    Linear Rat TraceAnalyticAdditiveAbelianEnvelope :=
  inferInstance

/-- The abelian-envelope abelian structure is Mathlib's pointwise abelian
structure on functor categories. -/
def TraceAnalyticAdditiveAbelianEnvelope.abelianStructure :
    Abelian TraceAnalyticAdditiveAbelianEnvelope :=
  inferInstance

/-- Short-complex homology exists in the abelian envelope because the envelope
is abelian. -/
def TraceAnalyticAdditiveAbelianEnvelope.categoryWithHomologyStructure :
    CategoryWithHomology TraceAnalyticAdditiveAbelianEnvelope :=
  inferInstance

/-- Evaluation of an abelian-envelope presheaf at one additive analytic object. -/
def TraceAnalyticAdditiveAbelianEnvelope.evaluation
    (object : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveAbelianEnvelope ⥤ ModuleCat Rat :=
  (CategoryTheory.evaluation
    (Opposite TraceAnalyticAdditiveCategoryObject)
    (ModuleCat Rat)).obj
      (Opposite.op object)

/-- Evaluation sends an abelian-envelope presheaf to its value at the opposite
analytic additive object. -/
theorem TraceAnalyticAdditiveAbelianEnvelope.evaluation_obj
    (object : TraceAnalyticAdditiveCategoryObject)
    (presheaf : TraceAnalyticAdditiveAbelianEnvelope) :
    (TraceAnalyticAdditiveAbelianEnvelope.evaluation object).obj presheaf =
      presheaf.obj (Opposite.op object) :=
  rfl

/-- The fully faithful Q-linear Yoneda embedding of the concrete analytic
additive category into its abelian envelope. -/
def TraceAnalyticAdditiveAbelianEnvelope.yoneda :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticAdditiveAbelianEnvelope :=
  CategoryTheory.linearYoneda Rat TraceAnalyticAdditiveCategoryObject

/-- Yoneda sends an additive analytic object to its represented Q-linear
presheaf. -/
theorem TraceAnalyticAdditiveAbelianEnvelope.yoneda_obj
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object =
      (CategoryTheory.linearYoneda Rat
        TraceAnalyticAdditiveCategoryObject).obj object :=
  rfl

/-- Evaluating the represented presheaf at a probe recovers the Q-module of
analytic additive morphisms from the probe to the represented object. -/
theorem TraceAnalyticAdditiveAbelianEnvelope.yoneda_obj_obj
    (probe object : TraceAnalyticAdditiveCategoryObject) :
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object).obj
        (Opposite.op probe) =
      ModuleCat.of Rat (probe ⟶ object) :=
  rfl

/-- The analytic Yoneda embedding into the abelian envelope is full. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaFull :
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).Full :=
  inferInstance

/-- The analytic Yoneda embedding into the abelian envelope is faithful. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaFaithful :
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).Faithful :=
  inferInstance

/-- The analytic Yoneda embedding into the abelian envelope is fully faithful. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaFullyFaithful :
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).FullyFaithful :=
  Functor.ofFullyFaithful

end AnalyticMotives
end LFunctions
end Boundary
