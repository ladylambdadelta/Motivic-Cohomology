import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.CategoryInput.Operations.Owner

/-!
# Pointwise extensionality for linear presheaf homs

This owner defines the pointwise equality relation on public linear presheaf
homs and proves that it is an equivalence relation compatible with
composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQLinearPresheafHom

/-- Pointwise equality of linear presheaf homs. -/
def PointwiseEq {F G : ContourCorQLinearPresheafObject}
    (η θ : ContourCorQLinearPresheafHom F G) : Prop :=
  (X : ContourCorQPresheafObject) →
    (a : F.valueAt X) →
      η.componentAt X a = θ.componentAt X a

/-- Pointwise equality is reflexive. -/
theorem pointwiseEq_refl {F G : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G) :
    PointwiseEq η η :=
  fun _ _ => rfl

/-- Pointwise equality is symmetric. -/
theorem pointwiseEq_symm {F G : ContourCorQLinearPresheafObject}
    {η θ : ContourCorQLinearPresheafHom F G}
    (h : PointwiseEq η θ) :
    PointwiseEq θ η :=
  fun X a => Eq.symm (h X a)

/-- Pointwise equality is transitive. -/
theorem pointwiseEq_trans {F G : ContourCorQLinearPresheafObject}
    {η θ κ : ContourCorQLinearPresheafHom F G}
    (hηθ : PointwiseEq η θ)
    (hθκ : PointwiseEq θ κ) :
    PointwiseEq η κ :=
  fun X a => Eq.trans (hηθ X a) (hθκ X a)

/-- Left composition respects pointwise equality. -/
theorem pointwiseEq_comp_left
    {F G H : ContourCorQLinearPresheafObject}
    {η θ : ContourCorQLinearPresheafHom F G}
    (h : PointwiseEq η θ)
    (κ : ContourCorQLinearPresheafHom G H) :
    PointwiseEq
      (ContourCorQLinearPresheafHom.comp η κ)
      (ContourCorQLinearPresheafHom.comp θ κ) :=
  fun X a =>
    congrArg (κ.componentAt X) (h X a)

/-- Right composition respects pointwise equality. -/
theorem pointwiseEq_comp_right
    {F G H : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    {θ κ : ContourCorQLinearPresheafHom G H}
    (h : PointwiseEq θ κ) :
    PointwiseEq
      (ContourCorQLinearPresheafHom.comp η θ)
      (ContourCorQLinearPresheafHom.comp η κ) :=
  fun X a =>
    h X (η.componentAt X a)

/-- Composition respects pointwise equality in both variables. -/
theorem pointwiseEq_comp
    {F G H : ContourCorQLinearPresheafObject}
    {η₁ η₂ : ContourCorQLinearPresheafHom F G}
    {θ₁ θ₂ : ContourCorQLinearPresheafHom G H}
    (hη : PointwiseEq η₁ η₂)
    (hθ : PointwiseEq θ₁ θ₂) :
    PointwiseEq
      (ContourCorQLinearPresheafHom.comp η₁ θ₁)
      (ContourCorQLinearPresheafHom.comp η₂ θ₂) :=
  pointwiseEq_trans
    (pointwiseEq_comp_left hη θ₁)
    (pointwiseEq_comp_right η₂ hθ)

end ContourCorQLinearPresheafHom

end AnalyticMotives
end LFunctions
end Boundary
