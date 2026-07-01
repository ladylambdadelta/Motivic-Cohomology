import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQConstruction.Laws.Owner

/-!
# Extensionality for constructed `ContourCor_Q` linear presheaves

This owner exposes pointwise equality and its compatibility with composition
for the constructive transfer lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedContourPresheafHom

/-- Pointwise equality of constructed contour presheaf homs. -/
def PointwiseEq {F G : ConstructedContourPresheafObject}
    (η θ : ConstructedContourPresheafHom F G) : Prop :=
  ContourCorQLinearPresheafHom.PointwiseEq η θ

/-- Pointwise equality is reflexive. -/
theorem pointwiseEq_refl {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G) :
    PointwiseEq η η :=
  ContourCorQLinearPresheafHom.pointwiseEq_refl η

/-- Pointwise equality is symmetric. -/
theorem pointwiseEq_symm {F G : ConstructedContourPresheafObject}
    {η θ : ConstructedContourPresheafHom F G}
    (h : PointwiseEq η θ) :
    PointwiseEq θ η :=
  ContourCorQLinearPresheafHom.pointwiseEq_symm h

/-- Pointwise equality is transitive. -/
theorem pointwiseEq_trans {F G : ConstructedContourPresheafObject}
    {η θ κ : ConstructedContourPresheafHom F G}
    (hηθ : PointwiseEq η θ)
    (hθκ : PointwiseEq θ κ) :
    PointwiseEq η κ :=
  ContourCorQLinearPresheafHom.pointwiseEq_trans hηθ hθκ

/-- Composition respects pointwise equality in both variables. -/
theorem pointwiseEq_comp
    {F G H : ConstructedContourPresheafObject}
    {η₁ η₂ : ConstructedContourPresheafHom F G}
    {θ₁ θ₂ : ConstructedContourPresheafHom G H}
    (hη : PointwiseEq η₁ η₂)
    (hθ : PointwiseEq θ₁ θ₂) :
    PointwiseEq (comp η₁ θ₁) (comp η₂ θ₂) :=
  ContourCorQLinearPresheafHom.pointwiseEq_comp hη hθ

end ConstructedContourPresheafHom

end AnalyticMotives
end LFunctions
end Boundary
