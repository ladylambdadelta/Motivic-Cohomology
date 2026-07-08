import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Exactness.Comparison.Transport.Owner

/-!
# Contravariant exactness transport to the explicit truncation short complex

This file transports contravariant Yoneda exactness from the opposite of the
canonical distinguished short complex to the opposite of the explicit
hand-built chosen truncation short complex.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The opposite canonical distinguished short complex is isomorphic to the
opposite explicit chosen truncation short complex. -/
def distinguishedShortComplexOpIsoShortComplexOp
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplex.op ≅
      representative.shortComplex.op :=
  ShortComplex.isoMk
    (Iso.refl _)
    (Iso.refl _)
    (Iso.refl _)
    (Eq.trans
      (Category.id_comp representative.shortComplex.op.f)
      (Eq.trans
        (congrArg Quiver.Hom.op representative.shortComplex_g)
        (Eq.trans
          (Eq.symm
            (congrArg Quiver.Hom.op
              representative.distinguishedShortComplex_g))
          (Eq.symm
            (Category.comp_id
              representative.distinguishedShortComplex.op.f)))))
    (Eq.trans
      (Category.id_comp representative.shortComplex.op.g)
      (Eq.trans
        (congrArg Quiver.Hom.op representative.shortComplex_f)
        (Eq.trans
          (Eq.symm
            (congrArg Quiver.Hom.op
              representative.distinguishedShortComplex_f))
          (Eq.symm
            (Category.comp_id
              representative.distinguishedShortComplex.op.g)))))

/-- The first component of the opposite short-complex comparison is the
identity. -/
theorem distinguishedShortComplexOpIsoShortComplexOp_hom_τ₁
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplexOpIsoShortComplexOp.hom.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the opposite short-complex comparison is the
identity. -/
theorem distinguishedShortComplexOpIsoShortComplexOp_hom_τ₂
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplexOpIsoShortComplexOp.hom.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the opposite short-complex comparison is the
identity. -/
theorem distinguishedShortComplexOpIsoShortComplexOp_hom_τ₃
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplexOpIsoShortComplexOp.hom.τ₃ =
      𝟙 _ :=
  rfl

/-- Contravariant preadditive Yoneda exactness for the explicit chosen
truncation short complex, transported from the canonical distinguished short
complex. -/
theorem yonedaShortComplex_exact
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (probe : TraceAnalyticDerivedMotiveCategory) :
    (representative.shortComplex.op.map
      (preadditiveYoneda.obj probe)).Exact :=
  ShortComplex.exact_of_iso
    ((preadditiveYoneda.obj probe).mapShortComplex.mapIso
      representative.distinguishedShortComplexOpIsoShortComplexOp)
    (representative.yonedaDistinguishedShortComplex_exact probe)

/-- Contravariant preadditive Yoneda exactness for the normalized adjacent
cut-`1` explicit chosen truncation short complex. -/
theorem normalized_yonedaShortComplex_exact
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (probe : TraceAnalyticDerivedMotiveCategory) :
    (representative.shortComplex.op.map
      (preadditiveYoneda.obj probe)).Exact :=
  representative.yonedaShortComplex_exact probe

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
