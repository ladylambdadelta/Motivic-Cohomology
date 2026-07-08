import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Boundary.Owner

/-!
# Cokernel property of the boundary opcycles projection

At the boundary degree of an upper truncation, the projection component is
`pOpcycles`.  This file records the owner-level cokernel theorem: `pOpcycles`
is the cokernel of the incoming cochain differential.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- A cokernel projection remains a cokernel projection after postcomposition
with an isomorphism of its target. -/
theorem cokernelCofork_isColimit_comp_iso
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    {source middle cokernelTarget transportedTarget : C}
    (incoming : source ⟶ middle)
    (projection : middle ⟶ cokernelTarget)
    (projection_zero : incoming ≫ projection = 0)
    (targetIso : cokernelTarget ≅ transportedTarget)
    (projection_isCokernel :
      IsColimit
        (CokernelCofork.ofπ
          projection
          projection_zero)) :
    IsColimit
      (CokernelCofork.ofπ
        (projection ≫ targetIso.hom)
        (Eq.trans
          (Category.assoc incoming projection targetIso.hom)
          (Eq.trans
            (congrArg
              (fun morphism => morphism ≫ targetIso.hom)
              projection_zero)
            (zero_comp targetIso.hom)))) :=
  IsColimit.ofIsoColimit
    projection_isCokernel
    (Cofork.ext targetIso rfl)

/-- For an analytic cochain complex, the boundary opcycles projection at
`cut` is the cokernel of the incoming differential from `cut - 1`. -/
theorem additiveOpcyclesBoundaryProjection_isCokernel_incoming
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    IsColimit
      (CokernelCofork.ofπ
        (complex.pOpcycles cut)
        (complex.d_pOpcycles (cut - 1) cut)) :=
  complex.opcyclesIsCokernel
    (i := cut - 1)
    (j := cut)
    (CochainComplex.prev ℤ cut)

/-- The boundary component of the full upper projection map is a cokernel of
the incoming differential after transporting the opcycles cokernel along
Mathlib's extended boundary truncation isomorphism. -/
theorem additiveTruncGEProjectionBoundaryComponent_isCokernel_incoming
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    IsColimit
      (CokernelCofork.ofπ
        (complex.pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            hdegree
            hboundary).inv)
        (Eq.trans
          (Category.assoc
            (complex.d (cut - 1) cut)
            (complex.pOpcycles cut)
            ((_root_.HomologicalComplex.truncGEXIsoOpcycles
              complex
              (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
              hdegree
              hboundary).inv))
          (Eq.trans
            (congrArg
              (fun morphism =>
                morphism ≫
                  (_root_.HomologicalComplex.truncGEXIsoOpcycles
                    complex
                    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                    hdegree
                    hboundary).inv)
              (complex.d_pOpcycles (cut - 1) cut))
            (zero_comp
              ((_root_.HomologicalComplex.truncGEXIsoOpcycles
                complex
                (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                hdegree
                hboundary).inv))))) :=
  TraceAnalyticMotivicTStructure.cokernelCofork_isColimit_comp_iso
    (complex.d (cut - 1) cut)
    (complex.pOpcycles cut)
    (complex.d_pOpcycles (cut - 1) cut)
    ((_root_.HomologicalComplex.truncGEXIsoOpcycles
      complex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      hdegree
      hboundary).symm)
    (TraceAnalyticMotivicTStructure
      .additiveOpcyclesBoundaryProjection_isCokernel_incoming
        cut
        complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
