import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.FormalSums.Owner

/-!
# Typed identity laws for trace-correspondence homs

This file owns the left and right identity laws in the typed hom quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The ambient class of a representative is the raw formal-sum class of its terms. -/
theorem TraceCorQHomRepresentative.ambientClass_eq_ofFormalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.ambientClass =
      TraceCorQQuotient.ofFormalSum representative.formalSum.raw :=
  TraceCorQQuotient.ofCandidate_eq_ofFormalSum representative.rawCandidate

/-- Left identity for typed trace-correspondence homs. -/
theorem TraceCorQHom.left_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.id source)
      hom =
      hom :=
  TraceCorQHom.eq_of_ambient_eq
    (Quotient.inductionOn
      hom
      (fun representative =>
        Eq.trans
          (TraceCorQHom.ambient_comp
            (TraceCorQHom.id source)
            (TraceCorQHom.ofRepresentative representative))
          (Eq.trans
            (congrArg
              (fun rightClass =>
                TraceCorQQuotient.comp
                  (TraceCorQHom.ambient (TraceCorQHom.id source))
                  rightClass)
              (TraceCorQHomRepresentative.ambientClass_eq_ofFormalSum
                representative))
            (Eq.trans
              (Eq.symm
                (TraceCorQHom.ambient_comp
                  (TraceCorQHom.id source)
                  (TraceCorQHom.ofFormalSum representative.formalSum)))
              (Eq.trans
                (TraceCorQHom.ambient_left_id_ofFormalSum
                  representative.formalSum)
                (Eq.symm
                  (TraceCorQHomRepresentative.ambientClass_eq_ofFormalSum
                    representative)))))))

/-- Right identity for typed trace-correspondence homs. -/
theorem TraceCorQHom.right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      hom
      (TraceCorQHom.id target) =
      hom :=
  TraceCorQHom.eq_of_ambient_eq
    (Quotient.inductionOn
      hom
      (fun representative =>
        Eq.trans
          (TraceCorQHom.ambient_comp
            (TraceCorQHom.ofRepresentative representative)
            (TraceCorQHom.id target))
          (Eq.trans
            (congrArg
              (fun leftClass =>
                TraceCorQQuotient.comp
                  leftClass
                  (TraceCorQHom.ambient (TraceCorQHom.id target)))
              (TraceCorQHomRepresentative.ambientClass_eq_ofFormalSum
                representative))
            (Eq.trans
              (Eq.symm
                (TraceCorQHom.ambient_comp
                  (TraceCorQHom.ofFormalSum representative.formalSum)
                  (TraceCorQHom.id target)))
              (Eq.trans
                (TraceCorQHom.ambient_right_id_ofFormalSum
                  representative.formalSum)
                (Eq.symm
                  (TraceCorQHomRepresentative.ambientClass_eq_ofFormalSum
                    representative)))))))

end AnalyticMotives
end LFunctions
end Boundary
