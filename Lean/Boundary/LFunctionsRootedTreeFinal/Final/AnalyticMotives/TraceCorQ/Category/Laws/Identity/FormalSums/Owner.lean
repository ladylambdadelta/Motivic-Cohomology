import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner

/-!
# Formal-sum identity laws for typed trace-correspondence homs

This file lifts singleton identity laws to finite typed formal sums after
forgetting to the ambient quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left identity holds for a typed formal sum after forgetting to the ambient quotient. -/
theorem TraceCorQHom.ambient_left_id_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.ofFormalSum formalSum)) =
      TraceCorQHom.ambient
        (TraceCorQHom.ofFormalSum formalSum) :=
  match formalSum with
  | [] =>
      Eq.trans
        (TraceCorQHom.ambient_comp
          (TraceCorQHom.id source)
          (TraceCorQHom.ofFormalSum
            (TraceCorQHomFormalSum.zero source target)))
        (Eq.trans
          (congrArg
            (fun leftClass =>
              TraceCorQQuotient.comp
                leftClass
                (TraceCorQHom.ambient
                  (TraceCorQHom.ofFormalSum
                    (TraceCorQHomFormalSum.zero source target))))
            (TraceCorQHom.ambient_id source))
          (Eq.trans
            (congrArg
              (fun rightClass =>
                TraceCorQQuotient.comp
                  (TraceCorQQuotient.singleton
                    1
                    (TraceCorQGenerator.id source))
                  rightClass)
              (TraceCorQHom.ambient_zero source target))
            (Eq.trans
              (TraceCorQQuotient.comp_zero
                (TraceCorQQuotient.singleton
                  1
                  (TraceCorQGenerator.id source)))
              (Eq.symm
                (TraceCorQHom.ambient_zero source target)))))
  | term :: tail =>
      Eq.trans
        (congrArg
          (fun rightHom =>
            TraceCorQHom.ambient
              (TraceCorQHom.comp
                (TraceCorQHom.id source)
                rightHom))
          (TraceCorQHom.ofFormalSum_cons term tail))
        (Eq.trans
          (TraceCorQHom.ambient_comp
            (TraceCorQHom.id source)
            (TraceCorQHom.add
              (TraceCorQHom.singleton
                source
                target
                term.coefficient
                term.generator
                (TraceCorQHomTerm.generator_source term)
                (TraceCorQHomTerm.generator_target term))
              (TraceCorQHom.ofFormalSum tail)))
          (Eq.trans
            (congrArg
              (fun leftClass =>
                TraceCorQQuotient.comp
                  leftClass
                  (TraceCorQHom.ambient
                    (TraceCorQHom.add
                      (TraceCorQHom.singleton
                        source
                        target
                        term.coefficient
                        term.generator
                        (TraceCorQHomTerm.generator_source term)
                        (TraceCorQHomTerm.generator_target term))
                      (TraceCorQHom.ofFormalSum tail))))
              (TraceCorQHom.ambient_id source))
            (Eq.trans
              (congrArg
                (fun rightClass =>
                  TraceCorQQuotient.comp
                    (TraceCorQQuotient.singleton
                      1
                      (TraceCorQGenerator.id source))
                    rightClass)
                (TraceCorQHom.ambient_add
                  (TraceCorQHom.singleton
                    source
                    target
                    term.coefficient
                    term.generator
                    (TraceCorQHomTerm.generator_source term)
                    (TraceCorQHomTerm.generator_target term))
                  (TraceCorQHom.ofFormalSum tail)))
              (Eq.trans
                (TraceCorQQuotient.comp_add
                  (TraceCorQQuotient.singleton
                    1
                    (TraceCorQGenerator.id source))
                  (TraceCorQHom.ambient
                    (TraceCorQHom.singleton
                      source
                      target
                      term.coefficient
                      term.generator
                      (TraceCorQHomTerm.generator_source term)
                      (TraceCorQHomTerm.generator_target term)))
                  (TraceCorQHom.ambient
                    (TraceCorQHom.ofFormalSum tail)))
                (Eq.trans
                  (congrArg
                    (fun headClass =>
                      TraceCorQQuotient.add
                        headClass
                        (TraceCorQQuotient.comp
                          (TraceCorQQuotient.singleton
                            1
                            (TraceCorQGenerator.id source))
                          (TraceCorQHom.ambient
                            (TraceCorQHom.ofFormalSum tail))))
                    (TraceCorQHom.ambient_left_id_singleton
                      source
                      target
                      term.coefficient
                      term.generator
                      (TraceCorQHomTerm.generator_source term)
                      (TraceCorQHomTerm.generator_target term)))
                  (Eq.trans
                    (congrArg
                      (fun tailClass =>
                        TraceCorQQuotient.add
                          (TraceCorQHom.ambient
                            (TraceCorQHom.singleton
                              source
                              target
                              term.coefficient
                              term.generator
                              (TraceCorQHomTerm.generator_source term)
                              (TraceCorQHomTerm.generator_target term)))
                          tailClass)
                      (TraceCorQHom.ambient_left_id_ofFormalSum tail))
                    (Eq.trans
                      (Eq.symm
                        (TraceCorQHom.ambient_add
                          (TraceCorQHom.singleton
                            source
                            target
                            term.coefficient
                            term.generator
                            (TraceCorQHomTerm.generator_source term)
                            (TraceCorQHomTerm.generator_target term))
                          (TraceCorQHom.ofFormalSum tail)))
                      (Eq.trans
                        (congrArg
                          TraceCorQHom.ambient
                          (Eq.symm
                            (TraceCorQHom.ofFormalSum_cons term tail)))
                        rfl)))))))

/-- Right identity holds for a typed formal sum after forgetting to the ambient quotient. -/
theorem TraceCorQHom.ambient_right_id_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.ofFormalSum formalSum)
        (TraceCorQHom.id target)) =
      TraceCorQHom.ambient
        (TraceCorQHom.ofFormalSum formalSum) :=
  match formalSum with
  | [] =>
      Eq.trans
        (TraceCorQHom.ambient_comp
          (TraceCorQHom.ofFormalSum
            (TraceCorQHomFormalSum.zero source target))
          (TraceCorQHom.id target))
        (Eq.trans
          (congrArg
            (fun leftClass =>
              TraceCorQQuotient.comp
                leftClass
                (TraceCorQHom.ambient (TraceCorQHom.id target)))
            (TraceCorQHom.ambient_zero source target))
          (Eq.trans
            (TraceCorQQuotient.zero_comp
              (TraceCorQHom.ambient (TraceCorQHom.id target)))
            (Eq.symm
              (TraceCorQHom.ambient_zero source target))))
  | term :: tail =>
      Eq.trans
        (congrArg
          (fun leftHom =>
            TraceCorQHom.ambient
              (TraceCorQHom.comp
                leftHom
                (TraceCorQHom.id target)))
          (TraceCorQHom.ofFormalSum_cons term tail))
        (Eq.trans
          (TraceCorQHom.ambient_comp
            (TraceCorQHom.add
              (TraceCorQHom.singleton
                source
                target
                term.coefficient
                term.generator
                (TraceCorQHomTerm.generator_source term)
                (TraceCorQHomTerm.generator_target term))
              (TraceCorQHom.ofFormalSum tail))
            (TraceCorQHom.id target))
          (Eq.trans
            (congrArg
              (fun leftClass =>
                TraceCorQQuotient.comp
                  leftClass
                  (TraceCorQHom.ambient (TraceCorQHom.id target)))
              (TraceCorQHom.ambient_add
                (TraceCorQHom.singleton
                  source
                  target
                  term.coefficient
                  term.generator
                  (TraceCorQHomTerm.generator_source term)
                  (TraceCorQHomTerm.generator_target term))
                (TraceCorQHom.ofFormalSum tail)))
            (Eq.trans
              (congrArg
                (fun rightClass =>
                  TraceCorQQuotient.comp
                    (TraceCorQQuotient.add
                      (TraceCorQHom.ambient
                        (TraceCorQHom.singleton
                          source
                          target
                          term.coefficient
                          term.generator
                          (TraceCorQHomTerm.generator_source term)
                          (TraceCorQHomTerm.generator_target term)))
                      (TraceCorQHom.ambient
                        (TraceCorQHom.ofFormalSum tail)))
                    rightClass)
                (TraceCorQHom.ambient_id target))
              (Eq.trans
                (TraceCorQQuotient.add_comp
                  (TraceCorQHom.ambient
                    (TraceCorQHom.singleton
                      source
                      target
                      term.coefficient
                      term.generator
                      (TraceCorQHomTerm.generator_source term)
                      (TraceCorQHomTerm.generator_target term)))
                  (TraceCorQHom.ambient
                    (TraceCorQHom.ofFormalSum tail))
                  (TraceCorQQuotient.singleton
                    1
                    (TraceCorQGenerator.id target)))
                (Eq.trans
                  (congrArg
                    (fun headClass =>
                      TraceCorQQuotient.add
                        headClass
                        (TraceCorQQuotient.comp
                          (TraceCorQHom.ambient
                            (TraceCorQHom.ofFormalSum tail))
                          (TraceCorQQuotient.singleton
                            1
                            (TraceCorQGenerator.id target))))
                    (TraceCorQHom.ambient_right_id_singleton
                      source
                      target
                      term.coefficient
                      term.generator
                      (TraceCorQHomTerm.generator_source term)
                      (TraceCorQHomTerm.generator_target term)))
                  (Eq.trans
                    (congrArg
                      (fun tailClass =>
                        TraceCorQQuotient.add
                          (TraceCorQHom.ambient
                            (TraceCorQHom.singleton
                              source
                              target
                              term.coefficient
                              term.generator
                              (TraceCorQHomTerm.generator_source term)
                              (TraceCorQHomTerm.generator_target term)))
                          tailClass)
                      (TraceCorQHom.ambient_right_id_ofFormalSum tail))
                    (Eq.trans
                      (Eq.symm
                        (TraceCorQHom.ambient_add
                          (TraceCorQHom.singleton
                            source
                            target
                            term.coefficient
                            term.generator
                            (TraceCorQHomTerm.generator_source term)
                            (TraceCorQHomTerm.generator_target term))
                          (TraceCorQHom.ofFormalSum tail)))
                      (Eq.trans
                        (congrArg
                          TraceCorQHom.ambient
                          (Eq.symm
                            (TraceCorQHom.ofFormalSum_cons term tail)))
                        rfl)))))))

end AnalyticMotives
end LFunctions
end Boundary
