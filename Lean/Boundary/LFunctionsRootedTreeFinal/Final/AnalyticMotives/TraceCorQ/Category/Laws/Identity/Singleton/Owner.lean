import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner

/-!
# Singleton identity laws for typed trace-correspondence homs

This file owns left and right identity laws for typed singleton homs after
forgetting to the ambient quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left identity holds for a typed singleton after forgetting to the ambient quotient. -/
theorem TraceCorQHom.ambient_left_id_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq)) =
      TraceCorQHom.ambient
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  Eq.trans
    (TraceCorQHom.ambient_comp
      (TraceCorQHom.id source)
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq))
    (Eq.trans
      (congrArg
        (fun leftClass =>
          TraceCorQQuotient.comp
            leftClass
            (TraceCorQHom.ambient
              (TraceCorQHom.singleton
                source
                target
                coefficient
                generator
                source_eq
                target_eq)))
        (TraceCorQHom.ambient_id source))
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.singleton
                1
                (TraceCorQGenerator.id source))
              rightClass)
          (TraceCorQHom.ambient_singleton
            source
            target
            coefficient
            generator
            source_eq
            target_eq))
        (Eq.trans
          (TraceCorQQuotient.comp_singleton_eq_composite
            1
            coefficient
            (TraceCorQGenerator.id source)
            generator)
          (Eq.trans
            (congrArg
              (fun scaledCoefficient =>
                TraceCorQQuotient.singleton
                  scaledCoefficient
                  (TraceCorQGenerator.comp
                    (TraceCorQGenerator.id source)
                    generator))
              (one_mul coefficient))
            (Eq.trans
              (TraceCorQQuotient.sound_sameFormalSum
                TraceCorQRelationLedger.empty
                (congrArg
                  (fun object =>
                    TraceCorQFormalSum.singleton
                      coefficient
                      (TraceCorQGenerator.comp
                        (TraceCorQGenerator.id object)
                        generator))
                  (Eq.symm source_eq)))
              (Eq.trans
                (TraceCorQGenerator.leftIdentityWeightedSingletonQuotient_eq
                  coefficient
                  generator)
                (Eq.symm
                  (TraceCorQHom.ambient_singleton
                    source
                    target
                    coefficient
                    generator
                    source_eq
                    target_eq))))))))

/-- Right identity holds for a typed singleton after forgetting to the ambient quotient. -/
theorem TraceCorQHom.ambient_right_id_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq)
        (TraceCorQHom.id target)) =
      TraceCorQHom.ambient
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  Eq.trans
    (TraceCorQHom.ambient_comp
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq)
      (TraceCorQHom.id target))
    (Eq.trans
      (congrArg
        (fun leftClass =>
          TraceCorQQuotient.comp
            leftClass
            (TraceCorQHom.ambient (TraceCorQHom.id target)))
        (TraceCorQHom.ambient_singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq))
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.singleton coefficient generator)
              rightClass)
          (TraceCorQHom.ambient_id target))
        (Eq.trans
          (TraceCorQQuotient.comp_singleton_eq_composite
            coefficient
            1
            generator
            (TraceCorQGenerator.id target))
          (Eq.trans
            (congrArg
              (fun scaledCoefficient =>
                TraceCorQQuotient.singleton
                  scaledCoefficient
                  (TraceCorQGenerator.comp
                    generator
                    (TraceCorQGenerator.id target)))
              (mul_one coefficient))
            (Eq.trans
              (TraceCorQQuotient.sound_sameFormalSum
                TraceCorQRelationLedger.empty
                (congrArg
                  (fun object =>
                    TraceCorQFormalSum.singleton
                      coefficient
                      (TraceCorQGenerator.comp
                        generator
                        (TraceCorQGenerator.id object)))
                  (Eq.symm target_eq)))
              (Eq.trans
                (TraceCorQGenerator.rightIdentityWeightedSingletonQuotient_eq
                  coefficient
                  generator)
                (Eq.symm
                  (TraceCorQHom.ambient_singleton
                    source
                    target
                    coefficient
                    generator
                    source_eq
                    target_eq))))))))

end AnalyticMotives
end LFunctions
end Boundary
