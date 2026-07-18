import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleDifferentialTransform

/-!
# Finite spectral-zero differential operator

Iterating the first-order operator `D + a` over a finite sample set produces
an admissible probe whose transform vanishes on the entire sample set.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

noncomputable def finiteSpectralZeroLinearMapList
    (samples : List ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] ZetaAdmissibleFunction :=
  samples.foldr
    (fun sample current =>
      current.comp (firstOrderSpectralZeroLinearMap sample))
    LinearMap.id

noncomputable def finiteSpectralZeroOperatorList
    (samples : List ℂ)
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  finiteSpectralZeroLinearMapList samples f

theorem finiteSpectralZeroOperatorList_cons
    (sample : ℂ)
    (samples : List ℂ)
    (f : ZetaAdmissibleFunction) :
    finiteSpectralZeroOperatorList (sample :: samples) f =
      finiteSpectralZeroOperatorList samples
        (firstOrderSpectralZeroOperator sample f) := by
  unfold finiteSpectralZeroOperatorList
  unfold finiteSpectralZeroLinearMapList
  exact Eq.trans
    (LinearMap.comp_apply
      (samples.foldr
        (fun sampleValue current =>
          current.comp (firstOrderSpectralZeroLinearMap sampleValue))
        LinearMap.id)
      (firstOrderSpectralZeroLinearMap sample)
      f)
    (congrArg
      (fun probe : ZetaAdmissibleFunction =>
        (samples.foldr
          (fun sampleValue current =>
            current.comp (firstOrderSpectralZeroLinearMap sampleValue))
          LinearMap.id) probe)
      (firstOrderSpectralZeroLinearMap_apply sample f))

theorem zetaSpectralEval_finiteSpectralZeroOperatorList
    (samples : List ℂ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaSpectralEval (finiteSpectralZeroOperatorList samples f) z =
      (samples.map (fun sample : ℂ => sample - z)).prod *
        zetaSpectralEval f z := by
  induction samples generalizing f with
  | nil =>
      exact Eq.trans
        (Eq.refl (zetaSpectralEval f z))
        (one_mul (zetaSpectralEval f z)).symm
  | cons sample samples hinduction =>
      have htail := hinduction (firstOrderSpectralZeroOperator sample f)
      have hfirst := zetaSpectralEval_firstOrderSpectralZeroOperator sample z f
      exact Eq.trans
        (congrArg
          (fun probe : ZetaAdmissibleFunction => zetaSpectralEval probe z)
          (finiteSpectralZeroOperatorList_cons sample samples f))
        (Eq.trans
          htail
          (Eq.trans
            (congrArg
              (fun value : ℂ =>
                (samples.map (fun nextSample : ℂ => nextSample - z)).prod * value)
              hfirst)
            (calc
            (samples.map (fun nextSample : ℂ => nextSample - z)).prod *
                ((sample - z) * zetaSpectralEval f z) =
                ((samples.map (fun nextSample : ℂ => nextSample - z)).prod *
                  (sample - z)) * zetaSpectralEval f z := by
              exact (mul_assoc
                (samples.map (fun nextSample : ℂ => nextSample - z)).prod
                (sample - z)
                (zetaSpectralEval f z)).symm
            _ = ((sample - z) *
                  (samples.map (fun nextSample : ℂ => nextSample - z)).prod) *
                    zetaSpectralEval f z := by
              exact congrArg
                (fun value : ℂ => value * zetaSpectralEval f z)
                (mul_comm
                  (samples.map (fun nextSample : ℂ => nextSample - z)).prod
                  (sample - z))
            _ = ((sample - z) ::
                  samples.map (fun nextSample : ℂ => nextSample - z)).prod *
                    zetaSpectralEval f z := by
              rfl)))

noncomputable def finiteSpectralZeroLinearMap
    (P : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] ZetaAdmissibleFunction :=
  finiteSpectralZeroLinearMapList P.toList

noncomputable def finiteSpectralZeroOperator
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  finiteSpectralZeroLinearMap P f

theorem finiteSpectralZeroLinearMap_apply
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction) :
    finiteSpectralZeroLinearMap P f = finiteSpectralZeroOperator P f := by
  rfl

theorem zetaSpectralEval_finiteSpectralZeroOperator
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaSpectralEval (finiteSpectralZeroOperator P f) z =
      (P.toList.map (fun sample : ℂ => sample - z)).prod *
        zetaSpectralEval f z := by
  exact zetaSpectralEval_finiteSpectralZeroOperatorList P.toList f z

theorem zetaZeroSideContribution_finiteSpectralZeroOperator
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaZeroSideContribution z (finiteSpectralZeroOperator P f) =
      (P.toList.map (fun sample : ℂ => sample - z)).prod *
        zetaZeroSideContribution z f := by
  have hspectral := zetaSpectralEval_finiteSpectralZeroOperator P f z
  unfold zetaZeroSideContribution
  exact Eq.trans
    (congrArg
      (fun value : ℂ => -((zetaZeroMultiplicity z : ℂ)) * value)
      hspectral)
    (calc
      -((zetaZeroMultiplicity z : ℂ)) *
          ((P.toList.map (fun sample : ℂ => sample - z)).prod *
            zetaSpectralEval f z) =
          (-((zetaZeroMultiplicity z : ℂ)) *
            (P.toList.map (fun sample : ℂ => sample - z)).prod) *
              zetaSpectralEval f z := by
        exact (mul_assoc
          (-((zetaZeroMultiplicity z : ℂ)))
          (P.toList.map (fun sample : ℂ => sample - z)).prod
          (zetaSpectralEval f z)).symm
      _ = ((P.toList.map (fun sample : ℂ => sample - z)).prod *
            -((zetaZeroMultiplicity z : ℂ))) * zetaSpectralEval f z := by
        exact congrArg
          (fun value : ℂ => value * zetaSpectralEval f z)
          (mul_comm
            (-((zetaZeroMultiplicity z : ℂ)))
            (P.toList.map (fun sample : ℂ => sample - z)).prod)
      _ = (P.toList.map (fun sample : ℂ => sample - z)).prod *
            (-((zetaZeroMultiplicity z : ℂ)) * zetaSpectralEval f z) := by
        exact mul_assoc
          (P.toList.map (fun sample : ℂ => sample - z)).prod
          (-((zetaZeroMultiplicity z : ℂ)))
          (zetaSpectralEval f z))

theorem zetaSpectralEval_finiteSpectralZeroOperator_eq_zero_of_mem
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ)
    (hz : z ∈ P) :
    zetaSpectralEval (finiteSpectralZeroOperator P f) z = 0 := by
  have hzList : z ∈ P.toList := Finset.mem_toList.mpr hz
  have hzeroFactor : (0 : ℂ) ∈ P.toList.map (fun sample : ℂ => sample - z) :=
    List.mem_map.mpr ⟨z, hzList, sub_self z⟩
  have hproductZero :
      (P.toList.map (fun sample : ℂ => sample - z)).prod = 0 :=
    List.prod_eq_zero hzeroFactor
  exact Eq.trans
    (zetaSpectralEval_finiteSpectralZeroOperator P f z)
    (Eq.trans
      (congrArg
        (fun value : ℂ => value * zetaSpectralEval f z)
        hproductZero)
      (zero_mul (zetaSpectralEval f z)))

/-- Away from the prescribed finite zero set, the differential multiplier is
nonzero. -/
theorem finiteSpectralZeroOperator_multiplier_ne_zero_of_not_mem
    (P : Finset ℂ)
    (z : ℂ)
    (hz : z ∉ P) :
    (P.toList.map (fun sample : ℂ => sample - z)).prod ≠ 0 :=
  List.prod_ne_zero
    (fun hzeroMember =>
      match List.mem_map.mp hzeroMember with
      | ⟨sample, hsampleList, hsampleDifference⟩ =>
          have hsampleEqual : sample = z :=
            sub_eq_zero.mp hsampleDifference
          hz
            (Eq.mp
              (congrArg (fun value : ℂ => value ∈ P) hsampleEqual)
              (Finset.mem_toList.mp hsampleList)))

theorem finiteSpectralZeroOperator_mem_evaluationKernel
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction) :
    ∀ z : ℂ, z ∈ P →
      zetaSpectralEval (finiteSpectralZeroOperator P f) z = 0 :=
  fun z hz =>
    zetaSpectralEval_finiteSpectralZeroOperator_eq_zero_of_mem P f z hz

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
