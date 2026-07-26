import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.PolynomialWeightedDensity

/-!
# Finite-evaluation kernel density in completed-zero coordinates

The completed-zero coordinate image of probes annihilating finitely many
spectral evaluations is dense in the compatible subspace of discrete `l1`.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

noncomputable def zetaCompletedZeroCoordinateComplementL1Distance
    (P : Finset ℂ)
    (left right : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) : ℝ :=
  ∑' rho : ZetaCompletedZeroCoordinate,
    if (rho : ℂ) ∈ P then 0 else ‖left rho - right rho‖

theorem zetaCompletedZeroCoordinateComplementL1Distance_empty
    (left right : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    zetaCompletedZeroCoordinateComplementL1Distance ∅ left right =
      dist left right := by
  have hpointwise :
      (fun rho : ZetaCompletedZeroCoordinate =>
        if (rho : ℂ) ∈ (∅ : Finset ℂ) then 0 else ‖left rho - right rho‖) =
        (fun rho : ZetaCompletedZeroCoordinate => ‖(left - right) rho‖) :=
    funext
      (fun rho : ZetaCompletedZeroCoordinate =>
        if hmembership : (rho : ℂ) ∈ (∅ : Finset ℂ) then
          False.elim (Finset.not_mem_empty (rho : ℂ) hmembership)
        else
          Eq.refl ‖left rho - right rho‖)
  unfold zetaCompletedZeroCoordinateComplementL1Distance
  exact Eq.trans
    (congrArg tsum hpointwise)
    (Eq.trans
      (lp_one_norm_eq_tsum_norm (left - right)).symm
      (dist_eq_norm left right).symm)

theorem finiteSpectralZeroOperator_complementDistance_summand_eq
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (seed : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) :
    (if (rho : ℂ) ∈ P then 0
      else
        ‖target rho -
          zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            (finiteSpectralZeroOperator P seed) rho‖) =
      if (rho : ℂ) ∈ P then 0
      else
        ‖target rho -
          finiteSpectralZeroMultiplier P (rho : ℂ) *
            zetaZeroSideContribution (rho : ℂ) seed‖ := by
  if hmembership : (rho : ℂ) ∈ P then
    exact Eq.trans (if_pos hmembership) (if_pos hmembership).symm
  else
    have hcoordinate :
        zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            (finiteSpectralZeroOperator P seed) rho =
          finiteSpectralZeroMultiplier P (rho : ℂ) *
            zetaZeroSideContribution (rho : ℂ) seed :=
      Eq.trans
        (zetaCompletedZeroSideCoordinateL1LinearMap_apply
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          (finiteSpectralZeroOperator P seed) rho)
        (finiteSpectralZeroMultiplier_eq_operatorMultiplier P seed (rho : ℂ))
    exact Eq.trans
      (if_neg hmembership)
      (Eq.trans
        (congrArg (fun value : ℂ => ‖target rho - value‖) hcoordinate)
        (if_neg hmembership).symm)

theorem exists_quantitativeCarrierSeparation_kernel_complementDistance_lt
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ z : ℂ, z ∈ P → zetaSpectralEval f z = 0) ∧
        zetaCompletedZeroCoordinateComplementL1Distance P target
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            f) < epsilon := by
  obtain ⟨seed, hseedApproximation⟩ :=
    exists_polynomialWeighted_completedZeroSideCoordinate_approximation
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P target epsilon hepsilon
  let corrected : ZetaAdmissibleFunction := finiteSpectralZeroOperator P seed
  have hkernel :
      ∀ z : ℂ, z ∈ P → zetaSpectralEval corrected z = 0 :=
    finiteSpectralZeroOperator_mem_evaluationKernel P seed
  have hdistanceIdentity :
      zetaCompletedZeroCoordinateComplementL1Distance P target
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            corrected) =
        ∑' rho : ZetaCompletedZeroCoordinate,
          if (rho : ℂ) ∈ P then 0
          else
            ‖target rho -
              finiteSpectralZeroMultiplier P (rho : ℂ) *
                zetaZeroSideContribution (rho : ℂ) seed‖ := by
    unfold zetaCompletedZeroCoordinateComplementL1Distance
    exact tsum_congr
      (finiteSpectralZeroOperator_complementDistance_summand_eq
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        P target seed)
  exact ⟨corrected, hkernel,
    Eq.subst
      (motive := fun value : ℝ => value < epsilon)
      hdistanceIdentity.symm
      hseedApproximation⟩

/-- Quantitative carrier-separated kernel approximation with the explicit
finite reciprocal-multiplier constant retained for downstream estimates. -/
theorem exists_quantitativeCarrierSeparation_kernel_complementDistance_lt_with_carrierBound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (carrier : Finset ZetaCompletedZeroCoordinate)
    (hdisjoint :
      ∀ rho : ZetaCompletedZeroCoordinate,
        rho ∈ carrier → (rho : ℂ) ∉ P)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ (C : ℝ) (f : ZetaAdmissibleFunction),
      0 ≤ C ∧
        (∀ rho : ZetaCompletedZeroCoordinate,
          rho ∈ carrier →
            finiteSpectralZeroMultiplier P (rho : ℂ) ≠ 0 ∧
              ‖(finiteSpectralZeroMultiplier P (rho : ℂ))⁻¹‖ ≤ C) ∧
        (∀ z : ℂ, z ∈ P → zetaSpectralEval f z = 0) ∧
          zetaCompletedZeroCoordinateComplementL1Distance P target
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              f) < epsilon := by
  let C : ℝ := finiteSpectralZeroMultiplierCarrierInverseNormBound P carrier
  have hcarrierSeparation :
      0 ≤ C ∧
        ∀ rho : ZetaCompletedZeroCoordinate,
          rho ∈ carrier →
            finiteSpectralZeroMultiplier P (rho : ℂ) ≠ 0 ∧
              ‖(finiteSpectralZeroMultiplier P (rho : ℂ))⁻¹‖ ≤ C :=
    finiteSpectralZeroMultiplier_quantitativeCarrierSeparation
      P carrier hdisjoint
  match
    exists_quantitativeCarrierSeparation_kernel_complementDistance_lt
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P target epsilon hepsilon with
  | ⟨f, hkernel, hdistance⟩ =>
      exact
        ⟨C, f, hcarrierSeparation.1, hcarrierSeparation.2, hkernel, hdistance⟩

theorem exists_zetaCompletedZeroSideCoordinateL1_kernel_approximation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ z : ℂ, z ∈ P → zetaSpectralEval f z = 0) ∧
        zetaCompletedZeroCoordinateComplementL1Distance P target
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            f) < epsilon :=
  exists_quantitativeCarrierSeparation_kernel_complementDistance_lt
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    P target epsilon hepsilon

theorem zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_kernelDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    zetaCompletedZeroSideCoordinateL1Closure
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
      Set.univ := by
  exact Set.eq_univ_of_forall
    (fun target =>
      show target ∈ closure
        (Set.range
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)) from
      Metric.mem_closure_iff.mpr
        (fun epsilon hepsilon =>
          match
            exists_zetaCompletedZeroSideCoordinateL1_kernel_approximation
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              ∅ target epsilon hepsilon with
          | ⟨f, hfiniteKernel, hdistance⟩ =>
              let coordinate :=
                zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary f
              have hdistanceMetric : dist target coordinate < epsilon :=
                Eq.subst
                  (motive := fun value : ℝ => value < epsilon)
                  (zetaCompletedZeroCoordinateComplementL1Distance_empty
                    target coordinate)
                  hdistance
              ⟨coordinate, ⟨f, Eq.refl coordinate⟩, hdistanceMetric⟩))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
