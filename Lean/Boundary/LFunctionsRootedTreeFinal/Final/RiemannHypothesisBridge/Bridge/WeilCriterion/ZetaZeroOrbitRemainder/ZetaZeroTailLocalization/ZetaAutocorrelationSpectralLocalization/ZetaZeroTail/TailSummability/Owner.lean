import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.GrowthDecayBounds.Owner

/-!
# Boundary zero-side tail

Split owner layer for the zero-side tail proof graph.  Public theorem names are
preserved through the root owner re-export.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The contribution majorant unfolds to multiplicity times transform size. -/
theorem zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroSideContributionMajorant φ ρ =
      zetaZeroMultiplicityTransformMajorant φ ρ := by
  have hmajorant_unfold :
      zetaZeroSideContributionMajorant φ ρ =
        ‖zetaZeroSideContribution (ρ : ℂ) φ‖ :=
    rfl
  have hcontribution_unfold :
      ‖zetaZeroSideContribution (ρ : ℂ) φ‖ =
        ‖(-(zetaZeroMultiplicity (ρ : ℂ) : ℂ)) *
            zetaSpectralEval φ (ρ : ℂ)‖ :=
    congrArg norm (zetaZeroSideContribution_def (ρ : ℂ) φ)
  have htransform_unfold :
      zetaZeroMultiplicityTransformMajorant φ ρ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
          ‖zetaSpectralEval φ (ρ : ℂ)‖ :=
    rfl
  have hnorm :
      ‖(-(zetaZeroMultiplicity (ρ : ℂ) : ℂ)) *
          zetaSpectralEval φ (ρ : ℂ)‖ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
          ‖zetaSpectralEval φ (ρ : ℂ)‖ := by
    calc
      ‖(-(zetaZeroMultiplicity (ρ : ℂ) : ℂ)) *
          zetaSpectralEval φ (ρ : ℂ)‖ =
          ‖(-(zetaZeroMultiplicity (ρ : ℂ) : ℂ))‖ *
            ‖zetaSpectralEval φ (ρ : ℂ)‖ := by
        exact norm_mul
          (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ))
          (zetaSpectralEval φ (ρ : ℂ))
      _ =
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
            ‖zetaSpectralEval φ (ρ : ℂ)‖ := by
        exact congrArg
          (fun x : ℝ => x *
            ‖zetaSpectralEval φ (ρ : ℂ)‖)
          (norm_neg
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ)
          )
  exact Eq.trans hmajorant_unfold
    (Eq.trans hcontribution_unfold
      (Eq.trans hnorm htransform_unfold.symm))

/-- Zero-counting, multiplicity, and Paley-Wiener transform decay make the
multiplicity-weighted transform majorant summable over the completed-zero locus. -/
theorem summable_zetaZeroMultiplicityTransformMajorant
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroMultiplicityTransformMajorant φ ρ) := by
  exact match exists_zetaZeroMultiplicityTransformEnvelope_bound
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary φ with
  | ⟨A, k, _hApos, henv, hbound⟩ =>
      have hnormBound :
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            ‖zetaZeroMultiplicityTransformMajorant φ ρ‖ ≤
              zetaZeroMultiplicityTransformEnvelope A k ρ := by
        intro ρ
        have hmajorant_nonneg :
            0 ≤ zetaZeroMultiplicityTransformMajorant φ ρ :=
          zetaZeroMultiplicityTransformMajorant_nonnegative φ ρ
        have hnorm :
            ‖zetaZeroMultiplicityTransformMajorant φ ρ‖ =
              zetaZeroMultiplicityTransformMajorant φ ρ :=
          Real.norm_of_nonneg hmajorant_nonneg
        calc
          ‖zetaZeroMultiplicityTransformMajorant φ ρ‖ =
              zetaZeroMultiplicityTransformMajorant φ ρ := hnorm
          _ ≤ zetaZeroMultiplicityTransformEnvelope A k ρ := hbound ρ
      Summable.of_norm_bounded
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformEnvelope A k ρ)
        henv
        hnormBound

/-- Zero-density, multiplicity, and transform-decay estimates make the zero-side majorant
summable over the completed-zero locus. -/
theorem summable_zetaZeroSideContributionMajorant
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContributionMajorant φ ρ) := by
  have hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformMajorant φ ρ) :=
    summable_zetaZeroMultiplicityTransformMajorant
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary φ
  have hfun :
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContributionMajorant φ ρ) =
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformMajorant φ ρ) := by
    funext ρ
    exact zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant φ ρ
  exact Eq.subst
    (motive := fun u : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ => Summable u)
    hfun.symm
    hsum

/-- The completed zero-side contribution is summable over the completed zero locus.

This is the analytic convergence input that makes zero-tail excision a genuine decomposition
of the completed zero-side `tsum`. -/
theorem summable_zetaZeroSideContribution
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContribution (ρ : ℂ) φ) := by
  have hmajorant :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContributionMajorant φ ρ) :=
    summable_zetaZeroSideContributionMajorant
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary φ
  have hmajorant_norm :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          ‖zetaZeroSideContribution (ρ : ℂ) φ‖) := by
    have hfun :
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            zetaZeroSideContributionMajorant φ ρ) =
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            ‖zetaZeroSideContribution (ρ : ℂ) φ‖) := by
      funext ρ
      rfl
    exact
      match hfun with
      | rfl => hmajorant
  exact hmajorant_norm.of_norm

/-- Splitting the completed zero-side sum into a finite zero set and its complementary tail.

This is the complex owner form of zero-tail excision.  The excluded finite set must consist of
completed zeros, so its finite contribution can be compared with the ambient completed-zero
subtype sum. -/
theorem zetaCompletedZeroSideSum_eq_finite_add_tail
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) φ)) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroSideContribution (ρ : ℂ) φ) =
      (∑ η in S, zetaZeroSideContribution η φ) +
        zetaZeroTail S φ := by
  have hsplit :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) φ) =
        (∑ η in S.attach,
          zetaZeroSideContribution
            ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
            zetaZeroSideContribution
              ((⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) :=
    completedZeroSubtype_tsum_eq_finite_add_complement
      S
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContribution (ρ : ℂ) φ)
      hS
      hsum
  have hfinite :
      (∑ η in S.attach,
        zetaZeroSideContribution
          ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) =
        ∑ η in S, zetaZeroSideContribution η φ :=
    zetaZeroSideContribution_sum_attach_eq_sum S φ hS
  have htail_unfold :
      zetaZeroTail S φ =
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          zetaZeroSideContribution (ρ : ℂ) φ) :=
    rfl
  have hsplit_target :
      (∑ η in S.attach,
          zetaZeroSideContribution
            ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
            zetaZeroSideContribution
              ((⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) =
        (∑ η in S, zetaZeroSideContribution η φ) +
          zetaZeroTail S φ :=
    Eq.trans
      (congrArg
        (fun x : ℂ =>
          x +
            (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
              zetaZeroSideContribution
                ((⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ))
        hfinite)
      (congrArg
        (fun x : ℂ =>
          (∑ η in S, zetaZeroSideContribution η φ) + x)
        htail_unfold.symm)
  exact Eq.trans hsplit
    hsplit_target

end
end LFunctions
end Boundary
