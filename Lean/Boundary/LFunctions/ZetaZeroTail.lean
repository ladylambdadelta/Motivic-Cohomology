import Boundary.LFunctions.ZetaZeroOrbitContribution

/-!
# Boundary zero-side tail

This file packages the tail functional as a consumer of the zero-side
definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The zero tail is the tsum over completed zeros outside the excluded set. -/
theorem zetaZeroTail_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaZeroSideContribution (η : ℂ) φ) := by
  rfl

/-- The real-valued zero tail is the real part of the complex one. -/
theorem zetaZeroTailRe_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTailRe S φ = Complex.re (zetaZeroTail S φ) := by
  rfl

/-- Pure finite-excision splitting for a completed-zero-indexed family.

This is the topology/root summability theorem behind zero-tail excision: a summable family
over the completed-zero subtype splits into the finite selected part and the complementary
subtype tail. -/
theorem completedZeroSubtype_tsum_eq_finiteSubtype_add_complement
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑ η in S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) := by
  sorry

/-- Generic finite-excision splitting for a completed-zero-indexed family.

This is the purely summability/topology root behind zero-tail excision.  The zeta-specific
theorem below only applies it to the zero-side contribution family. -/
theorem completedZeroSubtype_tsum_eq_finite_add_complement
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑ η in S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) :=
  completedZeroSubtype_tsum_eq_finiteSubtype_add_complement S F hS hF

/-- The attached finite zero-set sum is the ordinary finite zero-set contribution. -/
theorem zetaZeroSideContribution_sum_attach_eq_sum
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑ η in S.attach,
      zetaZeroSideContribution
        ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) =
      ∑ η in S, zetaZeroSideContribution η φ := by
  exact Finset.sum_attach S (fun η : ℂ => zetaZeroSideContribution η φ)

/-- Majorant for the zero-side contribution over the completed-zero locus. -/
noncomputable def zetaZeroSideContributionMajorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  ‖zetaZeroSideContribution (ρ : ℂ) φ‖

/-- The zero-side contribution is bounded by its majorant. -/
theorem norm_zetaZeroSideContribution_le_majorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖zetaZeroSideContribution (ρ : ℂ) φ‖ ≤
      zetaZeroSideContributionMajorant φ ρ := by
  unfold zetaZeroSideContributionMajorant
  exact le_refl _

/-- Zero-density, multiplicity, and transform-decay estimates make the zero-side majorant
summable over the completed-zero locus. -/
theorem summable_zetaZeroSideContributionMajorant
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContributionMajorant φ ρ) := by
  sorry

/-- The completed zero-side contribution is summable over the completed zero locus.

This is the analytic convergence input that makes zero-tail excision a genuine decomposition
of the completed zero-side `tsum`. -/
theorem summable_zetaZeroSideContribution
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContribution (ρ : ℂ) φ) := by
  have hmajorant :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContributionMajorant φ ρ) :=
    summable_zetaZeroSideContributionMajorant φ
  unfold zetaZeroSideContributionMajorant at hmajorant
  exact hmajorant.of_norm

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
  unfold zetaZeroTail
  exact Eq.trans hsplit
    (congrArg
      (fun x : ℂ =>
        x +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
            zetaZeroSideContribution
              ((⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ))
      hfinite)

end
end LFunctions
end Boundary
