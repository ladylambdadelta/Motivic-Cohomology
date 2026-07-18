import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.FiniteComplement.Owner

/-!
# Boundary zero-side tail

Split owner layer for the zero-side tail proof graph.  Public theorem names are
preserved through the root owner re-export.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
  exact
    (show
    ‖zetaZeroSideContribution (ρ : ℂ) φ‖ ≤
      ‖zetaZeroSideContribution (ρ : ℂ) φ‖ from
      le_refl _)

/-- Multiplicity-weighted transform majorant for a completed-zero contribution. -/
noncomputable def zetaZeroMultiplicityTransformMajorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
    ‖zetaSpectralEval φ (ρ : ℂ)‖

/-- The zero-side multiplicity-transform majorant is nonnegative. -/
theorem zetaZeroMultiplicityTransformMajorant_nonnegative
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroMultiplicityTransformMajorant φ ρ := by
  exact
    (show
    0 ≤
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
        ‖zetaSpectralEval φ (ρ : ℂ)‖ from
      mul_nonneg
        (norm_nonneg ((zetaZeroMultiplicity (ρ : ℂ) : ℂ)))
        (norm_nonneg (zetaSpectralEval φ (ρ : ℂ))))

/-- Polynomial zero-side envelope for multiplicity-weighted transform values. -/
noncomputable def zetaZeroMultiplicityTransformEnvelope
    (A : ℝ) (k : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))

/-- The zero-side envelope is nonnegative when its constant is nonnegative. -/
theorem zetaZeroMultiplicityTransformEnvelope_nonnegative
    {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroMultiplicityTransformEnvelope A k ρ := by
  have hheight :
      0 ≤ zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (le_trans zero_le_one (zetaCompletedZeroCenteredHeight_ge_one ρ))
      (-(k + 3 : ℤ))
  exact
    (show 0 ≤ A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) from
      mul_nonneg hA hheight)

/-- Polynomial zero-side envelopes are summable over the completed-zero locus
after choosing the envelope exponent beyond the zero-counting degree.

This is the zero-counting owner theorem in the form consumed by the tail
majorant: the envelope index records the necessary counting margin. -/
theorem summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
    (A C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroMultiplicityTransformEnvelope A (d + k) ρ) := by
  have hbase :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) :=
    summable_completedZero_centeredHeight_negativePower_of_counting_bound
      C d k hCpos hcount
  exact
    (show
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) from
        hbase.mul_left A)

/-- Polynomial growth envelope for completed-zero multiplicities. -/
noncomputable def zetaZeroMultiplicityGrowthEnvelope
    (M : ℝ) (d : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)

/-- Rapid-decay envelope for the spectral transform evaluated at completed zeros. -/
noncomputable def zetaZeroSpectralEvalDecayEnvelope
    (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))

/-- Product envelope obtained before absorbing growth and decay into one polynomial tail. -/
noncomputable def zetaZeroGrowthDecayProductEnvelope
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  zetaZeroMultiplicityGrowthEnvelope M d ρ *
    zetaZeroSpectralEvalDecayEnvelope B N ρ

/-- Multiplicity growth envelopes are nonnegative for positive constants. -/
theorem zetaZeroMultiplicityGrowthEnvelope_nonnegative
    {M : ℝ} (hM : 0 < M) (d : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroMultiplicityGrowthEnvelope M d ρ := by
  have hheight :
      0 ≤ zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) :=
    zpow_nonneg
      (le_trans zero_le_one (zetaCompletedZeroCenteredHeight_ge_one ρ))
      (d : ℤ)
  exact
    (show 0 ≤ M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) from
      mul_nonneg (le_of_lt hM) hheight)

/-- Spectral decay envelopes are nonnegative for positive constants. -/
theorem zetaZeroSpectralEvalDecayEnvelope_nonnegative
    {B : ℝ} (hB : 0 < B) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroSpectralEvalDecayEnvelope B N ρ := by
  have hheight :
      0 ≤ zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) :=
    zpow_nonneg
      (le_trans zero_le_one (zetaCompletedZeroCenteredHeight_ge_one ρ))
      (-(N : ℤ))
  exact
    (show 0 ≤ B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) from
      mul_nonneg (le_of_lt hB) hheight)

/-- Growth-decay product envelopes reduce to one constant times one power product. -/
theorem zetaZeroGrowthDecayProductEnvelope_eq_constant_mul_powerProduct
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroGrowthDecayProductEnvelope M d B N ρ =
      (M * B) *
        (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
  have hproduct_identity :
      (M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) *
          (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) =
        (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
    calc
    (M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) *
        (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) =
        M *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))) := by
      exact mul_assoc M
        (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
        (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))
    _ =
        M *
          (B *
            (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
              zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))) := by
      exact congrArg (fun x : ℝ => M * x)
        (by
          calc
            zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
                (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) =
                (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) * B) *
                  zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) := by
              exact (mul_assoc
                (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
                B
                (zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))).symm
            _ =
                (B * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) *
                  zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) := by
              exact congrArg
                (fun x : ℝ => x * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))
                (mul_comm (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) B)
            _ =
                B *
                  (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
                    zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
              exact mul_assoc B
                (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
                (zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))))
    _ =
        (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
      exact (mul_assoc M B
        (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))).symm
  exact hproduct_identity

/-- If the decay exponent is chosen past the growth degree, the product power is bounded
by the requested zero-tail decay power. -/
theorem zetaZero_height_growth_mul_decay_le_requestedDecay
    (d k : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ)) ≤
      zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) := by
  exact ZetaAdmissibleFunction.polynomialDegreeTimesRapidPower_le_requestedRapidPower
    d
    (k + 3)
    (zetaCompletedZeroCenteredHeight ρ)
    (zetaCompletedZeroCenteredHeight_ge_one ρ)

/-- A growth-decay envelope with sufficiently strong decay is bounded by a single
zero-tail transform envelope. -/
theorem zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
    (M : ℝ) (d : ℕ) (B : ℝ) (k : ℕ)
    (hM : 0 < M) (hB : 0 < B)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ ≤
      zetaZeroMultiplicityTransformEnvelope (M * B) k ρ := by
  have hconstant_nonneg : 0 ≤ M * B := by
    exact mul_nonneg (le_of_lt hM) (le_of_lt hB)
  have hpower :
      zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ)) ≤
        zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    zetaZero_height_growth_mul_decay_le_requestedDecay d k ρ
  have hscaled :
      (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ))) ≤
        (M * B) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    mul_le_mul_of_nonneg_left hpower hconstant_nonneg
  have hunfold :
      zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ =
        (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ))) :=
    zetaZeroGrowthDecayProductEnvelope_eq_constant_mul_powerProduct
      M d B (d + (k + 3) + 1) ρ
  have htarget :
      zetaZeroMultiplicityTransformEnvelope (M * B) k ρ =
        (M * B) * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    rfl
  exact Eq.subst
    (motive := fun y : ℝ =>
      zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ ≤ y)
    htarget.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        x ≤ (M * B) * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
      hunfold.symm
      hscaled)

end
end LFunctions
end Boundary
