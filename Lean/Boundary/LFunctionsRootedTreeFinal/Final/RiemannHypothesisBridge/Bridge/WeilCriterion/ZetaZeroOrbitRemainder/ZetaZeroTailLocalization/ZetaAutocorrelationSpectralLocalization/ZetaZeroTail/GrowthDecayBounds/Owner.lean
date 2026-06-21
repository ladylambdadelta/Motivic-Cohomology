import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TransformEnvelopes.Owner

/-!
# Boundary zero-side tail

Split owner layer for the zero-side tail proof graph.  Public theorem names are
preserved through the root owner re-export.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Completed-zero multiplicities have polynomial growth in centered height. -/
theorem exists_zetaZeroMultiplicityGrowthEnvelope_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htailBoundary : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ M : ℝ, ∃ d : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          zetaZeroMultiplicityGrowthEnvelope M d ρ := by
  match exists_zetaZeroMultiplicityGrowthEnvelope_bound_from_counting
      hbranch
      hpartialOneTwo htailOneTwo hcompactOneTwo
      hpartialLeft htailBoundary hcompactBoundary with
  | ⟨M, d, hMpos, hbound⟩ =>
      ⟨M, d, hMpos, fun ρ => by
        change
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
            M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)
        exact hbound ρ⟩

/-- A Paley-Wiener vertical-strip decay constant bounds spectral evaluation on the
centered completed-zero locus. -/
theorem zetaZeroSpectralEval_norm_le_of_verticalStripDecayConstant
    (φ : ZetaAdmissibleFunction) (N : ℕ)
    (a b C : ℝ)
    (hCbound :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction' z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
    (hstrip :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        a ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
          (zetaCenteredZero (ρ : ℂ)).re ≤ b)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
      zetaZeroSpectralEvalDecayEnvelope C N ρ := by
  have hρstrip :
      a ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
        (zetaCenteredZero (ρ : ℂ)).re ≤ b :=
    hstrip ρ
  have hbound :
      ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (zetaCenteredZero (ρ : ℂ))‖ ≤
        C * (1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖) ^ (-(N : ℤ)) :=
    hCbound
      (zetaCenteredZero (ρ : ℂ))
      hρstrip.1
      hρstrip.2
  have heval :
      zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)) =
        Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (zetaCenteredZero (ρ : ℂ)) :=
    zetaSpectralEval_eq_laplace φ (zetaCenteredZero (ρ : ℂ))
  change
    ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
      C * (1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖) ^ (-(N : ℤ))
  calc
    ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ =
        ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction'
            (zetaCenteredZero (ρ : ℂ))‖ := congrArg norm heval
    _ ≤ C * (1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖) ^ (-(N : ℤ)) := hbound

/-- Paley-Wiener decay bounds the spectral transform on the completed-zero locus. -/
theorem exists_zetaZeroSpectralEvalDecayEnvelope_bound
    (φ : ZetaAdmissibleFunction) (N : ℕ) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
          zetaZeroSpectralEvalDecayEnvelope B N ρ := by
  match exists_zetaCenteredZero_fixed_vertical_strip with
  | ⟨a, b, hstrip⟩ =>
      match zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
          φ a b N with
      | ⟨C, hCpos, hCbound⟩ =>
          ⟨C, hCpos, fun ρ =>
            zetaZeroSpectralEval_norm_le_of_verticalStripDecayConstant
              φ N a b C hCbound hstrip ρ⟩

/-- Separate multiplicity and spectral bounds give a product-envelope bound for the
multiplicity-weighted transform majorant. -/
theorem zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
    (φ : ZetaAdmissibleFunction)
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (hgrowth :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          zetaZeroMultiplicityGrowthEnvelope M d ρ)
    (hdecay :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
          zetaZeroSpectralEvalDecayEnvelope B N ρ) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      zetaZeroMultiplicityTransformMajorant φ ρ ≤
        zetaZeroGrowthDecayProductEnvelope M d B N ρ := by
  intro ρ
  change
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
        ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
      zetaZeroMultiplicityGrowthEnvelope M d ρ *
        zetaZeroSpectralEvalDecayEnvelope B N ρ
  have hleft_nonneg :
      0 ≤ ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ :=
    norm_nonneg (zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)))
  have hright_left_nonneg :
      0 ≤ zetaZeroMultiplicityGrowthEnvelope M d ρ :=
    le_trans
      (norm_nonneg ((zetaZeroMultiplicity (ρ : ℂ) : ℂ)))
      (hgrowth ρ)
  exact mul_le_mul
    (hgrowth ρ)
    (hdecay ρ)
    hleft_nonneg
    hright_left_nonneg

/-- A growth-decay product with requested strong decay is absorbed by a single summable
polynomial envelope. -/
theorem exists_zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_requestedDecay
    (M : ℝ) (d : ℕ) (B : ℝ)
    (hM : 0 < M) (hB : 0 < B) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  refine ⟨M * B, 0, ?_, ?_⟩
  · exact mul_pos hM hB
  · intro ρ
    exact zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
      M d B 0 hM hB ρ

/-- Multiplicity growth and transform decay combine into the zero-side transform envelope. -/
theorem exists_zetaZeroMultiplicityTransformEnvelope_bound_of_growth_and_decay
    (φ : ZetaAdmissibleFunction)
    (hgrowth :
      ∃ M : ℝ, ∃ d : ℕ,
        0 < M ∧
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
            zetaZeroMultiplicityGrowthEnvelope M d ρ)
    (hdecay :
      ∀ N : ℕ, ∃ B : ℝ,
        0 < B ∧
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
            zetaZeroSpectralEvalDecayEnvelope B N ρ) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroMultiplicityTransformMajorant φ ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  match hgrowth with
  | ⟨M, d, hMpos, hgrowth_bound⟩ =>
      match hdecay (d + (0 + 3) + 1) with
      | ⟨B, hBpos, hdecay_bound⟩ =>
          ⟨M * B, 0, mul_pos hMpos hBpos, fun ρ => by
            have hmajorant_product :
                zetaZeroMultiplicityTransformMajorant φ ρ ≤
                  zetaZeroGrowthDecayProductEnvelope M d B (d + (0 + 3) + 1) ρ :=
              zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
                φ M d B (d + (0 + 3) + 1) hgrowth_bound hdecay_bound ρ
            have hproduct :
                zetaZeroGrowthDecayProductEnvelope M d B (d + (0 + 3) + 1) ρ ≤
                  zetaZeroMultiplicityTransformEnvelope (M * B) 0 ρ :=
              zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
                M d B 0 hMpos hBpos ρ
            exact le_trans hmajorant_product hproduct⟩

/-- Zero multiplicity growth and Paley-Wiener transform decay give a summable polynomial
envelope for the multiplicity-weighted transform majorant. -/
theorem exists_zetaZeroMultiplicityTransformEnvelope_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htailBoundary : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (φ : ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformEnvelope A k ρ) ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroMultiplicityTransformMajorant φ ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  match exists_completedZeroMultiplicityCounting_height_bound
      hbranch
      hpartialOneTwo htailOneTwo hcompactOneTwo
      hpartialLeft htailBoundary hcompactBoundary with
  | ⟨C, dCount, hCpos, hcount⟩ =>
      match exists_zetaZeroMultiplicityGrowthEnvelope_bound
          hbranch
          hpartialOneTwo htailOneTwo hcompactOneTwo
          hpartialLeft htailBoundary hcompactBoundary with
      | ⟨M, dGrowth, hMpos, hgrowth_bound⟩ =>
          let k : ℕ := dCount + (dGrowth + 1)
          match exists_zetaZeroSpectralEvalDecayEnvelope_bound
              φ
              (dGrowth + (k + 3) + 1) with
          | ⟨B, hBpos, hdecay_bound⟩ =>
              ⟨M * B, k, mul_pos hMpos hBpos,
                by
                  change
                    Summable
                      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
                        zetaZeroMultiplicityTransformEnvelope (M * B)
                          (dCount + (dGrowth + 1)) ρ)
                  exact summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
                    (M * B) C dCount (dGrowth + 1) hCpos hcount,
                fun ρ => by
                  have hmajorant_product :
                      zetaZeroMultiplicityTransformMajorant φ ρ ≤
                        zetaZeroGrowthDecayProductEnvelope M dGrowth B
                          (dGrowth + (k + 3) + 1) ρ :=
                    zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
                      φ M dGrowth B
                      (dGrowth + (k + 3) + 1)
                      hgrowth_bound
                      hdecay_bound
                      ρ
                  have hproduct :
                      zetaZeroGrowthDecayProductEnvelope M dGrowth B
                          (dGrowth + (k + 3) + 1) ρ ≤
                        zetaZeroMultiplicityTransformEnvelope (M * B) k ρ :=
                    zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
                      M dGrowth B k hMpos hBpos ρ
                  exact le_trans hmajorant_product hproduct⟩

end
end LFunctions
end Boundary
