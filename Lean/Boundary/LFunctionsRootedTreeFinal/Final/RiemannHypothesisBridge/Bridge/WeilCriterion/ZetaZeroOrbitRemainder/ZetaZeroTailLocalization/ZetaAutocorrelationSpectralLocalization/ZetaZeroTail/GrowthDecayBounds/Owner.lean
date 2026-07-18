import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TransformEnvelopes.Owner

/-!
# Boundary zero-side tail

Split owner layer for the zero-side tail proof graph.  Public theorem names are
preserved through the root owner re-export.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Centering preserves the vertical height used by the decay estimate. -/
theorem zetaCompletedZeroCenteredHeight_eq_one_add_norm_im
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroCenteredHeight ρ = 1 + ‖(ρ : ℂ).im‖ := by
  have himNorm :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ = ‖(ρ : ℂ).im‖ :=
    congrArg norm (zetaCenteredZero_im_eq ρ)
  have hunfold :
      zetaCompletedZeroCenteredHeight ρ =
        1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖ :=
    Eq.refl _
  exact Eq.trans hunfold (congrArg (fun height : ℝ => 1 + height) himNorm)

/-- The decay envelope is the vertical-strip polynomial expression. -/
theorem zetaZeroSpectralEvalDecayEnvelope_eq_verticalExpression
    (C : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroSpectralEvalDecayEnvelope C N ρ =
      C * (1 + ‖(ρ : ℂ).im‖) ^ (-(N : ℤ)) := by
  have hunfold :
      zetaZeroSpectralEvalDecayEnvelope C N ρ =
        C * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) :=
    Eq.refl _
  have hheight :
      C * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) =
        C * (1 + ‖(ρ : ℂ).im‖) ^ (-(N : ℤ)) :=
    congrArg
      (fun height : ℝ => C * height ^ (-(N : ℤ)))
      (zetaCompletedZeroCenteredHeight_eq_one_add_norm_im ρ)
  exact Eq.trans hunfold hheight

/-- Completed-zero multiplicities have polynomial growth in centered height. -/
theorem exists_zetaZeroMultiplicityGrowthEnvelope_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ M : ℝ, ∃ d : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          zetaZeroMultiplicityGrowthEnvelope M d ρ := by
  exact match exists_zetaZeroMultiplicityGrowthEnvelope_bound_from_counting
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary with
  | ⟨M, d, hMpos, hbound⟩ =>
      Exists.intro M
        (Exists.intro d
          (And.intro hMpos
            (fun ρ =>
              (show
                ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
                  M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) from
                hbound ρ))))

/-- A Paley-Wiener vertical-strip decay constant bounds spectral evaluation on the
completed-zero locus. -/
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
        a ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ b)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤
      zetaZeroSpectralEvalDecayEnvelope C N ρ := by
  have hρstrip :
      a ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ b :=
    hstrip ρ
  have hbound :
      ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (ρ : ℂ)‖ ≤
        C * (1 + ‖(ρ : ℂ).im‖) ^ (-(N : ℤ)) :=
    hCbound
      (ρ : ℂ)
      hρstrip.1
      hρstrip.2
  have heval :
      zetaSpectralEval φ (ρ : ℂ) =
        Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (ρ : ℂ) :=
    zetaSpectralEval_eq_laplace φ (ρ : ℂ)
  have hvertical :
      ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤
        C * (1 + ‖(ρ : ℂ).im‖) ^ (-(N : ℤ)) :=
    calc
    ‖zetaSpectralEval φ (ρ : ℂ)‖ =
        ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (ρ : ℂ)‖ :=
      congrArg norm heval
    _ ≤ C * (1 + ‖(ρ : ℂ).im‖) ^ (-(N : ℤ)) := hbound
  exact Eq.subst
    (motive := fun envelope : ℝ => ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤ envelope)
    (zetaZeroSpectralEvalDecayEnvelope_eq_verticalExpression C N ρ).symm
    hvertical

/-- Paley-Wiener decay bounds the spectral transform on the completed-zero locus. -/
theorem exists_zetaZeroSpectralEvalDecayEnvelope_bound
    (φ : ZetaAdmissibleFunction) (N : ℕ) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤
          zetaZeroSpectralEvalDecayEnvelope B N ρ := by
  exact match exists_zetaCompletedZero_fixed_vertical_strip with
  | ⟨a, b, hstrip⟩ =>
      match zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
          φ a b N with
      | ⟨C, hCpos, hCbound⟩ =>
          Exists.intro C
            (And.intro hCpos
              (fun ρ =>
                zetaZeroSpectralEval_norm_le_of_verticalStripDecayConstant
                  φ N a b C hCbound hstrip ρ))

/-- The transform majorant unfolds to the product used by the separate bounds. -/
theorem zetaZeroMultiplicityTransformMajorant_eq_normProduct
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroMultiplicityTransformMajorant φ ρ =
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
        ‖zetaSpectralEval φ (ρ : ℂ)‖ :=
  Eq.refl _

/-- The growth-decay envelope unfolds to its two named factors. -/
theorem zetaZeroGrowthDecayProductEnvelope_eq_factorProduct
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroGrowthDecayProductEnvelope M d B N ρ =
      zetaZeroMultiplicityGrowthEnvelope M d ρ *
        zetaZeroSpectralEvalDecayEnvelope B N ρ :=
  Eq.refl _

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
        ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤
          zetaZeroSpectralEvalDecayEnvelope B N ρ) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      zetaZeroMultiplicityTransformMajorant φ ρ ≤
        zetaZeroGrowthDecayProductEnvelope M d B N ρ := by
  intro ρ
  have hleft_nonneg :
      0 ≤ ‖zetaSpectralEval φ (ρ : ℂ)‖ :=
    norm_nonneg (zetaSpectralEval φ (ρ : ℂ))
  have hright_left_nonneg :
      0 ≤ zetaZeroMultiplicityGrowthEnvelope M d ρ :=
    le_trans
      (norm_nonneg ((zetaZeroMultiplicity (ρ : ℂ) : ℂ)))
      (hgrowth ρ)
  have hproduct :
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
          ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤
        zetaZeroMultiplicityGrowthEnvelope M d ρ *
          zetaZeroSpectralEvalDecayEnvelope B N ρ :=
    mul_le_mul
      (hgrowth ρ)
      (hdecay ρ)
      hleft_nonneg
      hright_left_nonneg
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ zetaZeroGrowthDecayProductEnvelope M d B N ρ)
    (zetaZeroMultiplicityTransformMajorant_eq_normProduct φ ρ).symm
    (Eq.subst
      (motive := fun right : ℝ =>
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
            ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤ right)
      (zetaZeroGrowthDecayProductEnvelope_eq_factorProduct M d B N ρ).symm
      hproduct)

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
  exact
    Exists.intro (M * B)
      (Exists.intro 0
        ⟨mul_pos hM hB,
          fun ρ =>
            zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
              M d B 0 hM hB ρ⟩)

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
          ‖zetaSpectralEval φ (ρ : ℂ)‖ ≤
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
              have hApos : 0 < M * B := mul_pos hMpos hBpos
              have hbound :
                  ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
                    zetaZeroMultiplicityTransformMajorant φ ρ ≤
                      zetaZeroMultiplicityTransformEnvelope (M * B) 0 ρ := by
                intro ρ
                have hmajorant_product :
                    zetaZeroMultiplicityTransformMajorant φ ρ ≤
                      zetaZeroGrowthDecayProductEnvelope M d B
                        (d + (0 + 3) + 1) ρ :=
                  zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
                    φ M d B (d + (0 + 3) + 1) hgrowth_bound hdecay_bound ρ
                have hproduct :
                    zetaZeroGrowthDecayProductEnvelope M d B
                        (d + (0 + 3) + 1) ρ ≤
                      zetaZeroMultiplicityTransformEnvelope (M * B) 0 ρ :=
                  zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
                    M d B 0 hMpos hBpos ρ
                exact le_trans hmajorant_product hproduct
              exact ⟨M * B, 0, hApos, hbound⟩

/-- Zero multiplicity growth and Paley-Wiener transform decay give a summable polynomial
envelope for the multiplicity-weighted transform majorant. -/
theorem exists_zetaZeroMultiplicityTransformEnvelope_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
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
  exact match exists_completedZeroMultiplicityCounting_height_bound
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary with
  | ⟨C, dCount, hCpos, hcount⟩ =>
      match exists_zetaZeroMultiplicityGrowthEnvelope_bound
          hbranch
          hpartialOneTwo hcompactOneTwo
          hfinite
          hpartialLeft hcompactBoundary with
      | ⟨M, dGrowth, hMpos, hgrowth_bound⟩ =>
          let k : ℕ := dCount + (dGrowth + 1)
          match exists_zetaZeroSpectralEvalDecayEnvelope_bound
              φ
              (dGrowth + (k + 3) + 1) with
          | ⟨B, hBpos, hdecay_bound⟩ =>
              Exists.intro (M * B)
                (Exists.intro k
                  (And.intro
                    (mul_pos hMpos hBpos)
                    (And.intro
                      (show
                        Summable
                          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
                            zetaZeroMultiplicityTransformEnvelope (M * B)
                              (dCount + (dGrowth + 1)) ρ) from
                        summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
                          (M * B) C dCount (dGrowth + 1) hCpos hcount)
                      (fun ρ => by
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
                        exact le_trans hmajorant_product hproduct))))

end
end LFunctions
end Boundary
