import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling

/-!
# Prime-center weighted sampling bounds

This file owns the elementary weight transport from an unweighted prime-center
Plancherel-density polynomial bound to the weighted prime-sampling polynomial
bound used by the trace-energy source.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Nonnegative real values are equal to their real norm, at the prime-center
sampling owner level. -/
theorem primeCenterSampling_real_norm_eq_self_of_nonnegative
    (x : ℝ) (hx : 0 ≤ x) :
    ‖x‖ = x :=
  Real.norm_of_nonneg hx

/-- The completed prime-power weight has complex norm equal to the underlying
real weight, at the prime-center sampling owner level. -/
theorem primeCenterSampling_zetaPrimePowerIndex_complex_norm_weight_eq_weight
    (index : ZetaPrimePowerIndex) :
    ‖(ZetaPrimePowerIndex.weight index : ℂ)‖ =
      ZetaPrimePowerIndex.weight index := by
  calc
    ‖(ZetaPrimePowerIndex.weight index : ℂ)‖ =
        ‖ZetaPrimePowerIndex.weight index‖ := by
      exact Complex.norm_real (ZetaPrimePowerIndex.weight index)
    _ = ZetaPrimePowerIndex.weight index := by
      exact
        Real.norm_of_nonneg
          (ZetaPrimePowerIndex.weight_nonnegative index)

/-- Multiplying a prime-center density polynomial bound by the completed
prime-power weight is absorbed by shifting the polynomial height exponent. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_bound_of_density_bound_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction)
    (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity :
      ∀ index : ZetaPrimePowerIndex,
        ‖completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
            index f‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f‖ ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
  match ZetaPrimePowerIndex.weight_norm_mul_polynomialHeightDecay_le_shift k with
  | ⟨A, hafterA⟩ =>
      match hafterA with
      | ⟨l, hshiftAfterL⟩ =>
          let D : ℝ := C * A
          have hA : 0 ≤ A :=
            hshiftAfterL.left
          have hD : 0 ≤ D :=
            mul_nonneg hC hA
          have hbound :
              ∀ index : ZetaPrimePowerIndex,
                ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
                    index f‖ ≤
                  D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
            intro index
            have hweightNonnegative : 0 ≤ ZetaPrimePowerIndex.weight index :=
              ZetaPrimePowerIndex.weight_nonnegative index
            have hdensityNonnegative :
                0 ≤
                  completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                    index f :=
              completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity_nonnegative
                index f
            have hweightedNonnegative :
                0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling
                    index f :=
              completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
                index f
            have hdensityValue :
                completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                    index f ≤
                  C * ZetaPrimePowerIndex.polynomialHeightDecay k index :=
              Eq.subst
                (motive := fun value : ℝ =>
                  value ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k index)
                (primeCenterSampling_real_norm_eq_self_of_nonnegative
                  (completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                    index f)
                  hdensityNonnegative)
                (hdensity index)
            have hmulDensity :
                ZetaPrimePowerIndex.weight index *
                    completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                      index f ≤
                  ZetaPrimePowerIndex.weight index *
                    (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :=
              mul_le_mul_of_nonneg_left hdensityValue hweightNonnegative
            have hrightRearrange :
                ZetaPrimePowerIndex.weight index *
                    (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) =
                  C *
                    (ZetaPrimePowerIndex.weight index *
                      ZetaPrimePowerIndex.polynomialHeightDecay k index) := by
              calc
                ZetaPrimePowerIndex.weight index *
                    (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) =
                    (ZetaPrimePowerIndex.weight index * C) *
                      ZetaPrimePowerIndex.polynomialHeightDecay k index := by
                  exact (mul_assoc
                    (ZetaPrimePowerIndex.weight index)
                    C
                    (ZetaPrimePowerIndex.polynomialHeightDecay k index)).symm
                _ =
                    (C * ZetaPrimePowerIndex.weight index) *
                      ZetaPrimePowerIndex.polynomialHeightDecay k index := by
                  exact congrArg
                    (fun value : ℝ =>
                      value * ZetaPrimePowerIndex.polynomialHeightDecay k index)
                    (mul_comm (ZetaPrimePowerIndex.weight index) C)
                _ =
                    C *
                      (ZetaPrimePowerIndex.weight index *
                        ZetaPrimePowerIndex.polynomialHeightDecay k index) := by
                  exact
                    mul_assoc
                      C
                      (ZetaPrimePowerIndex.weight index)
                      (ZetaPrimePowerIndex.polynomialHeightDecay k index)
            have hweightDecay :
                ZetaPrimePowerIndex.weight index *
                    ZetaPrimePowerIndex.polynomialHeightDecay k index ≤
                  A * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
              have hcomplexWeight :
                  ‖(ZetaPrimePowerIndex.weight index : ℂ)‖ =
                    ZetaPrimePowerIndex.weight index :=
                primeCenterSampling_zetaPrimePowerIndex_complex_norm_weight_eq_weight
                  index
              exact Eq.subst
                (motive := fun value : ℝ =>
                  value * ZetaPrimePowerIndex.polynomialHeightDecay k index ≤
                    A * ZetaPrimePowerIndex.polynomialHeightDecay l index)
                hcomplexWeight
                (hshiftAfterL.right.right index)
            have hCmul :
                C *
                    (ZetaPrimePowerIndex.weight index *
                      ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
                  C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index) :=
              mul_le_mul_of_nonneg_left hweightDecay hC
            have hrightBound :
                ZetaPrimePowerIndex.weight index *
                    (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
                  C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index) :=
              Eq.subst
                (motive := fun leftValue : ℝ =>
                  leftValue ≤
                    C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index))
                hrightRearrange.symm
                hCmul
            have hfinalRight :
                C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index) =
                  D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
              calc
                C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index) =
                    (C * A) * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
                  exact (mul_assoc C A
                    (ZetaPrimePowerIndex.polynomialHeightDecay l index)).symm
                _ = D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
                  rfl
            have hvalue :
                ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
                    index f‖ =
                  completedAutocorrelationSpectralTransform_weightedPrimeSampling
                    index f :=
              primeCenterSampling_real_norm_eq_self_of_nonnegative
                (completedAutocorrelationSpectralTransform_weightedPrimeSampling index f)
                hweightedNonnegative
            have hsampling :
                completedAutocorrelationSpectralTransform_weightedPrimeSampling
                    index f =
                  ZetaPrimePowerIndex.weight index *
                    completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                      index f :=
              completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
                index f
            exact Eq.subst
              (motive := fun leftValue : ℝ =>
                leftValue ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
              hvalue.symm
              (Eq.subst
                (motive := fun leftValue : ℝ =>
                  leftValue ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
                hsampling.symm
                (le_trans
                  (le_trans hmulDensity hrightBound)
                  (le_of_eq hfinalRight)))
          exact ⟨D, l, hD, hbound⟩

/-! The same weight transport at the corrected vertical/Fourier owner.  This
is the bridge which turns the proved vertical density decay into the weighted
bound consumed by the Bessel and trace owners. -/

theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_bound_of_verticalDensity_bound_owner
    (f : ZetaAdmissibleFunction)
    (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          index f ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    ∃ D : ℝ, ∃ l : ℕ, 0 ≤ D ∧
      ∀ index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
            index f ≤
          D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
  match ZetaPrimePowerIndex.weight_norm_mul_polynomialHeightDecay_le_shift k with
  | ⟨A, hA⟩ =>
      match hA with
      | ⟨l, hshift⟩ =>
          let D : ℝ := C * A
          have hD : 0 ≤ D := mul_nonneg hC hshift.left
          have hbound : ∀ index : ZetaPrimePowerIndex,
              completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
                  index f ≤
                D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
            intro index
            have hweight : 0 ≤ ZetaPrimePowerIndex.weight index :=
              ZetaPrimePowerIndex.weight_nonnegative index
            have hdensityNonnegative :
                0 ≤ completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
                  index f :=
              completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity_nonnegative
                index f
            have hweightedNonnegative :
                0 ≤ completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
                  index f :=
              completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_nonnegative
                index f
            have hdensityValue := hdensity index
            have hmul := mul_le_mul_of_nonneg_left hdensityValue hweight
            have hweightDecay :
                ZetaPrimePowerIndex.weight index *
                    ZetaPrimePowerIndex.polynomialHeightDecay k index ≤
                  A * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
              exact Eq.subst
                (motive := fun value : ℝ =>
                  value * ZetaPrimePowerIndex.polynomialHeightDecay k index ≤
                    A * ZetaPrimePowerIndex.polynomialHeightDecay l index)
                (primeCenterSampling_zetaPrimePowerIndex_complex_norm_weight_eq_weight index)
                (hshift.right.right index)
            have hmulDecay :
                C * (ZetaPrimePowerIndex.weight index *
                    ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
                  C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index) :=
              mul_le_mul_of_nonneg_left hweightDecay hC
            have htransport :
                ZetaPrimePowerIndex.weight index *
                    (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
                  D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
              calc
                ZetaPrimePowerIndex.weight index *
                    (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) =
                    C * (ZetaPrimePowerIndex.weight index *
                      ZetaPrimePowerIndex.polynomialHeightDecay k index) := by
                  exact Eq.trans
                    ((mul_assoc (ZetaPrimePowerIndex.weight index) C
                      (ZetaPrimePowerIndex.polynomialHeightDecay k index)).symm)
                    (congrArg (fun value : ℝ => value *
                      ZetaPrimePowerIndex.polynomialHeightDecay k index)
                      (mul_comm (ZetaPrimePowerIndex.weight index) C))
                _ ≤ C * (A * ZetaPrimePowerIndex.polynomialHeightDecay l index) :=
                  hmulDecay
                _ = D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
                  exact (mul_assoc C A
                    (ZetaPrimePowerIndex.polynomialHeightDecay l index)).symm
            have hsample :
                completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
                    index f =
                  ZetaPrimePowerIndex.weight index *
                    completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
                      index f :=
              completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_eq_weight_mul_density
                index f
            have hnorm : ‖completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
                    index f‖ =
                completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
                    index f :=
              primeCenterSampling_real_norm_eq_self_of_nonnegative _ hweightedNonnegative
            exact Eq.subst (motive := fun value : ℝ =>
                value ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
              hnorm.symm
              (Eq.subst (motive := fun value : ℝ =>
                value ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
                hsample.symm
                (le_trans
                  (mul_le_mul_of_nonneg_left hdensityValue hweight)
                  htransport))
          exact ⟨D, l, hD, hbound⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
