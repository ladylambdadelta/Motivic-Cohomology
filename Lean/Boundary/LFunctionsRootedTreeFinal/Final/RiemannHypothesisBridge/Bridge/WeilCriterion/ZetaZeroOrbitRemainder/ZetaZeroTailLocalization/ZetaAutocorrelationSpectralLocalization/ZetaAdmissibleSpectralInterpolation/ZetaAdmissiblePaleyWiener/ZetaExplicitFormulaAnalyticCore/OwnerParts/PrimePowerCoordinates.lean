import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base

/-!
# Boundary explicit-formula analytic core

This file fixes the analytic vocabulary used by the completed Guinand--Weil
route:

* the involution `f†`,
* the autocorrelation kernel `g_f`,
* the spectral transform `Φ_f`,
* the completed zeta logarithmic derivative integrand,
* and the named prime / archimedean / correction pieces.

The file is intentionally definitional. The contour, residue, and decay
arguments will consume these owner-level objects.
-/

/-! This owner part contains the prime-power coordinates and spectral majorants. -/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The finite prime-power window used by the current completed explicit-formula core. -/
def zetaCompletedExplicitFormulaPrimeSupport : Finset (ℕ × ℕ) :=
  Finset.product
    (Finset.range (Nat.ceil (Real.exp 0) + 1))
    (Finset.range (Nat.ceil (Real.exp 0) + 1))

/-- Finite display presentation for packet-level prime terms.

This is not the owner completed prime distribution; the public prime contribution below is
the completed prime-power object. -/
noncomputable def zetaCompletedExplicitFormulaPrimeFinitePresentation
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
      (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) +
        star (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2))))

/-- One completed prime-power spectral-sample coordinate in the contour-side presentation. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
    -((ZetaPrimePowerIndex.weight ι : ℂ) *
      (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) +
        star (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι))))

/-- The paired seed-transform prime-power coordinate obtained by unfolding the
autocorrelation spectral sample. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
    -((ZetaPrimePowerIndex.weight ι : ℂ) *
      ((zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
          star
            (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ)))) +
        star
          (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
            star
              (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))))))

/-- The oriented seed-transform cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.weight ι : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
      star
        (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))))

/-- The opposite oriented seed-transform cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.weight ι : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ)) *
      star (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)))

/-- The symmetrized seed-transform cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
    star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)

/-- Rectangular finite-window sum of the oriented autocorrelation cross coordinates. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.box N,
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f

/-- Rectangular finite-window sum of the opposite oriented autocorrelation cross coordinates. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossBoxSum
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.box N,
    zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f

/-- The real part of one rectangular oriented-cross prime-power window. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)

/-- The paired spectral sample is the negative symmetrized cross coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f =
      -zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f := by
  let W : ℂ := (ZetaPrimePowerIndex.weight ι : ℂ)
  let A : ℂ := zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)
  let B : ℂ := zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))
  have hstarW : star W = W := by
    unfold W
    exact Complex.conj_ofReal (ZetaPrimePowerIndex.weight ι)
  unfold zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
  change -(W * (A * star B + star (A * star B))) = -(W * (A * star B) + star (W * (A * star B)))
  have hstar :
      star (W * (A * star B)) = W * star (A * star B) := by
    calc
      star (W * (A * star B)) = star (A * star B) * star W := by
        exact star_mul W (A * star B)
      _ = star (A * star B) * W := by
        exact congrArg (fun z : ℂ => star (A * star B) * z) hstarW
      _ = W * star (A * star B) := by
        exact mul_comm (star (A * star B)) W
  exact congrArg Neg.neg
    (calc
      W * (A * star B + star (A * star B)) =
          W * (A * star B) + W * star (A * star B) := by
        exact mul_add W (A * star B) (star (A * star B))
      _ = W * (A * star B) + star (W * (A * star B)) := by
        exact congrArg (fun z : ℂ => W * (A * star B) + z) hstar.symm)

/-- Conjugating an oriented cross coordinate gives the opposite oriented face. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f := by
  let W : ℂ := (ZetaPrimePowerIndex.weight ι : ℂ)
  let A : ℂ := zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)
  let B : ℂ := zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))
  have hstarW : star W = W := by
    unfold W
    exact Complex.conj_ofReal (ZetaPrimePowerIndex.weight ι)
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
  change star (W * (A * star B)) = W * (B * star A)
  calc
    star (W * (A * star B)) = star (A * star B) * star W := by
      exact star_mul W (A * star B)
    _ = star (A * star B) * W := by
      exact congrArg (fun z : ℂ => star (A * star B) * z) hstarW
    _ = (star (star B) * star A) * W := by
      exact congrArg (fun z : ℂ => z * W) (star_mul A (star B))
    _ = (B * star A) * W := by
      exact congrArg (fun z : ℂ => (z * star A) * W) (star_star B)
    _ = W * (B * star A) := by
      exact mul_comm (B * star A) W

/-- Autocorrelation prime-power spectral coordinates unfold to paired seed-transform
coordinates. -/
theorem zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f := by
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate
  exact congrArg
    (fun z : ℂ =>
      -((ZetaPrimePowerIndex.weight ι : ℂ) * (z + star z)))
    (zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
      f (ZetaPrimePowerIndex.center ι))

/-- The completed prime-power spectral-sample presentation indexed by genuine prime-power
coordinates.  This is the Laplace/contour-side presentation and is deliberately not the owner
real prime distribution: the final explicit-formula prime channel samples the completed
time/log-side boundary value. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' ι : ZetaPrimePowerIndex,
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι f

/-- Seed-pair real-axis spectral majorant assembled from the two one-sided
prime-power-center spectral majorants. -/
theorem zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant_of_oneSided
    (f : ZetaAdmissibleFunction)
    (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hCpos : 0 ≤ Cpos) (hCneg : 0 ≤ Cneg)
    (hpos :
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ ≤
          Cpos * ZetaPrimePowerIndex.polynomialHeightDecay kpos ι)
    (hneg :
      ∀ ι : ZetaPrimePowerIndex,
        ‖star
          (zetaCompletedExplicitFormulaPhi f
            (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
          Cneg * ZetaPrimePowerIndex.polynomialHeightDecay kneg ι) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                  (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact Exists.intro (Cpos * Cneg)
    (Exists.intro kpos
      (And.intro
        (mul_nonneg hCpos hCneg)
        (fun ι =>
          let A : ℝ :=
            ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖
          let B : ℝ :=
            ‖star
              (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ)))‖
          let Dpos : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kpos ι
          let Dneg : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kneg ι
          have hB_nonneg : 0 ≤ B := norm_nonneg _
          have hDpos_nonneg : 0 ≤ Dpos :=
            ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative kpos ι
          have hDneg_le_one : Dneg ≤ 1 :=
            ZetaPrimePowerIndex.polynomialHeightDecay_le_one kneg ι
          have hpos_ι : A ≤ Cpos * Dpos := hpos ι
          have hneg_ι : B ≤ Cneg * Dneg := hneg ι
          have hCposDpos_nonneg : 0 ≤ Cpos * Dpos :=
            mul_nonneg hCpos hDpos_nonneg
          have hmul_bounds : A * B ≤ (Cpos * Dpos) * (Cneg * Dneg) :=
            mul_le_mul hpos_ι hneg_ι hB_nonneg hCposDpos_nonneg
          have hCnegDneg_le_Cneg : Cneg * Dneg ≤ Cneg * 1 :=
            mul_le_mul_of_nonneg_left hDneg_le_one hCneg
          have hright_shrink :
              (Cpos * Dpos) * (Cneg * Dneg) ≤ (Cpos * Dpos) * (Cneg * 1) :=
            mul_le_mul_of_nonneg_left hCnegDneg_le_Cneg hCposDpos_nonneg
          have halgebra :
              (Cpos * Dpos) * (Cneg * 1) = (Cpos * Cneg) * Dpos := by
            calc
              (Cpos * Dpos) * (Cneg * 1) = (Cpos * Dpos) * Cneg := by
                exact congrArg (fun x : ℝ => (Cpos * Dpos) * x) (mul_one Cneg)
              _ = Cneg * (Cpos * Dpos) := by
                exact mul_comm (Cpos * Dpos) Cneg
              _ = (Cneg * Cpos) * Dpos := by
                exact (mul_assoc Cneg Cpos Dpos).symm
              _ = (Cpos * Cneg) * Dpos := by
                exact congrArg (fun x : ℝ => x * Dpos) (mul_comm Cneg Cpos)
          hmul_bounds.trans (hright_shrink.trans (le_of_eq halgebra)))))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
