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

/-- The explicit prime-power weight in the completed formula normalization. -/
def zetaCompletedExplicitFormulaPrimeWeight (p n : ℕ) : ℝ :=
  if _hp : Nat.Prime p then
    if _hn : n ≠ 0 then
      Real.log p / Real.sqrt (p ^ n)
    else
      0
  else
    0

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
  refine ⟨Cpos * Cneg, kpos, ?_, ?_⟩
  · exact mul_nonneg hCpos hCneg
  · intro ι
    let A : ℝ :=
      ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖
    let B : ℝ :=
      ‖star
        (zetaCompletedExplicitFormulaPhi f
          (-(ZetaPrimePowerIndex.center ι : ℂ)))‖
    let Dpos : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kpos ι
    let Dneg : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kneg ι
    have hA_nonneg : 0 ≤ A := norm_nonneg _
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
    have hDneg_nonneg : 0 ≤ Dneg :=
      ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative kneg ι
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
          exact mul_assoc Cneg Cpos Dpos
        _ = (Cpos * Cneg) * Dpos := by
          exact congrArg (fun x : ℝ => x * Dpos) (mul_comm Cneg Cpos)
    exact hmul_bounds.trans (hright_shrink.trans (le_of_eq halgebra))

/-- Positive prime-power spectral majorant: Laplace transform decay at prime-power centers.

The Laplace transform of an admissible test function φ = f.toZetaTestFunction',
when evaluated at prime-power center z = n·log(p), exhibits polynomial-height decay
in the index ι = (p, n).

This is constructed from the rapid-decay property of the test function itself. The
witness (C, k) is built by bounding the Laplace integral using the test function's
decay in the exponential weight. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_positive_spectralMajorant_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction'
              (ZetaPrimePowerIndex.center ι)‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  let I := ZetaPaleyWienerSupportInterval.mk f 0
  let a : ℝ := 0
  let b : ℝ := 1
  let hstrip : ∀ ι : ZetaPrimePowerIndex,
      zetaPaleyWienerInVerticalStrip a b (ZetaPrimePowerIndex.center ι : ℂ) :=
    fun ι => ⟨Complex.ofReal_re _, Complex.ofReal_re _⟩
  let henv : ∀ ι : ZetaPrimePowerIndex,
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' (ZetaPrimePowerIndex.center ι : ℂ)‖ ≤
        zetaPaleyWienerZeroOrderEnvelope f I a b :=
    fun ι => zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope f I a b
      (ZetaPrimePowerIndex.center ι : ℂ) (hstrip ι)
  let C : ℝ := zetaPaleyWienerZeroOrderEnvelope f I a b + 1
  let k : ℕ := 0
  let hC_nonneg : 0 ≤ C :=
    add_nonneg (zetaPaleyWienerZeroOrderEnvelope_nonnegative f I a b) one_nonneg
  let env : ℝ := zetaPaleyWienerZeroOrderEnvelope f I a b
  let h_env_add : env + 0 = env := add_zero env
  let h_env_le : env ≤ env + 1 := le_add_of_nonneg_right one_nonneg
  let h_env_eq_C : env + 1 = C := Eq.refl C
  let h_mul_one : C * 1 = C := mul_one C
  let h_decay : ∀ ι, ZetaPrimePowerIndex.polynomialHeightDecay k ι = 1 :=
    fun ι => Eq.refl 1
  exact ⟨C, k, hC_nonneg, fun ι =>
    calc
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' (ZetaPrimePowerIndex.center ι : ℂ)‖ ≤
          env := henv ι
      _ = env + 0 := (h_env_add).symm
      _ ≤ env + 1 := h_env_le
      _ = C := h_env_eq_C
      _ = C * 1 := (h_mul_one).symm
      _ = C * ZetaPrimePowerIndex.polynomialHeightDecay k ι :=
        congrArg (fun x : ℝ => C * x) (h_decay ι).symm⟩

/-- Positive spectral majorant of the completed transform at prime-power centers. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_positive_spectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f
              (ZetaPrimePowerIndex.center ι)‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, hC, hbound⟩ :=
    zetaCompletedExplicitFormulaPhi_primePower_positive_spectralMajorant_source f
  refine ⟨C, k, hC, ?_⟩
  intro ι
  have hphi :
      zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction'
          (ZetaPrimePowerIndex.center ι) := by
    rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k ι)
    hphi.symm
    (hbound ι)

/-- Reflected negative spectral majorant of the completed transform at
prime-power centers. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_negative_spectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖star
            (zetaCompletedExplicitFormulaPhi f
              (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match
    zetaCompletedExplicitFormulaPhi_primePower_positive_spectralMajorant
      (zetaAdmissibleDagger f)
  with
  | ⟨C, k, hC_nonneg, hpos⟩ =>
      exact
        ⟨C, k, hC_nonneg,
          fun ι =>
            let z : ℂ := (ZetaPrimePowerIndex.center ι : ℂ)
            have hstar_z : star z = z := by
              unfold z
              exact Complex.conj_ofReal (ZetaPrimePowerIndex.center ι)
            have harg : -star z = -z := by
              exact congrArg Neg.neg hstar_z
            have hdagger :
                zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z =
                  star (zetaCompletedExplicitFormulaPhi f (-z)) := by
              calc
                zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z =
                    star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
                  exact zetaCompletedExplicitFormulaPhi_dagger f z
                _ = star (zetaCompletedExplicitFormulaPhi f (-z)) := by
                  exact congrArg
                    (fun w : ℂ => star (zetaCompletedExplicitFormulaPhi f w))
                    harg
            have hnorm :
                ‖star (zetaCompletedExplicitFormulaPhi f (-z))‖ =
                  ‖zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z‖ := by
              exact congrArg norm hdagger.symm
            Eq.subst
              (motive := fun r : ℝ =>
                r ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k ι)
              hnorm.symm
              (hpos ι)⟩

/-- Two-sided spectral majorant of the completed transform at prime-power centers,
assembled from the two one-sided estimates. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_twoSided_spectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        (∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f
              (ZetaPrimePowerIndex.center ι)‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) ∧
        (∀ ι : ZetaPrimePowerIndex,
          ‖star
            (zetaCompletedExplicitFormulaPhi f
              (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) := by
  match zetaCompletedExplicitFormulaPhi_primePower_positive_spectralMajorant f with
  | ⟨Cpos, kpos, hCpos_nonneg, hpos⟩ =>
      match zetaCompletedExplicitFormulaPhi_primePower_negative_spectralMajorant f with
      | ⟨Cneg, kneg, hCneg_nonneg, hneg⟩ =>
          let C : ℝ := max Cpos Cneg
          let k : ℕ := min kpos kneg
          have hC_nonneg : 0 ≤ C := by
            unfold C
            exact le_max_of_le_left hCpos_nonneg
          have hCpos_le_C : Cpos ≤ C := by
            unfold C
            exact le_max_left Cpos Cneg
          have hCneg_le_C : Cneg ≤ C := by
            unfold C
            exact le_max_right Cpos Cneg
          have hk_le_kpos : k ≤ kpos := by
            unfold k
            exact min_le_left kpos kneg
          have hk_le_kneg : k ≤ kneg := by
            unfold k
            exact min_le_right kpos kneg
          have hpos_common :
              ∀ ι : ZetaPrimePowerIndex,
                ‖zetaCompletedExplicitFormulaPhi f
                    (ZetaPrimePowerIndex.center ι)‖ ≤
                  C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
            intro ι
            let Dpos : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kpos ι
            let D : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay k ι
            have hDpos_nonneg : 0 ≤ Dpos :=
              ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative kpos ι
            have hDpos_le_D : Dpos ≤ D :=
              ZetaPrimePowerIndex.polynomialHeightDecay_le_of_le hk_le_kpos ι
            have hscale : Cpos * Dpos ≤ C * D := by
              have hCposDpos_le_CDpos : Cpos * Dpos ≤ C * Dpos :=
                mul_le_mul_of_nonneg_right hCpos_le_C hDpos_nonneg
              have hCDpos_le_CD : C * Dpos ≤ C * D :=
                mul_le_mul_of_nonneg_left hDpos_le_D hC_nonneg
              exact hCposDpos_le_CDpos.trans hCDpos_le_CD
            exact (hpos ι).trans hscale
          have hneg_common :
              ∀ ι : ZetaPrimePowerIndex,
                ‖star
                  (zetaCompletedExplicitFormulaPhi f
                    (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
                  C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
            intro ι
            let Dneg : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kneg ι
            let D : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay k ι
            have hDneg_nonneg : 0 ≤ Dneg :=
              ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative kneg ι
            have hDneg_le_D : Dneg ≤ D :=
              ZetaPrimePowerIndex.polynomialHeightDecay_le_of_le hk_le_kneg ι
            have hscale : Cneg * Dneg ≤ C * D := by
              have hCnegDneg_le_CDneg : Cneg * Dneg ≤ C * Dneg :=
                mul_le_mul_of_nonneg_right hCneg_le_C hDneg_nonneg
              have hCDneg_le_CD : C * Dneg ≤ C * D :=
                mul_le_mul_of_nonneg_left hDneg_le_D hC_nonneg
              exact hCnegDneg_le_CDneg.trans hCDneg_le_CD
            exact (hneg ι).trans hscale
          exact ⟨C, k, hC_nonneg, hpos_common, hneg_common⟩

/-- Positive one-sided spectral majorant at prime-power centers. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_positive_realAxisSpectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f
              (ZetaPrimePowerIndex.center ι)‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match zetaCompletedExplicitFormulaPhi_primePower_twoSided_spectralMajorant f with
  | ⟨C, k, hC, hpositive, _hnegative⟩ =>
      exact ⟨C, k, hC, hpositive⟩

/-- Reflected negative one-sided spectral majorant at prime-power centers. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_negative_realAxisSpectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖star
            (zetaCompletedExplicitFormulaPhi f
              (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match zetaCompletedExplicitFormulaPhi_primePower_twoSided_spectralMajorant f with
  | ⟨C, k, hC, _hpositive, hnegative⟩ =>
      exact ⟨C, k, hC, hnegative⟩

/-- Prime-power spectral seed-pair summability majorant.

This is the spectral/Laplace prime sample estimate after the prime-channel
transport owner has supplied one-sided polynomial-height majorants. -/
theorem zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match zetaCompletedExplicitFormulaPhi_primePower_positive_realAxisSpectralMajorant f with
  | ⟨Cpos, kpos, hCpos, hpos⟩ =>
      match zetaCompletedExplicitFormulaPhi_primePower_negative_realAxisSpectralMajorant f with
      | ⟨Cneg, kneg, hCneg, hneg⟩ =>
          exact
            zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant_of_oneSided
              f Cpos Cneg kpos kneg hCpos hCneg hpos hneg

/-- Spectral seed-pair majorant at prime-power centers, in the real norm shape needed
by the paired seed estimate. -/
theorem zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant'
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
            ‖star
              (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, _hC, hbound⟩ :=
    zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant
      f
  exact ⟨C, k, hbound⟩

/-- Prime-power weights are absorbed into the seed-pair rapid-decay polynomial height. -/
theorem zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_from_seedPairDecay
    (f : ZetaAdmissibleFunction)
    (hseed :
      ∃ C : ℝ, ∃ k : ℕ,
        0 ≤ C ∧
          ∀ ι : ZetaPrimePowerIndex,
            ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
                ‖star
                  (zetaCompletedExplicitFormulaPhi f
                    (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
              C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖(ZetaPrimePowerIndex.weight ι : ℂ)‖ *
            (‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                  (-(ZetaPrimePowerIndex.center ι : ℂ)))‖) ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, hC_nonneg, hseed_bound⟩ := hseed
  obtain ⟨A, l, hA_nonneg, _hkl, hweight_bound⟩ :=
    ZetaPrimePowerIndex.weight_norm_mul_polynomialHeightDecay_le_shift k
  refine ⟨C * A, l, ?_⟩
  intro ι
  let W : ℝ := ‖(ZetaPrimePowerIndex.weight ι : ℂ)‖
  let P : ℝ :=
    ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
      ‖star
        (zetaCompletedExplicitFormulaPhi f
          (-(ZetaPrimePowerIndex.center ι : ℂ)))‖
  let Dk : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay k ι
  let Dl : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay l ι
  have hW_nonneg : 0 ≤ W := norm_nonneg _
  have hseed_ι : P ≤ C * Dk := hseed_bound ι
  have hmul_seed : W * P ≤ W * (C * Dk) :=
    mul_le_mul_of_nonneg_left hseed_ι hW_nonneg
  have hcomm : W * (C * Dk) = C * (W * Dk) := by
    calc
      W * (C * Dk) = (W * C) * Dk := by
        exact (mul_assoc W C Dk).symm
      _ = (C * W) * Dk := by
        exact congrArg (fun x : ℝ => x * Dk) (mul_comm W C)
      _ = C * (W * Dk) := by
        exact mul_assoc C W Dk
  have hweight_ι : W * Dk ≤ A * Dl := hweight_bound ι
  have hscaled : C * (W * Dk) ≤ C * (A * Dl) :=
    mul_le_mul_of_nonneg_left hweight_ι hC_nonneg
  have htarget : C * (A * Dl) = C * A * Dl := by
    exact (mul_assoc C A Dl).symm
  exact hmul_seed.trans
    ((le_of_eq hcomm).trans
      (hscaled.trans (le_of_eq htarget)))

/-- Real-norm Paley-Wiener majorant for the weighted seed-pair prime-power coordinate. -/
theorem zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_le_polynomialHeightDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖(ZetaPrimePowerIndex.weight ι : ℂ)‖ *
            (‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                  (-(ZetaPrimePowerIndex.center ι : ℂ)))‖) ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_from_seedPairDecay
      f
      (zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant
        f)

/-- Paley-Wiener prime-power seed-pair estimate for the weighted oriented cross coordinate. -/
theorem zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_norm_le_polynomialHeightDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖(ZetaPrimePowerIndex.weight ι : ℂ) *
          (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
            star
              (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ))))‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, hmajorant⟩ :=
    zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_le_polynomialHeightDecay
      f
  refine ⟨C, k, ?_⟩
  intro ι
  let W : ℂ := (ZetaPrimePowerIndex.weight ι : ℂ)
  let A : ℂ := zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)
  let B : ℂ :=
    star
      (zetaCompletedExplicitFormulaPhi f
        (-(ZetaPrimePowerIndex.center ι : ℂ)))
  have hnorm :
      ‖W * (A * B)‖ = ‖W‖ * (‖A‖ * ‖B‖) := by
    calc
      ‖W * (A * B)‖ = ‖W‖ * ‖A * B‖ := by
        exact norm_mul W (A * B)
      _ = ‖W‖ * (‖A‖ * ‖B‖) := by
        exact congrArg (fun x : ℝ => ‖W‖ * x) (norm_mul A B)
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k ι)
    hnorm.symm
    (hmajorant ι)

/-- The oriented autocorrelation cross coordinate has a polynomial-height majorant. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_norm_le_polynomialHeightDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_norm_le_polynomialHeightDecay
      f

/-- The oriented autocorrelation cross coordinate family is summable over raw prime-power
indices. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) := by
  obtain ⟨C, k, hbound⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_norm_le_polynomialHeightDecay
      f
  have hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :=
    ZetaPrimePowerIndex.summable_const_mul_polynomialHeightDecay C k
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        C * ZetaPrimePowerIndex.polynomialHeightDecay k ι)
      hmajorant
      hbound

/-- The opposite oriented autocorrelation cross coordinate family is summable over raw
prime-power indices. -/
theorem zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) := by
  have horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hstar :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    horiented.star
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) =
      (fun ι : ZetaPrimePowerIndex =>
        star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
    funext ι
    exact
      (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        ι f).symm
  exact Eq.subst
    (motive := fun u : ZetaPrimePowerIndex → ℂ => Summable u)
    hpoint.symm
    hstar


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
