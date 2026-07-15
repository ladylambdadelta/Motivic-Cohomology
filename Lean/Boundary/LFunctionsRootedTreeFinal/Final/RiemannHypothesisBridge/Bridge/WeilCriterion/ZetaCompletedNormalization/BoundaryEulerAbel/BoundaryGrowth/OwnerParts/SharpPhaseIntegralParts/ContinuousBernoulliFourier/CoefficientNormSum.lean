import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ModeSeriesSummability

/-!
# Bilateral mass of the second-Bernoulli Fourier coefficients
-/

namespace Boundary
namespace LFunctions

noncomputable section

local notation "π" => Real.pi

/-- On a nonnegative integral index, the complex coefficient norm is the real
reciprocal square. -/
theorem norm_centeredQuadraticPrimitive_fourier_coefficient_natCast
    (n : ℕ) :
    ‖(1 : ℂ) / ((n : ℤ) : ℂ) ^ (2 : ℕ)‖ =
      (1 : ℝ) / (n : ℝ) ^ (2 : ℕ) := by
  have hcast : (((n : ℤ) : ℂ)) = (n : ℂ) :=
    Int.cast_natCast n
  have hnormCast : ‖(n : ℂ)‖ = (n : ℝ) :=
    Complex.norm_natCast n
  exact Eq.trans
    (norm_div (1 : ℂ) (((n : ℤ) : ℂ) ^ (2 : ℕ)))
    (Eq.trans
      (congrArg₂ Div.div norm_one
        (norm_pow (((n : ℤ) : ℂ)) (2 : ℕ)))
      (Eq.trans
        (congrArg
          (fun r : ℝ => (1 : ℝ) / r ^ (2 : ℕ))
          (Eq.trans (congrArg Norm.norm hcast) hnormCast))
        rfl))

/-- On a negative-successor integral index, the coefficient norm is the real
reciprocal square of the corresponding positive integer. -/
theorem norm_centeredQuadraticPrimitive_fourier_coefficient_negSucc
    (n : ℕ) :
    ‖(1 : ℂ) / ((Int.negSucc n : ℤ) : ℂ) ^ (2 : ℕ)‖ =
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
  have hnegSucc : Int.negSucc n = -((n + 1 : ℕ) : ℤ) :=
    rfl
  have hnormCastRaw :
      ‖((Int.negSucc n : ℤ) : ℂ)‖ =
        |((Int.negSucc n : ℤ) : ℝ)| :=
    Complex.norm_intCast (Int.negSucc n)
  have hcastReal :
      ((Int.negSucc n : ℤ) : ℝ) = -(((n + 1 : ℕ) : ℝ)) := by
    exact Eq.trans
      (congrArg (fun z : ℤ => (z : ℝ)) hnegSucc)
      (Eq.trans (Int.cast_neg _) (congrArg Neg.neg (Int.cast_natCast _)))
  have hpositive : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) :=
    Nat.cast_nonneg (n + 1)
  have habs :
      |((Int.negSucc n : ℤ) : ℝ)| = (((n + 1 : ℕ) : ℝ)) :=
    Eq.trans
      (congrArg abs hcastReal)
      (Eq.trans (abs_neg _) (abs_of_nonneg hpositive))
  have hnormCast :
      ‖((Int.negSucc n : ℤ) : ℂ)‖ = (((n + 1 : ℕ) : ℝ)) :=
    Eq.trans hnormCastRaw habs
  exact Eq.trans
    (norm_div (1 : ℂ) (((Int.negSucc n : ℤ) : ℂ) ^ (2 : ℕ)))
    (Eq.trans
      (congrArg₂ Div.div norm_one
        (norm_pow (((Int.negSucc n : ℤ) : ℂ)) (2 : ℕ)))
      (congrArg (fun r : ℝ => (1 : ℝ) / r ^ (2 : ℕ)) hnormCast))

/-- The nonnegative half of the bilateral coefficient norms has Basel mass
`π²/6`; its zero term vanishes automatically. -/
theorem hasSum_centeredQuadraticPrimitive_fourier_coefficient_norm_natCast :
    HasSum
      (fun n : ℕ => ‖(1 : ℂ) / ((n : ℤ) : ℂ) ^ (2 : ℕ)‖)
      (π ^ (2 : ℕ) / 6) := by
  have hterms :
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) =
        (fun n : ℕ => ‖(1 : ℂ) / ((n : ℤ) : ℂ) ^ (2 : ℕ)‖) := by
    funext n
    exact
      (norm_centeredQuadraticPrimitive_fourier_coefficient_natCast n).symm
  exact Eq.subst
    (motive := fun terms : ℕ → ℝ => HasSum terms (π ^ (2 : ℕ) / 6))
    hterms
    hasSum_zeta_two

/-- The negative-successor half of the bilateral coefficient norms also has
Basel mass `π²/6`. -/
theorem hasSum_centeredQuadraticPrimitive_fourier_coefficient_norm_negSucc :
    HasSum
      (fun n : ℕ =>
        ‖(1 : ℂ) / ((Int.negSucc n : ℤ) : ℂ) ^ (2 : ℕ)‖)
      (π ^ (2 : ℕ) / 6) := by
  let zetaTerm : ℕ → ℝ :=
    fun n => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)
  have hzero : zetaTerm 0 = 0 := by
    have hcast : ((0 : ℕ) : ℝ) = 0 :=
      Nat.cast_zero
    have hpower : (0 : ℝ) ^ (2 : ℕ) = 0 :=
      zero_pow (OfNat.ofNat_ne_zero 2)
    exact Eq.trans
      (congrArg (fun value : ℝ => (1 : ℝ) / value ^ (2 : ℕ)) hcast)
      (Eq.trans
        (congrArg (fun value : ℝ => (1 : ℝ) / value) hpower)
        (div_zero 1))
  have hshifted :
      HasSum (fun n : ℕ => zetaTerm (n + 1)) (π ^ (2 : ℕ) / 6) := by
    have hraw :
        HasSum (fun n : ℕ => zetaTerm (n + 1))
          (π ^ (2 : ℕ) / 6 - ∑ i ∈ Finset.range 1, zetaTerm i) :=
      (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    have hfinite : (∑ i ∈ Finset.range 1, zetaTerm i) = 0 := by
      have hrange : Finset.range 1 = {0} :=
        Finset.range_one
      exact Eq.trans
        (congrArg (fun s : Finset ℕ => ∑ i ∈ s, zetaTerm i) hrange)
        (Eq.trans (Finset.sum_singleton zetaTerm 0) hzero)
    have hvalue :
        π ^ (2 : ℕ) / 6 - ∑ i ∈ Finset.range 1, zetaTerm i =
          π ^ (2 : ℕ) / 6 :=
      Eq.trans
        (congrArg (fun r : ℝ => π ^ (2 : ℕ) / 6 - r) hfinite)
        (sub_zero _)
    exact Eq.subst
      (motive := fun value : ℝ =>
        HasSum (fun n : ℕ => zetaTerm (n + 1)) value)
      hvalue
      hraw
  have hterms :
      (fun n : ℕ => zetaTerm (n + 1)) =
        (fun n : ℕ =>
          ‖(1 : ℂ) / ((Int.negSucc n : ℤ) : ℂ) ^ (2 : ℕ)‖) := by
    funext n
    exact
      (norm_centeredQuadraticPrimitive_fourier_coefficient_negSucc n).symm
  exact Eq.subst
    (motive := fun terms : ℕ → ℝ => HasSum terms (π ^ (2 : ℕ) / 6))
    hterms
    hshifted

/-- The bilateral coefficient-norm mass is the sum of the two Basel halves. -/
theorem hasSum_centeredQuadraticPrimitive_fourier_coefficient_norm_int :
    HasSum
      (fun m : ℤ => ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖)
      (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6) := by
  exact HasSum.of_nat_of_neg_add_one
    hasSum_centeredQuadraticPrimitive_fourier_coefficient_norm_natCast
    hasSum_centeredQuadraticPrimitive_fourier_coefficient_norm_negSucc

/-- Exact `tsum` value of the bilateral coefficient norms. -/
theorem tsum_centeredQuadraticPrimitive_fourier_coefficient_norm_int :
    (∑' m : ℤ, ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖) =
      π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6 :=
  hasSum_centeredQuadraticPrimitive_fourier_coefficient_norm_int.tsum_eq

/-- The norm of the coefficient-weighted integrated mode series is bounded by
four times the bilateral Basel mass. -/
theorem norm_tsum_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_le
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    ‖∑' m : ℤ,
        boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
          t a L m‖ ≤
      4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6) := by
  let weighted :=
    boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral t a L
  let coefficientNorm : ℤ → ℝ :=
    fun m => ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖
  have hweighted : Summable weighted :=
    summable_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
      t ha hL
  have hnormTsum :
      ‖∑' m : ℤ, weighted m‖ ≤ ∑' m : ℤ, ‖weighted m‖ :=
    norm_tsum_le_tsum_norm hweighted.norm
  have hmajorant :
      Summable (fun m : ℤ => 4 * coefficientNorm m) :=
    Summable.mul_left 4
      summable_centeredQuadraticPrimitive_fourier_coefficient_norm
  have hnormSummable : Summable (fun m : ℤ => ‖weighted m‖) :=
    hweighted.norm
  have hpointwise :
      ∀ m : ℤ, ‖weighted m‖ ≤ 4 * coefficientNorm m :=
    norm_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_le
      t ha hL
  have htsumMono :
      (∑' m : ℤ, ‖weighted m‖) ≤
        ∑' m : ℤ, 4 * coefficientNorm m :=
    tsum_le_tsum hpointwise hnormSummable hmajorant
  have hmulTsum :
      (∑' m : ℤ, 4 * coefficientNorm m) =
        4 * ∑' m : ℤ, coefficientNorm m :=
    tsum_mul_left
  have hcoefficientTsum :
      (∑' m : ℤ, coefficientNorm m) =
        π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6 :=
    tsum_centeredQuadraticPrimitive_fourier_coefficient_norm_int
  exact le_trans hnormTsum
    (le_trans htsumMono
      (le_of_eq
        (Eq.trans hmulTsum
          (congrArg (fun r : ℝ => 4 * r) hcoefficientTsum))))

end
end LFunctions
end Boundary
