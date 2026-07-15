import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveGapCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerSpecializations
import Mathlib.Data.PNat.Equiv

/-!
# Natural-number reindexing of the enhanced positive ray

Positive integer Fourier modes are canonically indexed by natural numbers:
the natural index `n` represents mode `n + 1`.  Under this equivalence the
endpoint-enhanced logarithmic phase gap is exactly an affine shifted gap.
This owner records the equivalence and all coercion identities explicitly so
the shifted reciprocal-power series can be consumed without cast automation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePositiveIntegerToPNat
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) : ℕ+ :=
  ⟨Int.toNat (m : ℤ), Int.lt_toNat.mpr m.property⟩

def Complex.logarithmicPhasePNatToPositiveInteger
    (n : ℕ+) : Complex.logarithmicPhasePoissonPositiveTailModes :=
  ⟨((n : ℕ) : ℤ), Int.natCast_pos.mpr n.property⟩

theorem Complex.logarithmicPhasePositiveIntegerToPNat_value
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    (Complex.logarithmicPhasePositiveIntegerToPNat m : ℕ) =
      Int.toNat (m : ℤ) := by
  exact rfl

theorem Complex.logarithmicPhasePNatToPositiveInteger_value
    (n : ℕ+) :
    ((Complex.logarithmicPhasePNatToPositiveInteger n :
      Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) =
      ((n : ℕ) : ℤ) := by
  exact rfl

theorem Complex.logarithmicPhasePositiveIntegerToPNat_leftInverse
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhasePNatToPositiveInteger
      (Complex.logarithmicPhasePositiveIntegerToPNat m) = m := by
  have hnonneg : 0 ≤ (m : ℤ) := le_of_lt m.property
  have hcast : ((Int.toNat (m : ℤ) : ℕ) : ℤ) = (m : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  exact Subtype.ext hcast

theorem Complex.logarithmicPhasePositiveIntegerToPNat_rightInverse
    (n : ℕ+) :
    Complex.logarithmicPhasePositiveIntegerToPNat
      (Complex.logarithmicPhasePNatToPositiveInteger n) = n := by
  have htoNat : Int.toNat ((n : ℕ) : ℤ) = (n : ℕ) :=
    Int.toNat_natCast (n : ℕ)
  exact Subtype.ext htoNat

def Complex.logarithmicPhasePositiveIntegerEquivPNat :
    Complex.logarithmicPhasePoissonPositiveTailModes ≃ ℕ+ where
  toFun := Complex.logarithmicPhasePositiveIntegerToPNat
  invFun := Complex.logarithmicPhasePNatToPositiveInteger
  left_inv := Complex.logarithmicPhasePositiveIntegerToPNat_leftInverse
  right_inv := Complex.logarithmicPhasePositiveIntegerToPNat_rightInverse

def Complex.logarithmicPhasePositiveIntegerEquivNat :
    Complex.logarithmicPhasePoissonPositiveTailModes ≃ ℕ :=
  Complex.logarithmicPhasePositiveIntegerEquivPNat.trans Equiv.pnatEquivNat

theorem Complex.logarithmicPhasePositiveIntegerEquivNat_apply
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhasePositiveIntegerEquivNat m =
      (Complex.logarithmicPhasePositiveIntegerToPNat m).natPred := by
  exact rfl

theorem Complex.logarithmicPhasePositiveIntegerEquivNat_symm_value
    (n : ℕ) :
    (((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n :
      Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) =
      ((n + 1 : ℕ) : ℤ) := by
  have hpnat : (Nat.succPNat n : ℕ) = n + 1 :=
    Nat.succPNat_coe n
  exact congrArg (fun value : ℕ => (value : ℤ)) hpnat

theorem Complex.logarithmicPhasePositiveIntegerEquivNat_symm_real_value
    (n : ℕ) :
    ((((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n :
      Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) : ℝ) =
      (n : ℝ) + 1 := by
  have hint :=
    Complex.logarithmicPhasePositiveIntegerEquivNat_symm_value n
  have hcast := congrArg (fun value : ℤ => (value : ℝ)) hint
  have hnatCast : (((n + 1 : ℕ) : ℤ) : ℝ) = (n : ℝ) + 1 := by
    have hadd : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + ((1 : ℕ) : ℝ) :=
      Nat.cast_add n 1
    have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
    have hnormalized : (n : ℝ) + ((1 : ℕ) : ℝ) = (n : ℝ) + 1 :=
      congrArg (fun value : ℝ => (n : ℝ) + value) hone
    exact Eq.trans (Int.cast_natCast (n + 1))
      (Eq.trans hadd hnormalized)
  exact Eq.trans hcast hnatCast

def Complex.logarithmicPhaseEnhancedPositiveShift
    (t : ℝ) (b : ℤ) : ℝ :=
  ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b

def Complex.logarithmicPhaseAngularStep : ℝ :=
  2 * Real.pi

theorem Complex.logarithmicPhaseAngularStep_pos :
    0 < Complex.logarithmicPhaseAngularStep := by
  unfold Complex.logarithmicPhaseAngularStep
  exact Complex.two_mul_pi_pos

theorem Complex.logarithmicPhaseEnhancedPositiveShift_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseEnhancedPositiveShift t b := by
  unfold Complex.logarithmicPhaseEnhancedPositiveShift
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  exact div_nonneg (norm_nonneg t) hright.le

theorem Complex.logarithmicPhasePositiveModeGap_eq_angularStep_mul
    (m : ℤ) :
    Complex.logarithmicPhasePositiveModeGap m =
      Complex.logarithmicPhaseAngularStep * (m : ℝ) := by
  unfold Complex.logarithmicPhasePositiveModeGap
  unfold Complex.logarithmicPhaseAngularStep
  exact rfl

theorem Complex.logarithmicPhaseEnhancedPositiveModeGap_eq_affine
    (t : ℝ) (b : ℤ) (n : ℕ) :
    Complex.logarithmicPhaseEnhancedPositiveModeGap t b
        ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) =
      Complex.logarithmicPhaseEnhancedPositiveShift t b +
        Complex.logarithmicPhaseAngularStep * ((n : ℝ) + 1) := by
  unfold Complex.logarithmicPhaseEnhancedPositiveModeGap
  unfold Complex.logarithmicPhaseEnhancedPositiveShift
  have hmode :=
    Complex.logarithmicPhasePositiveModeGap_eq_angularStep_mul
      ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ)
  have hreal :=
    Complex.logarithmicPhasePositiveIntegerEquivNat_symm_real_value n
  exact Eq.trans
    (congrArg
      (fun value : ℝ =>
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b + value)
      hmode)
    (congrArg
      (fun value : ℝ =>
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b +
          Complex.logarithmicPhaseAngularStep * value)
      hreal)

theorem Complex.enhancedPositive_inverseSquare_eq_shiftedTerm
    (t : ℝ) (b : ℤ) (n : ℕ) :
    1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b
      ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ)) ^ 2 =
      Real.shiftedInverseSquareTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep n := by
  unfold Real.shiftedInverseSquareTerm
  exact congrArg (fun gap : ℝ => 1 / gap ^ 2)
    (Complex.logarithmicPhaseEnhancedPositiveModeGap_eq_affine t b n)

theorem Complex.enhancedPositive_inverseCube_eq_shiftedTerm
    (t : ℝ) (b : ℤ) (n : ℕ) :
    1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b
      ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ)) ^ 3 =
      Real.shiftedInverseCubeTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep n := by
  unfold Real.shiftedInverseCubeTerm
  exact congrArg (fun gap : ℝ => 1 / gap ^ 3)
    (Complex.logarithmicPhaseEnhancedPositiveModeGap_eq_affine t b n)

theorem Complex.enhancedPositive_inverseFourth_eq_shiftedTerm
    (t : ℝ) (b : ℤ) (n : ℕ) :
    1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b
      ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ)) ^ 4 =
      Real.shiftedInverseFourthTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep n := by
  unfold Real.shiftedInverseFourthTerm
  exact congrArg (fun gap : ℝ => 1 / gap ^ 4)
    (Complex.logarithmicPhaseEnhancedPositiveModeGap_eq_affine t b n)

theorem Complex.tsum_positiveInteger_comp_equivNat
    (f : Complex.logarithmicPhasePoissonPositiveTailModes → ℝ) :
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes, f m) =
      ∑' n : ℕ, f ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n) := by
  let e := Complex.logarithmicPhasePositiveIntegerEquivNat
  let g : ℕ → ℝ := fun n : ℕ => f (e.symm n)
  have hpointwise : ∀ m : Complex.logarithmicPhasePoissonPositiveTailModes,
      f m = g (e m) :=
    fun m =>
      have hinverse : e.symm (e m) = m := e.symm_apply_apply m
      congrArg f hinverse.symm
  have hleft :
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes, f m) =
        ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes, g (e m) :=
    tsum_congr hpointwise
  have hreindex :
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes, g (e m)) =
        ∑' n : ℕ, g n :=
    e.tsum_eq g
  exact Eq.trans hleft hreindex

theorem Complex.tsum_enhancedPositive_inverseSquare_eq_shifted
    (t : ℝ) (b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 2) =
      ∑' n : ℕ, Real.shiftedInverseSquareTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep n := by
  have hreindex := Complex.tsum_positiveInteger_comp_equivNat
    (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 2)
  have hterms := tsum_congr
    (fun n => Complex.enhancedPositive_inverseSquare_eq_shiftedTerm t b n)
  exact Eq.trans hreindex hterms

theorem Complex.tsum_enhancedPositive_inverseCube_eq_shifted
    (t : ℝ) (b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 3) =
      ∑' n : ℕ, Real.shiftedInverseCubeTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep n := by
  have hreindex := Complex.tsum_positiveInteger_comp_equivNat
    (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 3)
  have hterms := tsum_congr
    (fun n => Complex.enhancedPositive_inverseCube_eq_shiftedTerm t b n)
  exact Eq.trans hreindex hterms

theorem Complex.tsum_enhancedPositive_inverseFourth_eq_shifted
    (t : ℝ) (b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 4) =
      ∑' n : ℕ, Real.shiftedInverseFourthTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep n := by
  have hreindex := Complex.tsum_positiveInteger_comp_equivNat
    (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      1 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 4)
  have hterms := tsum_congr
    (fun n => Complex.enhancedPositive_inverseFourth_eq_shiftedTerm t b n)
  exact Eq.trans hreindex hterms

end
end LFunctions
end Boundary
