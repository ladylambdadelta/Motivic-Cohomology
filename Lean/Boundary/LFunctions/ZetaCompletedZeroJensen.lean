import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Jensen counting for completed zeta zeros

This file owns the finite-order/Jensen analytic counting input for the centered
completed zeta divisor, counted with analytic multiplicity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Multiplicity summand for completed zeros inside a centered closed disk. -/
noncomputable def completedZeroMultiplicityClosedDiskSummand
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  if ‖(ρ : ℂ)‖ ≤ R then
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  else
    0

/-- Completed-zero multiplicity count in the centered closed disk of radius `R`. -/
noncomputable def completedZeroMultiplicityCountingInCenteredClosedDisk
    (R : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    completedZeroMultiplicityClosedDiskSummand R ρ

/-- Completed zeros in the centered ordinary closed disk of radius `R`. -/
def completedZerosInCenteredClosedDisk
    (R : ℝ) : Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ | ‖(ρ : ℂ)‖ ≤ R}

/-- Zeros of the centered entire zero-carrier. -/
abbrev CenteredCompletedZetaZeroCarrierZero : Type :=
  {z : ℂ // centeredCompletedRiemannZetaZeroCarrier z = 0}

/-- Multiplicity of a zero of the centered entire zero-carrier. -/
noncomputable def centeredCompletedZetaZeroCarrierMultiplicity
    (z : ℂ) : ℕ :=
  (centeredCompletedRiemannZetaZeroCarrier_analyticAt z).order.toNat

/-- Multiplicity summand for carrier zeros inside a centered closed disk. -/
noncomputable def centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (centeredCompletedZetaZeroCarrierMultiplicity (z : ℂ) : ℝ)
  else
    0

/-- Carrier-zero multiplicity count in the centered closed disk of radius `R`. -/
noncomputable def centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk
    (R : ℝ) : ℝ :=
  ∑' z : CenteredCompletedZetaZeroCarrierZero,
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z

/-- Carrier zeros in the centered ordinary closed disk of radius `R`. -/
def centeredCompletedZetaZeroCarrierZerosInClosedDisk
    (R : ℝ) : Set CenteredCompletedZetaZeroCarrierZero :=
  {z | ‖(z : ℂ)‖ ≤ R}

/-- Closed-disk multiplicity summands are nonnegative. -/
theorem completedZeroMultiplicityClosedDiskSummand_nonnegative
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ completedZeroMultiplicityClosedDiskSummand R ρ := by
  unfold completedZeroMultiplicityClosedDiskSummand
  by_cases hρ : ‖(ρ : ℂ)‖ ≤ R
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_pos hρ).symm
      (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_neg hρ).symm
      (le_refl (0 : ℝ))

/-- Closed-disk multiplicity summands vanish outside the closed disk. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_zero_of_not_mem
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredClosedDisk R) :
    completedZeroMultiplicityClosedDiskSummand R ρ = 0 := by
  unfold completedZerosInCenteredClosedDisk at hρ
  unfold completedZeroMultiplicityClosedDiskSummand
  exact if_neg hρ

/-- Centering by the real half-shift does not change the imaginary coordinate. -/
theorem zetaCenteredZero_im_eq
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaCenteredZero (ρ : ℂ)).im = (ρ : ℂ).im := by
  unfold zetaCenteredZero
  calc
    ((ρ : ℂ) - (1 / 2 : ℂ)).im =
        (ρ : ℂ).im - (1 / 2 : ℂ).im := by
      exact Complex.sub_im (ρ : ℂ) (1 / 2 : ℂ)
    _ = (ρ : ℂ).im - (0 : ℝ) := by
      exact congrArg (fun x : ℝ => (ρ : ℂ).im - x) Complex.ofReal_im
    _ = (ρ : ℂ).im := by
      exact sub_zero (ρ : ℂ).im

/-- A completed zero in an ordinary closed disk lies in the enlarged centered-height ball. -/
theorem completedZero_mem_centeredHeightBall_of_mem_centeredClosedDisk
    (R : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ completedZerosInCenteredClosedDisk R) :
    ρ ∈ completedZerosInCenteredHeightBall (R + 1) := by
  unfold completedZerosInCenteredClosedDisk at hρ
  unfold completedZerosInCenteredHeightBall
  unfold zetaCompletedZeroCenteredHeight
  have him :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ = ‖(ρ : ℂ).im‖ :=
    congrArg (fun x : ℝ => ‖x‖) (zetaCenteredZero_im_eq ρ)
  have him_norm :
      ‖(ρ : ℂ).im‖ ≤ ‖(ρ : ℂ)‖ :=
    Complex.abs_im_le_abs (ρ : ℂ)
  have him_centered_norm :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤ ‖(ρ : ℂ)‖ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖(ρ : ℂ)‖)
      him.symm
      him_norm
  have hheight_le_one_add_norm :
      1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤ 1 + ‖(ρ : ℂ)‖ :=
    add_le_add_left him_centered_norm 1
  have hone_add_norm_le_one_add_R :
      1 + ‖(ρ : ℂ)‖ ≤ 1 + R :=
    add_le_add_left hρ 1
  have hone_add_R_eq_R_add_one : 1 + R = R + 1 :=
    add_comm 1 R
  exact le_trans hheight_le_one_add_norm
    (Eq.subst
      (motive := fun x : ℝ => 1 + ‖(ρ : ℂ)‖ ≤ x)
      hone_add_R_eq_R_add_one
      hone_add_norm_le_one_add_R)

/-- Centered ordinary closed disks contain only finitely many completed zeros. -/
theorem finite_completedZerosInCenteredClosedDisk
    (R : ℝ) :
    (completedZerosInCenteredClosedDisk R).Finite := by
  exact Set.Finite.subset
    (finite_completedZerosInCenteredHeightBall (R + 1))
    (fun ρ hρ =>
      completedZero_mem_centeredHeightBall_of_mem_centeredClosedDisk R ρ hρ)

/-- Finite closed disks make the closed-disk multiplicity summand summable. -/
theorem summable_completedZeroMultiplicityClosedDiskSummand_of_finite_closedDisk
    (R : ℝ)
    (hfinite : (completedZerosInCenteredClosedDisk R).Finite) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) := by
  exact summable_of_finite_support_real
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityClosedDiskSummand R ρ)
    (completedZerosInCenteredClosedDisk R)
    hfinite
    (completedZeroMultiplicityClosedDiskSummand_eq_zero_of_not_mem R)

/-- Closed-disk multiplicity summands are summable. -/
theorem summable_completedZeroMultiplicityClosedDiskSummand
    (R : ℝ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) := by
  exact summable_completedZeroMultiplicityClosedDiskSummand_of_finite_closedDisk
    R
    (finite_completedZerosInCenteredClosedDisk R)

/-- Completed zeros in a centered height ball lie in a controlled ordinary closed disk.

The geometric input is the centered critical-strip bound for completed zeros: the real part
is bounded, while the centered height controls the imaginary part. -/
theorem completedZero_mem_centeredClosedDisk_of_mem_centeredHeightBall
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    ‖(ρ : ℂ)‖ ≤ T + 2 := by
  have hstrip :
      -(1 / 2 : ℝ) ≤ (ρ : ℂ).re ∧
        (ρ : ℂ).re ≤ (1 / 2 : ℝ) :=
    zetaCompletedZero_re_mem_centeredCriticalStrip ρ
  have hheight :
      1 + ‖((ρ : ℂ) - (1 / 2 : ℂ)).im‖ ≤ T := by
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ T)
      (by
        unfold zetaCompletedZeroCenteredHeight
        unfold zetaCenteredZero
        rfl)
      hρ
  have hbox : (ρ : ℂ) ∈ centeredCriticalHeightBox T :=
    ⟨hstrip.1, hstrip.2, hheight⟩
  have hnorm_radius :
      ‖(ρ : ℂ)‖ ≤ 2 + |T| :=
    centeredCriticalHeightBox_norm_le_radius hbox
  have hT_nonneg : 0 ≤ T :=
    le_trans zero_le_one hT
  have habs : |T| = T :=
    abs_of_nonneg hT_nonneg
  have hradius : 2 + |T| = T + 2 := by
    calc
      2 + |T| = 2 + T := by
        exact congrArg (fun x : ℝ => 2 + x) habs
      _ = T + 2 := by
        exact add_comm 2 T
  exact Eq.subst
    (motive := fun x : ℝ => ‖(ρ : ℂ)‖ ≤ x)
    hradius
    hnorm_radius

/-- The height-ball multiplicity summand is pointwise bounded by the corresponding
controlled closed-disk summand. -/
theorem completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityClosedDiskSummand (T + 2) ρ := by
  unfold completedZeroMultiplicityHeightBallSummand
  unfold completedZeroMultiplicityClosedDiskSummand
  by_cases hheight : zetaCompletedZeroCenteredHeight ρ ≤ T
  · have hdisk : ‖(ρ : ℂ)‖ ≤ T + 2 :=
      completedZero_mem_centeredClosedDisk_of_mem_centeredHeightBall
        T hT ρ hheight
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ if ‖(ρ : ℂ)‖ ≤ T + 2 then
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
      (if_pos hheight).symm
      (Eq.subst
        (motive := fun x : ℝ =>
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ x)
        (if_pos hdisk).symm
        (le_refl (zetaZeroMultiplicity (ρ : ℂ) : ℝ)))
  · exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ if ‖(ρ : ℂ)‖ ≤ T + 2 then
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
      (if_neg hheight).symm
      (by
        by_cases hdisk : ‖(ρ : ℂ)‖ ≤ T + 2
        · exact Eq.subst
            (motive := fun x : ℝ => 0 ≤ x)
            (if_pos hdisk).symm
            (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
        · exact Eq.subst
            (motive := fun x : ℝ => 0 ≤ x)
            (if_neg hdisk).symm
            (le_refl (0 : ℝ)))

/-- Centered-height multiplicity counting is bounded by closed-disk multiplicity counting
at the controlled enlarged radius. -/
theorem completedZeroMultiplicityCounting_heightBall_le_closedDiskCounting
    (T : ℝ) (hT : 1 ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall T ≤
      completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) := by
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  unfold completedZeroMultiplicityCountingInCenteredClosedDisk
  exact tsum_le_tsum
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand T hT ρ)
    (summable_completedZeroMultiplicityHeightBallSummand T)
    (summable_completedZeroMultiplicityClosedDiskSummand (T + 2))

/-- A closed-disk polynomial bound at radius `T + 2` gives a centered-height polynomial
bound at radius `T`, after increasing the polynomial constant. -/
theorem completedZeroMultiplicityCounting_heightBall_polynomial_bound_of_closedDisk_bound
    (C : ℝ) (d : ℕ)
    (hC : 0 < C)
    (hclosed :
      ∀ R : ℝ,
        1 ≤ R →
        completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d) :
    ∃ C' : ℝ,
      0 < C' ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C' * T ^ d := by
  refine ⟨C * (3 : ℝ) ^ d, ?_, ?_⟩
  · exact mul_pos hC (pow_pos zero_lt_three d)
  · intro T hT
    have hheight_disk :
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤
          completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) :=
      completedZeroMultiplicityCounting_heightBall_le_closedDiskCounting T hT
    have hR_ge_one : 1 ≤ T + 2 :=
      le_trans hT (le_add_of_nonneg_right zero_le_two)
    have hclosed_T :
        completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) ≤
          C * (T + 2) ^ d :=
      hclosed (T + 2) hR_ge_one
    have htwo_le_two_mul : (2 : ℝ) ≤ 2 * T := by
      exact mul_le_mul_of_nonneg_left hT zero_le_two
    have hT_add_le_three_mul : T + 2 ≤ (3 : ℝ) * T := by
      have hadd : T + 2 ≤ T + 2 * T :=
        add_le_add_left htwo_le_two_mul T
      have hthree : (3 : ℝ) * T = T + 2 * T := by
        calc
          (3 : ℝ) * T = T + T + T := by
            exact three_mul T
          _ = T + (T + T) := by
            exact add_assoc T T T
          _ = T + 2 * T := by
            exact congrArg (fun x : ℝ => T + x) (two_mul T).symm
      exact Eq.subst
        (motive := fun x : ℝ => T + 2 ≤ x)
        hthree.symm
        hadd
    have hT_add_nonneg : 0 ≤ T + 2 :=
      le_trans zero_le_one hR_ge_one
    have hpow :
        (T + 2) ^ d ≤ ((3 : ℝ) * T) ^ d :=
      pow_le_pow_left₀ hT_add_nonneg hT_add_le_three_mul d
    have hscaled :
        C * (T + 2) ^ d ≤ C * (((3 : ℝ) * T) ^ d) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
    have hfactor :
        C * (((3 : ℝ) * T) ^ d) = (C * (3 : ℝ) ^ d) * T ^ d := by
      calc
        C * (((3 : ℝ) * T) ^ d) =
            C * ((3 : ℝ) ^ d * T ^ d) := by
          exact congrArg (fun x : ℝ => C * x) (mul_pow (3 : ℝ) T d)
        _ = (C * (3 : ℝ) ^ d) * T ^ d := by
          exact (mul_assoc C ((3 : ℝ) ^ d) (T ^ d)).symm
    exact le_trans hheight_disk
      (le_trans hclosed_T
        (le_trans hscaled
          (le_of_eq hfactor)))

/-- A completed zero is a zero of the centered entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_zero_of_completedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    centeredCompletedRiemannZetaZeroCarrier (ρ : ℂ) = 0 := by
  exact centeredCompletedRiemannZetaZeroCarrier_eq_zero_of_completed_zero
    (centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ))
    (centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ))
    (zetaCompletedZero_zero ρ)

/-- A completed zero maps canonically to a zero of the centered entire zero-carrier. -/
def completedZeroToCarrierZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    CenteredCompletedZetaZeroCarrierZero :=
  ⟨(ρ : ℂ), centeredCompletedRiemannZetaZeroCarrier_zero_of_completedZero ρ⟩

/-- The completed-zero to carrier-zero map is injective. -/
theorem completedZeroToCarrierZero_injective :
    Function.Injective completedZeroToCarrierZero := by
  intro ρ η hρη
  exact Subtype.ext (congrArg Subtype.val hρη)

/-- The cleared zero-carrier is nonzero at the negative shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_ne_zero_negHalf :
    centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) ≠ 0 := by
  unfold centeredCompletedRiemannZetaZeroCarrier
  norm_num

/-- The cleared zero-carrier is nonzero at the positive shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_ne_zero_posHalf :
    centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) ≠ 0 := by
  unfold centeredCompletedRiemannZetaZeroCarrier
  norm_num

/-- A carrier zero cannot be the negative shifted pole face. -/
theorem centeredCompletedZetaZeroCarrierZero_ne_negHalf
    (z : CenteredCompletedZetaZeroCarrierZero) :
    (z : ℂ) ≠ -(1 / 2 : ℂ) := by
  intro hz
  have hcarrier_at_pole :
      centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) = 0 := by
    exact Eq.subst
      (motive := fun w : ℂ => centeredCompletedRiemannZetaZeroCarrier w = 0)
      hz
      z.2
  exact centeredCompletedRiemannZetaZeroCarrier_ne_zero_negHalf hcarrier_at_pole

/-- A carrier zero cannot be the positive shifted pole face. -/
theorem centeredCompletedZetaZeroCarrierZero_ne_posHalf
    (z : CenteredCompletedZetaZeroCarrierZero) :
    (z : ℂ) ≠ (1 / 2 : ℂ) := by
  intro hz
  have hcarrier_at_pole :
      centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) = 0 := by
    exact Eq.subst
      (motive := fun w : ℂ => centeredCompletedRiemannZetaZeroCarrier w = 0)
      hz
      z.2
  exact centeredCompletedRiemannZetaZeroCarrier_ne_zero_posHalf hcarrier_at_pole

/-- A zero of the cleared entire carrier is a completed zero after excluding the shifted
pole faces. -/
theorem zetaCompletedZero_of_centeredCompletedZetaZeroCarrierZero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    ZetaCompletedZero (z : ℂ) := by
  have hneg : (z : ℂ) ≠ -(1 / 2 : ℂ) :=
    centeredCompletedZetaZeroCarrierZero_ne_negHalf z
  have hpos : (z : ℂ) ≠ (1 / 2 : ℂ) :=
    centeredCompletedZetaZeroCarrierZero_ne_posHalf z
  have hleft :
      (1 / 2 : ℂ) + (z : ℂ) ≠ 0 :=
    centeredShift_leftDenominator_ne_zero_of_ne_negHalf hneg
  have hright :
      1 - ((1 / 2 : ℂ) + (z : ℂ)) ≠ 0 :=
    centeredShift_rightDenominator_ne_zero_of_ne_posHalf hpos
  have hdenom :
      ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) ≠ 0 :=
    centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles hneg hpos
  have hcarrier_eq_product :
      centeredCompletedRiemannZetaZeroCarrier (z : ℂ) =
        ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) *
            centeredCompletedRiemannZeta (z : ℂ) :=
    centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hleft hright
  have hproduct_zero :
      ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) *
            centeredCompletedRiemannZeta (z : ℂ) = 0 :=
    hcarrier_eq_product.symm.trans z.2
  have hcompleted_zero :
      centeredCompletedRiemannZeta (z : ℂ) = 0 :=
    match mul_eq_zero.mp hproduct_zero with
    | Or.inl hdenom_zero => False.elim (hdenom hdenom_zero)
    | Or.inr hzero => hzero
  exact zetaCompletedZero_mk hneg hpos hcompleted_zero

/-- A carrier zero maps canonically back to the completed-zero divisor. -/
def carrierZeroToCompletedZero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    {ρ : ℂ // ZetaCompletedZero ρ} :=
  ⟨(z : ℂ), zetaCompletedZero_of_centeredCompletedZetaZeroCarrierZero z⟩

/-- The carrier-zero to completed-zero map is injective. -/
theorem carrierZeroToCompletedZero_injective :
    Function.Injective carrierZeroToCompletedZero := by
  intro z w hzw
  exact Subtype.ext (congrArg Subtype.val hzw)

/-- Carrier zeros in a closed disk map into completed zeros in the same closed disk. -/
theorem carrierZeroToCompletedZero_mem_closedDisk
    (R : ℝ)
    (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : z ∈ centeredCompletedZetaZeroCarrierZerosInClosedDisk R) :
    carrierZeroToCompletedZero z ∈ completedZerosInCenteredClosedDisk R := by
  unfold centeredCompletedZetaZeroCarrierZerosInClosedDisk at hz
  unfold completedZerosInCenteredClosedDisk
  exact hz

/-- Carrier closed-disk multiplicity summands are nonnegative. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero) :
    0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z := by
  unfold centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
  by_cases hz : ‖(z : ℂ)‖ ≤ R
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_pos hz).symm
      (Nat.cast_nonneg (centeredCompletedZetaZeroCarrierMultiplicity (z : ℂ)))
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_neg hz).symm
      (le_refl (0 : ℝ))

/-- Carrier closed-disk multiplicity summands vanish outside the carrier closed disk. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_zero_of_not_mem
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : z ∉ centeredCompletedZetaZeroCarrierZerosInClosedDisk R) :
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z = 0 := by
  unfold centeredCompletedZetaZeroCarrierZerosInClosedDisk at hz
  unfold centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
  exact if_neg hz

/-- The denominator clearing factor is nonzero at a completed zero. -/
theorem completedZero_denominatorClearingFactor_ne_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ((1 / 2 : ℂ) + (ρ : ℂ)) *
        (1 - ((1 / 2 : ℂ) + (ρ : ℂ))) ≠ 0 := by
  exact centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles
    (zetaCompletedZero_ne_negHalf ρ)
    (zetaCompletedZero_ne_posHalf ρ)

/-- Near a completed zero, the cleared zero-carrier is the denominator unit times the
centered completed zeta normalization. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eventuallyEq_denominator_mul
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    centeredCompletedRiemannZetaZeroCarrier =ᶠ[𝓝 (ρ : ℂ)]
      (fun w : ℂ =>
        ((1 / 2 : ℂ) + w) *
          (1 - ((1 / 2 : ℂ) + w)) *
            centeredCompletedRiemannZeta w) := by
  have hleft_ne :
      ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 := by
    exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ)
  have hright_ne :
      1 - ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 := by
    exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ)
  have hleft_eventually :
      ∀ᶠ w in 𝓝 (ρ : ℂ), (1 / 2 : ℂ) + w ≠ 0 :=
    ((continuous_const.add continuous_id).continuousAt).eventually_ne hleft_ne
  have hright_eventually :
      ∀ᶠ w in 𝓝 (ρ : ℂ), 1 - ((1 / 2 : ℂ) + w) ≠ 0 :=
    ((continuous_const.sub (continuous_const.add continuous_id)).continuousAt).eventually_ne
      hright_ne
  filter_upwards [hleft_eventually, hright_eventually] with w hwleft hwright
  exact centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hwleft hwright

/-- Completed-zero multiplicity is the cleared-carrier multiplicity at the same point. -/
theorem zetaZeroMultiplicity_eq_carrierMultiplicity
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroMultiplicity (ρ : ℂ) =
      centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) := by
  let u : ℂ → ℂ :=
    fun w : ℂ => ((1 / 2 : ℂ) + w) * (1 - ((1 / 2 : ℂ) + w))
  have hcompleted :
      AnalyticAt ℂ centeredCompletedRiemannZeta (ρ : ℂ) :=
    centeredCompletedRiemannZeta_analyticAt_of_completedZero ρ
  have hcarrier :
      AnalyticAt ℂ centeredCompletedRiemannZetaZeroCarrier (ρ : ℂ) :=
    centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)
  have hu : AnalyticAt ℂ u (ρ : ℂ) := by
    exact centeredShift_denominatorClearingFactor_analyticAt (ρ : ℂ)
  have huz : u (ρ : ℂ) ≠ 0 := by
    exact completedZero_denominatorClearingFactor_ne_zero ρ
  have heq :
      centeredCompletedRiemannZetaZeroCarrier =ᶠ[𝓝 (ρ : ℂ)]
        (fun w : ℂ => u w * centeredCompletedRiemannZeta w) :=
    centeredCompletedRiemannZetaZeroCarrier_eventuallyEq_denominator_mul ρ
  have horder :
      hcarrier.order = hcompleted.order :=
    analyticAt_order_eq_of_eventuallyEq_mul_left
      hcarrier
      hcompleted
      hu
      huz
      heq
  calc
    zetaZeroMultiplicity (ρ : ℂ) =
        completedZetaZeroMultiplicity (ρ : ℂ) := by
      rfl
    _ = hcompleted.order.toNat := by
      exact completedZetaZeroMultiplicity_eq_order (ρ : ℂ) hcompleted
    _ = hcarrier.order.toNat := by
      exact (congrArg ENat.toNat horder).symm
    _ = centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) := by
      rfl

/-- Closed-disk completed-zero summands are the pullback of carrier-zero summands. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityClosedDiskSummand R ρ =
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
        (completedZeroToCarrierZero ρ) := by
  unfold completedZeroMultiplicityClosedDiskSummand
  unfold centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
  change
    (if ‖(ρ : ℂ)‖ ≤ R then
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0) =
    (if ‖(ρ : ℂ)‖ ≤ R then
      (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) else 0)
  by_cases hρ : ‖(ρ : ℂ)‖ ≤ R
  · have hleft :
        (if ‖(ρ : ℂ)‖ ≤ R then
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0) =
            (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
      if_pos hρ
    have hright :
        (if ‖(ρ : ℂ)‖ ≤ R then
          (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) else 0) =
            (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) :=
      if_pos hρ
    exact hleft.trans
      ((congrArg (fun n : ℕ => (n : ℝ))
        (zetaZeroMultiplicity_eq_carrierMultiplicity ρ)).trans hright.symm)
  · have hleft :
        (if ‖(ρ : ℂ)‖ ≤ R then
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0) = 0 :=
      if_neg hρ
    have hright :
        (if ‖(ρ : ℂ)‖ ≤ R then
          (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) else 0) = 0 :=
      if_neg hρ
    exact hleft.trans hright.symm

/-- The centered entire zero-carrier has only finitely many zeros in every
ordinary closed disk. This is the local-finiteness part of the finite-order
Jensen package for the cleared entire divisor. -/
theorem finite_centeredCompletedZetaZeroCarrierZerosInClosedDisk
    (R : ℝ) :
    (centeredCompletedZetaZeroCarrierZerosInClosedDisk R).Finite := by
  have himage_subset :
      carrierZeroToCompletedZero ''
          centeredCompletedZetaZeroCarrierZerosInClosedDisk R ⊆
        completedZerosInCenteredClosedDisk R := by
    intro ρ hρ
    match hρ with
    | ⟨z, hzmem, hzρ⟩ =>
        exact Eq.subst
          (motive := fun y : {ρ : ℂ // ZetaCompletedZero ρ} =>
            y ∈ completedZerosInCenteredClosedDisk R)
          hzρ
          (carrierZeroToCompletedZero_mem_closedDisk R z hzmem)
  have himage_finite :
      (carrierZeroToCompletedZero ''
          centeredCompletedZetaZeroCarrierZerosInClosedDisk R).Finite :=
    Set.Finite.subset
      (finite_completedZerosInCenteredClosedDisk R)
      himage_subset
  exact Set.Finite.of_finite_image
    himage_finite
    (fun z hz w hw hzw => carrierZeroToCompletedZero_injective hzw)

/-- Finite carrier closed disks make the carrier multiplicity summand summable. -/
theorem summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_of_finite_closedDisk
    (R : ℝ) :
    Summable
      (fun z : CenteredCompletedZetaZeroCarrierZero =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z) := by
  exact summable_of_finite_support_real
    (fun z : CenteredCompletedZetaZeroCarrierZero =>
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)
    (centeredCompletedZetaZeroCarrierZerosInClosedDisk R)
    (finite_centeredCompletedZetaZeroCarrierZerosInClosedDisk R)
    (centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_zero_of_not_mem R)

/-- Carrier closed-disk multiplicity summands are summable. -/
theorem summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
    (R : ℝ) :
    Summable
      (fun z : CenteredCompletedZetaZeroCarrierZero =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z) := by
  exact
    summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_of_finite_closedDisk R

/-- Completed-zero closed-disk counting is dominated by the carrier count once the carrier
summand is known to be summable. -/
theorem completedZeroMultiplicityCounting_closedDisk_le_carrierCounting_of_summable
    (R : ℝ)
    (hcarrier :
      Summable
        (fun z : CenteredCompletedZetaZeroCarrierZero =>
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)) :
    completedZeroMultiplicityCountingInCenteredClosedDisk R ≤
      centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R := by
  have hcompleted_as_pullback :
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) =
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
          (completedZeroToCarrierZero ρ)) := by
    funext ρ
    exact completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback R ρ
  have hnonnegative :
      ∀ z : CenteredCompletedZetaZeroCarrierZero,
        0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z :=
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative R
  unfold completedZeroMultiplicityCountingInCenteredClosedDisk
  unfold centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk
  exact Eq.subst
    (motive := fun u : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ =>
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, u ρ) ≤
        ∑' z : CenteredCompletedZetaZeroCarrierZero,
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)
    hcompleted_as_pullback.symm
    (tsum_comp_le_tsum_of_inj
      hcarrier
      hnonnegative
      completedZeroToCarrierZero_injective)

/-- Jensen counting for the centered entire zero-carrier divisor in ordinary closed disks. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityCounting_closedDisk_bound_of_finiteOrder
    (hfinite :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R ≤ C * R ^ d := by
  sorry

/-- Completed-zero closed-disk counting is dominated by the cleared-carrier divisor count.

This is the local divisor-transport step: clearing the shifted pole denominators does not
decrease the order of a non-pole zero. -/
theorem completedZeroMultiplicityCounting_closedDisk_le_carrierCounting
    (R : ℝ) :
    completedZeroMultiplicityCountingInCenteredClosedDisk R ≤
      centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R := by
  exact completedZeroMultiplicityCounting_closedDisk_le_carrierCounting_of_summable
    R
    (summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R)

/-- Jensen transport from finite-order growth of the entire zero-carrier to
multiplicity-aware centered closed-disk completed-zero counting. -/
theorem centeredCompletedRiemannZeta_closedDiskMultiplicityCounting_bound_of_zeroCarrierFiniteOrder
    (hfinite :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d := by
  exact
    match centeredCompletedZetaZeroCarrierMultiplicityCounting_closedDisk_bound_of_finiteOrder
        hfinite with
    | ⟨C, d, hC, hcarrier⟩ =>
        ⟨C, d, hC,
          fun R hR =>
            le_trans
              (completedZeroMultiplicityCounting_closedDisk_le_carrierCounting R)
              (hcarrier R hR)⟩

/-- Centered closed-disk zero counting bounds centered-height zero counting after polynomial
radius enlargement. -/
theorem completedZeroMultiplicityCounting_heightBall_bound_of_closedDisk_bound
    (hclosed :
      ∃ C : ℝ, ∃ d : ℕ,
        0 < C ∧
        ∀ R : ℝ,
          1 ≤ R →
          completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    match hclosed with
    | ⟨C, d, hC, hbound⟩ =>
        match completedZeroMultiplicityCounting_heightBall_polynomial_bound_of_closedDisk_bound
            C d hC hbound with
        | ⟨C', hC', hbound'⟩ =>
            ⟨C', d, hC', hbound'⟩

/-- Jensen transport from finite-order growth of the entire zero-carrier to
multiplicity-aware centered-height completed-zero counting. -/
theorem centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_zeroCarrierFiniteOrder
    (hfinite :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact completedZeroMultiplicityCounting_heightBall_bound_of_closedDisk_bound
    (centeredCompletedRiemannZeta_closedDiskMultiplicityCounting_bound_of_zeroCarrierFiniteOrder
      hfinite)

/-- Finite-order/Jensen zero counting for the centered completed zeta divisor,
with analytic multiplicities and centered vertical height. -/
theorem centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_zeroCarrierFiniteOrder
      centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound

/-- Coarse polynomial counting of completed zeros with multiplicity in centered
height. -/
theorem exists_completedZeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound

end

end LFunctions
end Boundary
