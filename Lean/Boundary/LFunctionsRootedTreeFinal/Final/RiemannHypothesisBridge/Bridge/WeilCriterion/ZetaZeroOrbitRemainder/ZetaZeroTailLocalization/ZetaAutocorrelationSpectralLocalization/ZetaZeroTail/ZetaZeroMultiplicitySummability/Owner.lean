import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.Owner

/-!
# Completed zero multiplicity summability

This file owns the passage from multiplicity-aware height counting to summability
of negative centered-height powers over completed zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The cumulative counting envelope controlling one centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellCountingEnvelope
    (C : ℝ) (d k m : ℕ) : ℝ :=
  C * (((m + 1 : ℕ) : ℝ) ^ d) *
    (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))

/-- The explicit constant used to dominate the shell counting envelope by a
one-dimensional polynomial tail. -/
noncomputable def completedZeroCenteredHeightShellTailConstant
    (C : ℝ) (d k : ℕ) : ℝ :=
  C * (2 : ℝ) ^ (d + k + 3)

/-- The explicit shell-tail constant is positive when `C` is positive. -/
theorem completedZeroCenteredHeightShellTailConstant_pos
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C) :
    0 < completedZeroCenteredHeightShellTailConstant C d k := by
  change 0 < C * (2 : ℝ) ^ (d + k + 3)
  exact mul_pos hCpos (pow_pos zero_lt_two (d + k + 3))

/-- The lower decay factor attached to a centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellLowerDecay
    (d k m : ℕ) : ℝ :=
  (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))

/-- The lower shell decay factor is nonnegative. -/
theorem completedZeroCenteredHeightShellLowerDecay_nonnegative
    (d k m : ℕ) :
    0 ≤ completedZeroCenteredHeightShellLowerDecay d k m := by
  change 0 ≤ (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))
  exact zpow_nonneg
    (le_trans zero_le_one (le_max_left 1 ‖((m : ℕ) : ℝ)‖))
    (-(d + k + 3 : ℤ))

/-- A centered-height shell decay mass is nonnegative. -/
theorem completedZeroCenteredHeightShellDecayMass_nonnegative
    (d k m : ℕ) :
    0 ≤ completedZeroCenteredHeightShellDecayMass d k m := by
  change
    0 ≤
      tsum
        (fun x : completedZeroCenteredHeightShellFiber m =>
          zetaCompletedZeroCenteredHeight
              (x : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(d + k + 3 : ℤ)))
  exact tsum_nonneg
    (fun x : completedZeroCenteredHeightShellFiber m =>
      zpow_nonneg
        (le_trans zero_le_one
          (zetaCompletedZeroCenteredHeight_ge_one
            (x : {ρ : ℂ // ZetaCompletedZero ρ})))
        (-(d + k + 3 : ℤ)))

/-- The norm of a centered-height shell decay mass is the mass itself. -/
theorem norm_completedZeroCenteredHeightShellDecayMass_eq_self
    (d k m : ℕ) :
    ‖completedZeroCenteredHeightShellDecayMass d k m‖ =
      completedZeroCenteredHeightShellDecayMass d k m := by
  exact Real.norm_of_nonneg
    (completedZeroCenteredHeightShellDecayMass_nonnegative d k m)

/-- A successor natural, cast to `ℝ`, is at least one. -/
theorem one_le_nat_succ_cast_real
    (m : ℕ) :
    1 ≤ ((m + 1 : ℕ) : ℝ) := by
  exact Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le m))

/-- On bases at least one, negative natural integer powers are antitone. -/
theorem real_zpow_negNat_antitone_on_one_le
    {a b : ℝ} (N : ℕ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    b ^ (-(N : ℤ)) ≤ a ^ (-(N : ℤ)) := by
  have ha_pos : 0 < a :=
    lt_of_lt_of_le zero_lt_one ha
  have hpow_le :
      a ^ N ≤ b ^ N :=
    pow_le_pow_left₀ (le_of_lt ha_pos) hab N
  have ha_pow_pos :
      0 < a ^ N :=
    pow_pos ha_pos N
  have hinv :
      (b ^ N)⁻¹ ≤ (a ^ N)⁻¹ :=
    inv_anti₀ ha_pow_pos hpow_le
  have hb_zpow :
      b ^ (-(N : ℤ)) = (b ^ N)⁻¹ := by
    have hb_neg :
        b ^ (-(N : ℤ)) = (b ^ (N : ℤ))⁻¹ :=
      zpow_neg b (N : ℤ)
    have hb_nat :
        b ^ (N : ℤ) = b ^ N :=
      zpow_natCast b N
    exact Eq.trans hb_neg (congrArg Inv.inv hb_nat)
  have ha_zpow :
      a ^ (-(N : ℤ)) = (a ^ N)⁻¹ := by
    have ha_neg :
        a ^ (-(N : ℤ)) = (a ^ (N : ℤ))⁻¹ :=
      zpow_neg a (N : ℤ)
    have ha_nat :
        a ^ (N : ℤ) = a ^ N :=
      zpow_natCast a N
    exact Eq.trans ha_neg (congrArg Inv.inv ha_nat)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ a ^ (-(N : ℤ)))
    hb_zpow.symm
    (Eq.subst
      (motive := fun x : ℝ => (b ^ N)⁻¹ ≤ x)
      ha_zpow.symm
      hinv)

/-- The lower shell base is below the centered height of each zero in the shell. -/
theorem completedZeroCenteredHeightShell_lowerBase_le_height
    (m : ℕ)
    (ρ : completedZeroCenteredHeightShellFiber m) :
    max 1 ‖((m : ℕ) : ℝ)‖ ≤
      zetaCompletedZeroCenteredHeight
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) := by
  have hheight_ge_one :
      1 ≤ zetaCompletedZeroCenteredHeight
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    zetaCompletedZeroCenteredHeight_ge_one
      (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
  have hm_cast_le_height :
      ((m : ℕ) : ℝ) ≤
        zetaCompletedZeroCenteredHeight
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    ρ.2.1
  have hm_norm_eq :
      ‖((m : ℕ) : ℝ)‖ = ((m : ℕ) : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg m)
  have hm_norm_le_height :
      ‖((m : ℕ) : ℝ)‖ ≤
        zetaCompletedZeroCenteredHeight
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ zetaCompletedZeroCenteredHeight
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}))
      hm_norm_eq.symm
      hm_cast_le_height
  exact max_le hheight_ge_one hm_norm_le_height

/-- A completed zero in shell `m` has its decay term bounded by the lower shell
decay factor. -/
theorem completedZeroCenteredHeightShell_decay_le_lowerDecay
    (d k m : ℕ)
    (ρ : completedZeroCenteredHeightShellFiber m) :
    zetaCompletedZeroCenteredHeight
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ)) ≤
      completedZeroCenteredHeightShellLowerDecay d k m := by
  change
    zetaCompletedZeroCenteredHeight
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ)) ≤
      (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))
  exact real_zpow_negNat_antitone_on_one_le
    (d + k + 3)
    (le_max_left 1 ‖((m : ℕ) : ℝ)‖)
    (completedZeroCenteredHeightShell_lowerBase_le_height m ρ)

/-- A `tsum` over a finite type is bounded by cardinal times a uniform bound. -/
theorem real_tsum_le_natCard_mul_of_forall_le
    {α : Type*} [Fintype α]
    (u : α → ℝ) (B : ℝ)
    (hbound : ∀ a : α, u a ≤ B) :
    (∑' a : α, u a) ≤ (Nat.card α : ℝ) * B := by
  have htsum :
      (∑' a : α, u a) = ∑ a : α, u a :=
    tsum_fintype
  have hsum :
      (∑ a : α, u a) ≤ Finset.univ.card • B :=
    Finset.sum_le_card_nsmul
      Finset.univ
      u
      B
      (fun a _ha => hbound a)
  have hcard :
      Finset.univ.card = Nat.card α :=
    Eq.trans
      (Finset.card_univ)
      (Fintype.card_eq_nat_card)
  have hsmul :
      Finset.univ.card • B = (Finset.univ.card : ℝ) * B :=
    nsmul_eq_mul Finset.univ.card B
  have hcast :
      (Finset.univ.card : ℝ) = (Nat.card α : ℝ) :=
    congrArg Nat.cast hcard
  have hmul :
      (Finset.univ.card : ℝ) * B = (Nat.card α : ℝ) * B :=
    congrArg (fun x : ℝ => x * B) hcast
  have htarget :
      Finset.univ.card • B = (Nat.card α : ℝ) * B :=
    Eq.trans hsmul hmul
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ (Nat.card α : ℝ) * B)
    htsum
    (Eq.subst
      (motive := fun x : ℝ => (∑ a : α, u a) ≤ x)
      htarget
      hsum)

/-- A finite `tsum` whose terms are all at least one dominates the cardinality
of its index type. -/
theorem natCard_le_real_tsum_of_one_le
    {α : Type*} [Fintype α]
    (u : α → ℝ)
    (hone : ∀ a : α, (1 : ℝ) ≤ u a) :
    (Nat.card α : ℝ) ≤ ∑' a : α, u a := by
  have hsum :
      (∑ a : α, (1 : ℝ)) ≤ ∑ a : α, u a :=
    Finset.sum_le_sum
      (fun a _ha => hone a)
  have hsum_one :
      (∑ a : α, (1 : ℝ)) = Finset.univ.card • (1 : ℝ) :=
    Finset.sum_const (1 : ℝ)
  have hsmul_one :
      Finset.univ.card • (1 : ℝ) = (Finset.univ.card : ℝ) * (1 : ℝ) :=
    nsmul_eq_mul Finset.univ.card (1 : ℝ)
  have hmul_one :
      (Finset.univ.card : ℝ) * (1 : ℝ) = (Finset.univ.card : ℝ) :=
    mul_one (Finset.univ.card : ℝ)
  have hsum_one_card :
      (∑ a : α, (1 : ℝ)) = (Finset.univ.card : ℝ) :=
    Eq.trans hsum_one (Eq.trans hsmul_one hmul_one)
  have hcard :
      Finset.univ.card = Nat.card α :=
    Eq.trans
      (Finset.card_univ)
      (Fintype.card_eq_nat_card)
  have hcast :
      (Finset.univ.card : ℝ) = (Nat.card α : ℝ) :=
    congrArg Nat.cast hcard
  have hsum_one_natCard :
      (∑ a : α, (1 : ℝ)) = (Nat.card α : ℝ) :=
    Eq.trans hsum_one_card hcast
  have hnatCard_le_sum :
      (Nat.card α : ℝ) ≤ ∑ a : α, u a :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ∑ a : α, u a)
      hsum_one_natCard
      hsum
  have htsum :
      (∑' a : α, u a) = ∑ a : α, u a :=
    tsum_fintype
  exact Eq.subst
    (motive := fun x : ℝ => (Nat.card α : ℝ) ≤ x)
    htsum.symm
    hnatCard_le_sum

/-- A completed zero in a height ball contributes at least one to the
multiplicity height-ball summand. -/
theorem one_le_completedZeroMultiplicityHeightBallSummand_of_mem
    (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ completedZerosInCenteredHeightBall T) :
    (1 : ℝ) ≤ completedZeroMultiplicityHeightBallSummand T ρ := by
  change
    (1 : ℝ) ≤
      if ρ ∈ completedZerosInCenteredHeightBall T then
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
      else
        0
  have hpos :
      0 < zetaZeroMultiplicity (ρ : ℂ) :=
    zetaZeroMultiplicity_pos_of_completedZero ρ
  have hone_nat :
      1 ≤ zetaZeroMultiplicity (ρ : ℂ) :=
    hpos
  have hone_real :
      (1 : ℝ) ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    Nat.cast_le.mpr hone_nat
  exact Eq.subst
    (motive := fun x : ℝ => (1 : ℝ) ≤ x)
    (if_pos hρ).symm
    hone_real

/-- The unweighted shell cardinal is bounded by the multiplicity count in the
containing height ball. -/
theorem completedZeroCenteredHeightShell_unweightedCount_le_multiplicityCounting
    (m : ℕ) :
    (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) := by
  haveI : Fintype (completedZeroCenteredHeightShellFiber m) :=
    (finite_completedZeroCenteredHeightShell m).fintype
  let T : ℝ := ((m + 1 : ℕ) : ℝ)
  let i :
      completedZeroCenteredHeightShellFiber m →
        {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun ρ => (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
  have hi : Function.Injective i := by
    intro ρ η hρη
    exact Subtype.ext hρη
  have hone :
      ∀ ρ : completedZeroCenteredHeightShellFiber m,
        (1 : ℝ) ≤
          completedZeroMultiplicityHeightBallSummand T (i ρ) := by
    intro ρ
    have hmem :
        i ρ ∈ completedZerosInCenteredHeightBall T :=
      completedZeroCenteredHeightShell_subset_heightBall m ρ.2
    exact one_le_completedZeroMultiplicityHeightBallSummand_of_mem T (i ρ) hmem
  have hcard_le_shell_tsum :
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
        ∑' ρ : completedZeroCenteredHeightShellFiber m,
          completedZeroMultiplicityHeightBallSummand T (i ρ) :=
    natCard_le_real_tsum_of_one_le
      (fun ρ : completedZeroCenteredHeightShellFiber m =>
        completedZeroMultiplicityHeightBallSummand T (i ρ))
      hone
  have hsummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          completedZeroMultiplicityHeightBallSummand T ρ) :=
    summable_completedZeroMultiplicityHeightBallSummand T
  have hnonnegative :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        0 ≤ completedZeroMultiplicityHeightBallSummand T ρ :=
    completedZeroMultiplicityHeightBallSummand_nonnegative T
  have hshell_tsum_le_total :
      (∑' ρ : completedZeroCenteredHeightShellFiber m,
          completedZeroMultiplicityHeightBallSummand T (i ρ)) ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ :=
    tsum_comp_le_tsum_of_inj
      hsummable
      hnonnegative
      hi
  change
    (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        completedZeroMultiplicityHeightBallSummand T ρ
  exact le_trans hcard_le_shell_tsum hshell_tsum_le_total

/-- A finite nonnegative shell `tsum` is bounded by cardinal times a uniform
shell bound. -/
theorem completedZeroCenteredHeightShellDecayMass_le_card_mul_lowerDecay
    (d k m : ℕ) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m := by
  haveI : Fintype (completedZeroCenteredHeightShellFiber m) :=
    (finite_completedZeroCenteredHeightShell m).fintype
  change
    (∑' ρ : completedZeroCenteredHeightShellFiber m,
      zetaCompletedZeroCenteredHeight
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ))) ≤
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m
  exact real_tsum_le_natCard_mul_of_forall_le
    (fun ρ : completedZeroCenteredHeightShellFiber m =>
      zetaCompletedZeroCenteredHeight
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ)))
    (completedZeroCenteredHeightShellLowerDecay d k m)
    (completedZeroCenteredHeightShell_decay_le_lowerDecay d k m)

/-- Shell decay mass is bounded by the cumulative multiplicity count times the
lower shell decay factor. -/
theorem completedZeroCenteredHeightShellDecayMass_le_counting_mul_lowerDecay
    (d k m : ℕ) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m := by
  have hcard :
      completedZeroCenteredHeightShellDecayMass d k m ≤
        (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellDecayMass_le_card_mul_lowerDecay d k m
  have hcount :
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
        completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) :=
    completedZeroCenteredHeightShell_unweightedCount_le_multiplicityCounting m
  have hdecay_nonnegative :
      0 ≤ completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellLowerDecay_nonnegative d k m
  have hmul :
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m ≤
        completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    mul_le_mul_of_nonneg_right hcount hdecay_nonnegative
  exact le_trans hcard hmul

/-- Applying a counting bound converts the counting-times-decay expression into
the named cumulative shell envelope. -/
theorem completedZeroMultiplicityCounting_mul_lowerDecay_le_countingEnvelope
    (C : ℝ) (d k m : ℕ)
    (hcount_m :
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) ≤
        C * (((m + 1 : ℕ) : ℝ) ^ d)) :
    completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m ≤
      completedZeroCenteredHeightShellCountingEnvelope C d k m := by
  have hdecay_nonnegative :
      0 ≤ completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellLowerDecay_nonnegative d k m
  have hmul :
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m ≤
        (C * (((m + 1 : ℕ) : ℝ) ^ d)) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    mul_le_mul_of_nonneg_right hcount_m hdecay_nonnegative
  exact hmul

/-- Multiplicity-aware counting bounds the real shell decay mass by the raw
cumulative shell envelope. -/
theorem completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      completedZeroCenteredHeightShellCountingEnvelope C d k m := by
  have hshell :
      completedZeroCenteredHeightShellDecayMass d k m ≤
        completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellDecayMass_le_counting_mul_lowerDecay d k m
  have hcount_m :
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) ≤
        C * (((m + 1 : ℕ) : ℝ) ^ d) :=
    hcount
      ((m + 1 : ℕ) : ℝ)
      (one_le_nat_succ_cast_real m)
  exact le_trans hshell
    (completedZeroMultiplicityCounting_mul_lowerDecay_le_countingEnvelope
      C d k m hcount_m)

/-- Multiplicity-aware counting dominates the unweighted shell decay by the
raw cumulative shell envelope. -/
theorem norm_completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    ‖completedZeroCenteredHeightShellDecayMass d k m‖ ≤
      completedZeroCenteredHeightShellCountingEnvelope C d k m := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroCenteredHeightShellCountingEnvelope C d k m)
    (norm_completedZeroCenteredHeightShellDecayMass_eq_self d k m).symm
    (completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
      C d k m hCpos hcount)

/-- The canonical tail base `1 + ‖m‖` is controlled by twice the lower shell
base `max 1 ‖m‖`. -/
theorem one_add_natNorm_le_two_mul_max_one_natNorm
    (m : ℕ) :
    1 + ‖((m : ℕ) : ℝ)‖ ≤
      (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ := by
  match Decidable.em (1 ≤ ‖((m : ℕ) : ℝ)‖) with
  | Or.inl hlarge =>
    have hmax :
        max 1 ‖((m : ℕ) : ℝ)‖ =
          ‖((m : ℕ) : ℝ)‖ :=
      max_eq_right hlarge
    have hadd :
        1 + ‖((m : ℕ) : ℝ)‖ ≤
          ‖((m : ℕ) : ℝ)‖ + ‖((m : ℕ) : ℝ)‖ :=
      add_le_add_right hlarge ‖((m : ℕ) : ℝ)‖
    have htwo :
        ‖((m : ℕ) : ℝ)‖ + ‖((m : ℕ) : ℝ)‖ =
          (2 : ℝ) * ‖((m : ℕ) : ℝ)‖ :=
      (two_mul ‖((m : ℕ) : ℝ)‖).symm
    have htarget :
        (2 : ℝ) * ‖((m : ℕ) : ℝ)‖ =
        (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ :=
      congrArg (fun x : ℝ => (2 : ℝ) * x) hmax.symm
    exact le_trans hadd (le_of_eq (Eq.trans htwo htarget))
  | Or.inr hlarge =>
    have hsmall :
        ‖((m : ℕ) : ℝ)‖ ≤ 1 :=
      le_of_not_ge hlarge
    have hmax :
        max 1 ‖((m : ℕ) : ℝ)‖ = 1 :=
      max_eq_left hsmall
    have hadd :
        1 + ‖((m : ℕ) : ℝ)‖ ≤ 1 + 1 :=
      add_le_add_left hsmall 1
    have hone_add_one :
        (1 : ℝ) + 1 = (2 : ℝ) * 1 :=
      (two_mul (1 : ℝ)).symm
    have htarget :
        (2 : ℝ) * 1 =
          (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ :=
      congrArg (fun x : ℝ => (2 : ℝ) * x) hmax.symm
    exact le_trans hadd (le_of_eq (Eq.trans hone_add_one htarget))

/-- The successor shell endpoint is the canonical tail base. -/
theorem natSucc_cast_eq_one_add_natNorm
    (m : ℕ) :
    (((m + 1 : ℕ) : ℝ)) = 1 + ‖((m : ℕ) : ℝ)‖ := by
  have hm_norm :
      ‖((m : ℕ) : ℝ)‖ = ((m : ℕ) : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg m)
  have hsucc :
      (((m + 1 : ℕ) : ℝ)) = ((m : ℕ) : ℝ) + 1 := by
    exact Nat.cast_add m 1
  have hcomm :
      ((m : ℕ) : ℝ) + 1 = 1 + ((m : ℕ) : ℝ) :=
    add_comm ((m : ℕ) : ℝ) 1
  have hnorm :
      1 + ((m : ℕ) : ℝ) = 1 + ‖((m : ℕ) : ℝ)‖ :=
    congrArg (fun x : ℝ => 1 + x) hm_norm.symm
  exact Eq.trans hsucc (Eq.trans hcomm hnorm)

/-- Abstract exponent bookkeeping for the shell envelope: if `b` is controlled
by `2 * a`, then the growth factor in `b` is absorbed by the stronger decay in
`a`, after enlarging the constant by `2 ^ D`. -/
theorem real_growth_decay_product_le_tail_of_baseComparison
    {a b : ℝ} (d D K : ℕ)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hbase : b ≤ (2 : ℝ) * a)
    (hdk : d + K ≤ D) :
    b ^ d * a ^ (-(D : ℤ)) ≤
      (2 : ℝ) ^ D * b ^ (-(K : ℤ)) := by
  have ha_pos : 0 < a :=
    lt_of_lt_of_le zero_lt_one ha
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_one hb
  have haD_pos : 0 < a ^ D :=
    pow_pos ha_pos D
  have hbK_pos : 0 < b ^ K :=
    pow_pos hb_pos K
  have hnum_left_eq :
      b ^ d * b ^ K = b ^ (d + K) :=
    (pow_add b d K).symm
  have hnum_left_le_D :
      b ^ (d + K) ≤ b ^ D :=
    pow_le_pow_right₀ hb hdk
  have hbase_pow :
      b ^ D ≤ ((2 : ℝ) * a) ^ D :=
    pow_le_pow_left₀ (le_trans zero_le_one hb) hbase D
  have hmul_pow :
      ((2 : ℝ) * a) ^ D = (2 : ℝ) ^ D * a ^ D :=
    mul_pow (2 : ℝ) a D
  have hnum :
      b ^ d * b ^ K ≤ (2 : ℝ) ^ D * a ^ D :=
    le_trans
      (Eq.subst
        (motive := fun x : ℝ => x ≤ b ^ D)
        hnum_left_eq.symm
        hnum_left_le_D)
      (le_trans hbase_pow (le_of_eq hmul_pow))
  have hdiv :
      b ^ d / a ^ D ≤ (2 : ℝ) ^ D / b ^ K :=
    (div_le_div_iff₀ haD_pos hbK_pos).mpr hnum
  have ha_zpow :
      a ^ (-(D : ℤ)) = (a ^ D)⁻¹ := by
    have hneg :
        a ^ (-(D : ℤ)) = (a ^ (D : ℤ))⁻¹ :=
      zpow_neg a (D : ℤ)
    have hnat :
        a ^ (D : ℤ) = a ^ D :=
      zpow_natCast a D
    exact Eq.trans hneg (congrArg Inv.inv hnat)
  have hb_zpow :
      b ^ (-(K : ℤ)) = (b ^ K)⁻¹ := by
    have hneg :
        b ^ (-(K : ℤ)) = (b ^ (K : ℤ))⁻¹ :=
      zpow_neg b (K : ℤ)
    have hnat :
        b ^ (K : ℤ) = b ^ K :=
      zpow_natCast b K
    exact Eq.trans hneg (congrArg Inv.inv hnat)
  have hleft :
      b ^ d * a ^ (-(D : ℤ)) = b ^ d / a ^ D :=
    Eq.trans
      (congrArg (fun x : ℝ => b ^ d * x) ha_zpow)
      (div_eq_mul_inv (b ^ d) (a ^ D)).symm
  have hright :
      (2 : ℝ) ^ D * b ^ (-(K : ℤ)) =
        (2 : ℝ) ^ D / b ^ K :=
    Eq.trans
      (congrArg (fun x : ℝ => (2 : ℝ) ^ D * x) hb_zpow)
      (div_eq_mul_inv ((2 : ℝ) ^ D) (b ^ K)).symm
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ (2 : ℝ) ^ D * b ^ (-(K : ℤ)))
    hleft.symm
    (Eq.subst
      (motive := fun x : ℝ => b ^ d / a ^ D ≤ x)
      hright.symm
      hdiv)

/-- Multiplying the abstract growth-decay comparison by a positive constant. -/
theorem real_const_mul_growth_decay_product_le_tail_of_baseComparison
    {a b C : ℝ} (d D K : ℕ)
    (hCpos : 0 < C)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hbase : b ≤ (2 : ℝ) * a)
    (hdk : d + K ≤ D) :
    C * (b ^ d * a ^ (-(D : ℤ))) ≤
      C * ((2 : ℝ) ^ D * b ^ (-(K : ℤ))) := by
  exact mul_le_mul_of_nonneg_left
    (real_growth_decay_product_le_tail_of_baseComparison
      d D K ha hb hbase hdk)
    (le_of_lt hCpos)

/-- The normalized shell envelope is bounded by the explicit tail constant once
all height-base comparisons are written in the canonical base
`1 + ‖m‖`. -/
theorem completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant_of_heightBase
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C) :
    completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
      completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  let a : ℝ := max 1 ‖((m : ℕ) : ℝ)‖
  let b : ℝ := 1 + ‖((m : ℕ) : ℝ)‖
  let D : ℕ := d + k + 3
  let K : ℕ := k + 2
  have ha : 1 ≤ a :=
    le_max_left 1 ‖((m : ℕ) : ℝ)‖
  have hb : 1 ≤ b :=
    le_add_of_nonneg_right (norm_nonneg ((m : ℕ) : ℝ))
  have hbase : b ≤ (2 : ℝ) * a :=
    one_add_natNorm_le_two_mul_max_one_natNorm m
  have hdk_eq :
      d + K = d + k + 2 := by
    change d + (k + 2) = d + k + 2
    exact (Nat.add_assoc d k 2).symm
  have hdk_le_raw :
      d + k + 2 ≤ d + k + 3 :=
    Nat.le_succ (d + k + 2)
  have hdk : d + K ≤ D := by
    change d + K ≤ d + k + 3
    exact Eq.subst
      (motive := fun x : ℕ => x ≤ d + k + 3)
      hdk_eq.symm
      hdk_le_raw
  have hsucc :
      (((m + 1 : ℕ) : ℝ)) = b := by
    change (((m + 1 : ℕ) : ℝ)) = 1 + ‖((m : ℕ) : ℝ)‖
    exact natSucc_cast_eq_one_add_natNorm m
  have hsucc_pow :
      (((m + 1 : ℕ) : ℝ) ^ d) = b ^ d :=
    congrArg (fun x : ℝ => x ^ d) hsucc
  have hcore :
      C * (b ^ d * a ^ (-(D : ℤ))) ≤
        C * ((2 : ℝ) ^ D * b ^ (-(K : ℤ))) :=
    real_const_mul_growth_decay_product_le_tail_of_baseComparison
      d D K hCpos ha hb hbase hdk
  change
    C * (((m + 1 : ℕ) : ℝ) ^ d) *
        (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) ≤
      C * (2 : ℝ) ^ (d + k + 3) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))
  have hleft :
      C * (((m + 1 : ℕ) : ℝ) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
        C * (b ^ d * a ^ (-(D : ℤ))) := by
    change
      C * (((m + 1 : ℕ) : ℝ) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
        C *
          (b ^ d *
            (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)))
    have hreplace :
        C * (((m + 1 : ℕ) : ℝ) ^ d) *
            (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
          C * (b ^ d) *
            (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) :=
      congrArg
        (fun x : ℝ =>
          C * x *
            (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)))
        hsucc_pow
    have hassoc :
        C * (b ^ d) *
            (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
          C *
            (b ^ d *
              (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))) :=
      mul_assoc C (b ^ d)
        ((max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)))
    exact Eq.trans hreplace hassoc
  have hright :
      C * (2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) =
        C * ((2 : ℝ) ^ D * b ^ (-(K : ℤ))) := by
    change
      C * (2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) =
        C *
          ((2 : ℝ) ^ (d + k + 3) *
            (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
    exact mul_assoc C ((2 : ℝ) ^ (d + k + 3))
      ((1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
    hleft.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        C * (b ^ d * a ^ (-(D : ℤ))) ≤ x)
      hright.symm
      hcore)

/-- The shell counting envelope is bounded by the explicit polynomial tail
constant. -/
theorem completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C) :
    completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
      completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant_of_heightBase
    C d k m hCpos

/-- The cumulative shell envelope is bounded by a one-dimensional polynomial
tail after increasing the constant. -/
theorem exists_completedZeroCenteredHeightShellCountingEnvelope_le_polynomialTail
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ m : ℕ,
        completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact ⟨completedZeroCenteredHeightShellTailConstant C d k,
    completedZeroCenteredHeightShellTailConstant_pos C d k hCpos,
    fun m =>
      completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant
        C d k m hCpos⟩

/-- Multiplicity-aware counting dominates the unweighted shell decay by a
one-dimensional polynomial tail after increasing the constant.

This is the exact estimate where positive zero multiplicity, shell containment,
and exponent bookkeeping meet. -/
theorem exists_norm_completedZeroCenteredHeightShellDecayMass_le_polynomialTail_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ m : ℕ,
        ‖completedZeroCenteredHeightShellDecayMass d k m‖ ≤
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  match exists_completedZeroCenteredHeightShellCountingEnvelope_le_polynomialTail
      C d k hCpos with
  | ⟨A, hApos, hA⟩ =>
      ⟨A, hApos, fun m =>
        le_trans
          (norm_completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
            C d k m hCpos hcount)
          (hA m)⟩

/-- The degree-aware shell masses are summable under the polynomial
multiplicity-counting bound. -/
theorem summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun m : ℕ =>
        completedZeroCenteredHeightShellDecayMass d k m) := by
  match exists_norm_completedZeroCenteredHeightShellDecayMass_le_polynomialTail_of_counting_bound
      C d k hCpos hcount with
  | ⟨A, _hApos, hA⟩ =>
      have htail :
          Summable
            (fun m : ℕ =>
              A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) :=
        (summable_one_add_nat_norm_negative_zpow_succ k).const_mul A
      Summable.of_norm_bounded
        (fun m : ℕ =>
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
        htail
        hA

/-- Polynomial negative-height envelopes are summable over completed zeros once
the decay exponent is chosen beyond the counting degree.

This is the p-series consequence of multiplicity-aware polynomial zero counting. -/
theorem summable_completedZero_centeredHeight_negativePower_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_completedZero_centeredHeight_negativePower_of_shellMass
    d
    k
    (summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
      C d k hCpos hcount)

/-- The completed-zero counting theorem supplies a counting degree after which
all further polynomial negative-height envelopes are summable. -/
theorem exists_summable_completedZero_centeredHeight_negativePower_with_countingMargin
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htailBoundary : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ d : ℕ,
      ∀ k : ℕ,
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  match exists_completedZeroMultiplicityCounting_height_bound
      hpartialOneTwo htailOneTwo hcompactOneTwo
      hpartialLeft htailBoundary hcompactBoundary with
  | ⟨C, d, hCpos, hcount⟩ =>
      ⟨d, fun k =>
        summable_completedZero_centeredHeight_negativePower_of_counting_bound
          C d k hCpos hcount⟩

end

end LFunctions
end Boundary
