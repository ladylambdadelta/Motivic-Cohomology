import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseNoWinding

/-!
# Real-phase resonance partition support

This file owns finite order lemmas used to replace global no-winding
hypotheses by resonance-aware interval decompositions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Compatibility name for singleton finsets in this file. -/
def Finset.singleton {α : Type*} [DecidableEq α] (a : α) : Finset α :=
  insert a ∅

/-- Remove an integer lattice slope from a real phase.  On integer samples this
does not change the associated unit complex exponential. -/
def Complex.realPhase_integerLatticeShift
    (φ : ℝ → ℝ)
    (k : ℤ)
    (x : ℝ) : ℝ :=
  φ x - (2 * Real.pi * (k : ℝ)) * x

/-- Exponential samples are invariant under removing an integer lattice slope. -/
theorem Complex.realPhase_integerLatticeShift_exp_eq
    (φ : ℝ → ℝ)
    (k : ℤ)
    (n : ℕ) :
    Complex.exp
        (Complex.I *
          (Complex.realPhase_integerLatticeShift φ k n : ℂ)) =
      Complex.exp (Complex.I * (φ n : ℂ)) := by
  have hperiod :
      Complex.exp
          (((φ n - (2 * Real.pi * (k : ℝ)) * (n : ℝ) : ℝ) : ℂ) *
            Complex.I) =
        Complex.exp ((φ n : ℂ) * Complex.I) :=
    Complex.exp_mul_I_real_sub_int_two_pi_mul_nat_period_for_logarithmicPhase
      (φ n) k n
  have hleft_arg :
      Complex.I *
          (Complex.realPhase_integerLatticeShift φ k n : ℂ) =
        ((φ n - (2 * Real.pi * (k : ℝ)) * (n : ℝ) : ℝ) : ℂ) *
          Complex.I := by
    unfold Complex.realPhase_integerLatticeShift
    exact mul_comm Complex.I
      ((φ (n : ℝ) - (2 * Real.pi * (k : ℝ)) * (n : ℝ) : ℝ) : ℂ)
  have hright_arg :
      (φ n : ℂ) * Complex.I =
        Complex.I * (φ n : ℂ) :=
    mul_comm (φ n : ℂ) Complex.I
  exact
    Eq.trans
      (congrArg Complex.exp hleft_arg)
      (Eq.trans hperiod
        (congrArg Complex.exp hright_arg))

/-- A finite exponential sum is unchanged after removing an integer lattice
slope from the phase. -/
theorem Complex.realPhase_integerLatticeShift_sum_eq
    (φ : ℝ → ℝ)
    (k : ℤ)
    (S : Finset ℕ) :
    (∑ n ∈ S,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_integerLatticeShift φ k n : ℂ))) =
      ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)) := by
  exact Finset.sum_congr rfl
    (fun n _hn =>
      Complex.realPhase_integerLatticeShift_exp_eq φ k n)

/-- Norm of a finite exponential sum is unchanged after removing an integer
lattice slope from the phase. -/
theorem Complex.realPhase_integerLatticeShift_sum_norm_eq
    (φ : ℝ → ℝ)
    (k : ℤ)
    (S : Finset ℕ) :
    ‖∑ n ∈ S,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_integerLatticeShift φ k n : ℂ))‖ =
      ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ :=
  congrArg norm
    (Complex.realPhase_integerLatticeShift_sum_eq φ k S)

/-- Any finite exponential-sum bound for the integer-lattice shifted phase
transfers back to the original phase on the same finite set. -/
theorem Complex.realPhase_sum_norm_le_of_integerLatticeShift_sum_norm_le
    (φ : ℝ → ℝ)
    (k : ℤ)
    (S : Finset ℕ)
    {M : ℝ}
    (hshift :
      ‖∑ n ∈ S,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_integerLatticeShift φ k n : ℂ))‖ ≤ M) :
    ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ M := by
  have hnorm :
      ‖∑ n ∈ S,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_integerLatticeShift φ k n : ℂ))‖ =
        ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    Complex.realPhase_integerLatticeShift_sum_norm_eq φ k S
  exact
    Eq.subst
      (motive := fun r : ℝ => r ≤ M)
      hnorm
      hshift

/-- Adjacent increments of an integer-lattice shifted phase are translated by
the chosen lattice frequency. -/
theorem Complex.realPhase_integerIncrement_integerLatticeShift_eq
    (φ : ℝ → ℝ)
    (k : ℤ)
    (n : ℕ) :
    Complex.realPhase_integerIncrement
        (Complex.realPhase_integerLatticeShift φ k) n =
      Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ)) := by
  let A : ℝ := 2 * Real.pi * (k : ℝ)
  have hsucc_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 :=
    Eq.trans
      (Nat.cast_add n 1)
      (congrArg (fun r : ℝ => (n : ℝ) + r) (Nat.cast_one))
  have hsucc_shift :
      Complex.realPhase_integerLatticeShift φ k (n + 1 : ℕ) =
        φ (n + 1 : ℕ) - A * ((n : ℝ) + 1) := by
    unfold Complex.realPhase_integerLatticeShift A
    exact congrArg
      (fun x : ℝ => φ (n + 1 : ℕ) - (2 * Real.pi * (k : ℝ)) * x)
      hsucc_cast
  have hn_shift :
      Complex.realPhase_integerLatticeShift φ k n =
        φ n - A * (n : ℝ) := by
    exact Eq.refl (Complex.realPhase_integerLatticeShift φ k n)
  have hraw :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n =
        (φ (n + 1 : ℕ) - A * ((n : ℝ) + 1)) -
          (φ n - A * (n : ℝ)) := by
    unfold Complex.realPhase_integerIncrement
    exact
      Eq.trans
        (congrArg
          (fun x : ℝ => x - Complex.realPhase_integerLatticeShift φ k n)
          hsucc_shift)
        (congrArg
          (fun x : ℝ => (φ (n + 1 : ℕ) - A * ((n : ℝ) + 1)) - x)
          hn_shift)
  have hlinear :
      A * ((n : ℝ) + 1) = A * (n : ℝ) + A := by
    exact Eq.trans (mul_add A (n : ℝ) 1)
      (congrArg (fun r : ℝ => A * (n : ℝ) + r) (mul_one A))
  have hneg_linear :
      -(A * ((n : ℝ) + 1)) =
        -(A * (n : ℝ)) + -A := by
    exact Eq.trans
      (congrArg Neg.neg hlinear)
      (neg_add (A * (n : ℝ)) A)
  have harith :
      (φ (n + 1 : ℕ) - A * ((n : ℝ) + 1)) -
          (φ n - A * (n : ℝ)) =
        (φ (n + 1 : ℕ) - φ n) - A := by
    calc
      (φ (n + 1 : ℕ) - A * ((n : ℝ) + 1)) -
          (φ n - A * (n : ℝ)) =
        (φ (n + 1 : ℕ) + -(A * ((n : ℝ) + 1))) +
          (-(φ n) + A * (n : ℝ)) := by
        have hright :
            -(φ n - A * (n : ℝ)) = -(φ n) + A * (n : ℝ) := by
          calc
            -(φ n - A * (n : ℝ)) =
                A * (n : ℝ) - φ n := by
              exact neg_sub (φ n) (A * (n : ℝ))
            _ = A * (n : ℝ) + -(φ n) := by
              exact sub_eq_add_neg (A * (n : ℝ)) (φ n)
            _ = -(φ n) + A * (n : ℝ) := by
              exact add_comm (A * (n : ℝ)) (-(φ n))
        exact congrArg₂ HAdd.hAdd
          (sub_eq_add_neg (φ (n + 1 : ℕ)) (A * ((n : ℝ) + 1)))
          hright
      _ =
        (φ (n + 1 : ℕ) + (-(A * (n : ℝ)) + -A)) +
          (-(φ n) + A * (n : ℝ)) := by
        exact congrArg
          (fun r : ℝ => (φ (n + 1 : ℕ) + r) + (-(φ n) + A * (n : ℝ)))
          hneg_linear
      _ =
        ((φ (n + 1 : ℕ) + -(φ n)) +
          ((-(A * (n : ℝ)) + -A) + A * (n : ℝ))) := by
        exact add_add_add_comm
          (φ (n + 1 : ℕ))
          (-(A * (n : ℝ)) + -A)
          (-(φ n))
          (A * (n : ℝ))
      _ =
        ((φ (n + 1 : ℕ) + -(φ n)) +
          (-A + (-(A * (n : ℝ)) + A * (n : ℝ)))) := by
        have hcomm :
            (-(A * (n : ℝ)) + -A) + A * (n : ℝ) =
              -A + (-(A * (n : ℝ)) + A * (n : ℝ)) := by
          calc
            (-(A * (n : ℝ)) + -A) + A * (n : ℝ) =
                -(A * (n : ℝ)) + (-A + A * (n : ℝ)) := by
              exact add_assoc (-(A * (n : ℝ))) (-A) (A * (n : ℝ))
            _ = -(A * (n : ℝ)) + (A * (n : ℝ) + -A) := by
              exact congrArg
                (fun r : ℝ => -(A * (n : ℝ)) + r)
                (add_comm (-A) (A * (n : ℝ)))
            _ = (-(A * (n : ℝ)) + A * (n : ℝ)) + -A := by
              exact (add_assoc (-(A * (n : ℝ))) (A * (n : ℝ)) (-A)).symm
            _ = -A + (-(A * (n : ℝ)) + A * (n : ℝ)) := by
              exact add_comm (-(A * (n : ℝ)) + A * (n : ℝ)) (-A)
        exact congrArg
          (fun r : ℝ => (φ (n + 1 : ℕ) + -(φ n)) + r)
          hcomm
      _ =
        ((φ (n + 1 : ℕ) + -(φ n)) + (-A + 0)) := by
        exact congrArg
          (fun r : ℝ => (φ (n + 1 : ℕ) + -(φ n)) + (-A + r))
          (neg_add_cancel (A * (n : ℝ)))
      _ =
        ((φ (n + 1 : ℕ) + -(φ n)) + -A) := by
        exact congrArg
          (fun r : ℝ => (φ (n + 1 : ℕ) + -(φ n)) + r)
          (add_zero (-A))
      _ =
        (φ (n + 1 : ℕ) - φ n) + -A := by
        exact congrArg
          (fun r : ℝ => r + -A)
          (sub_eq_add_neg (φ (n + 1 : ℕ)) (φ n)).symm
      _ =
        (φ (n + 1 : ℕ) - φ n) - A :=
        (sub_eq_add_neg (φ (n + 1 : ℕ) - φ n) A).symm
  exact
    Eq.trans hraw
      (Eq.trans harith
        (congrArg (fun r : ℝ => r - A)
          (Eq.refl (Complex.realPhase_integerIncrement φ n))))

/-- A `2πk`-centered resonance condition for a phase is exactly the
zero-centered resonance condition for the integer-lattice shifted phase. -/
theorem Complex.realPhase_integerIncrement_integerLatticeShift_zero_resonance_iff
    (φ : ℝ → ℝ)
    (k : ℤ)
    (n : ℕ)
    (lam : ℝ) :
    ‖Complex.realPhase_integerIncrement
        (Complex.realPhase_integerLatticeShift φ k) n -
        (2 * Real.pi * (0 : ℝ))‖ < lam ↔
      ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ < lam := by
  have hzero :
      2 * Real.pi * (0 : ℝ) = 0 := by
    exact mul_zero (2 * Real.pi)
  have hinc :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ)) :=
    Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
  have hleft :
      ‖Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n -
          (2 * Real.pi * (0 : ℝ))‖ =
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ := by
    calc
      ‖Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n -
          (2 * Real.pi * (0 : ℝ))‖ =
        ‖Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n - 0‖ := by
        exact congrArg
          (fun r : ℝ =>
            ‖Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n - r‖)
          hzero
      _ =
        ‖Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n‖ := by
        exact congrArg norm
          (sub_zero
            (Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n))
      _ =
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ := by
        exact congrArg norm hinc
  exact
    Iff.intro
      (fun h =>
        Eq.subst
          (motive := fun r : ℝ => r < lam)
          hleft
          h)
      (fun h =>
        Eq.subst
          (motive := fun r : ℝ => r < lam)
          hleft.symm
          h)

/-! Canonical resonance windows are placed here before the integer-lattice
transport lemmas that consume them. -/

/-- The canonical finite resonant-index set for adjacent increments inside a
half-open natural block. -/
def Complex.realPhase_integerIncrementResonanceWindow
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (resonance lam : ℝ) : Finset ℕ :=
  (Finset.Ico a b).filter
    (fun n : ℕ =>
      ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)

/-- Membership in the canonical resonant-index set is exactly block
membership plus proximity to the chosen resonance center. -/
theorem Complex.mem_realPhase_integerIncrementResonanceWindow_iff
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {resonance lam : ℝ} :
    n ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam ↔
      n ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam := by
  exact Finset.mem_filter

/-- The nonresonant complement of a canonical adjacent-increment resonance
window inside a half-open natural block. -/
def Complex.realPhase_integerIncrementResonanceWindowComplement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (resonance lam : ℝ) : Finset ℕ :=
  (Finset.Ico a b).filter
    (fun n : ℕ =>
      ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)

/-- Membership in the nonresonant complement is exactly block membership plus
avoidance of the chosen resonance window. -/
theorem Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {resonance lam : ℝ} :
    n ∈ Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b resonance lam ↔
      n ∈ Finset.Ico a b ∧
        ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam := by
  exact Finset.mem_filter

/-- The `2πk`-centered resonance window for a phase is the zero-centered
resonance window for the integer-lattice shifted phase. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_integerLatticeShift_zero_eq
    (φ : ℝ → ℝ)
    (k : ℤ)
    (a b : ℕ)
    (lam : ℝ) :
    Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_integerLatticeShift φ k)
        a b (2 * Real.pi * (0 : ℝ)) lam =
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hdata :
              n ∈ Finset.Ico a b ∧
                ‖Complex.realPhase_integerIncrement
                    (Complex.realPhase_integerLatticeShift φ k) n -
                    (2 * Real.pi * (0 : ℝ))‖ < lam :=
            (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
              (φ := Complex.realPhase_integerLatticeShift φ k)
              (a := a)
              (b := b)
              (n := n)
              (resonance := 2 * Real.pi * (0 : ℝ))
              (lam := lam)).mp hn
          (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
            (φ := φ)
            (a := a)
            (b := b)
            (n := n)
            (resonance := 2 * Real.pi * (k : ℝ))
            (lam := lam)).mpr
            (And.intro hdata.1
              ((Complex.realPhase_integerIncrement_integerLatticeShift_zero_resonance_iff
                φ k n lam).mp hdata.2)))
        (fun hn =>
          have hdata :
              n ∈ Finset.Ico a b ∧
                ‖Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ))‖ < lam :=
            (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
              (φ := φ)
              (a := a)
              (b := b)
              (n := n)
              (resonance := 2 * Real.pi * (k : ℝ))
              (lam := lam)).mp hn
          (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
            (φ := Complex.realPhase_integerLatticeShift φ k)
            (a := a)
            (b := b)
            (n := n)
            (resonance := 2 * Real.pi * (0 : ℝ))
            (lam := lam)).mpr
            (And.intro hdata.1
              ((Complex.realPhase_integerIncrement_integerLatticeShift_zero_resonance_iff
                φ k n lam).mpr hdata.2))))

/-- Raw integer-increment monotonicity is preserved by removing a fixed
integer lattice slope. -/
theorem Complex.realPhase_integerIncrementMonotoneOn_integerLatticeShift
    (φ : ℝ → ℝ)
    (k : ℤ)
    {a b : ℕ}
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.realPhase_integerLatticeShift φ k) a b := by
  match hmono with
  | Or.inl hinc =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m =
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k m
          have hn_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n =
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
          have hraw :
              Complex.realPhase_integerIncrement φ m ≤
                Complex.realPhase_integerIncrement φ n :=
            hinc hm hn hmn
          have hshift :
              Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) ≤
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            sub_le_sub_right hraw (2 * Real.pi * (k : ℝ))
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n)
            hm_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ m -
                    (2 * Real.pi * (k : ℝ)) ≤ right)
              hn_eq.symm
              hshift))
  | Or.inr hdec =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m =
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k m
          have hn_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n =
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
          have hraw :
              Complex.realPhase_integerIncrement φ n ≤
                Complex.realPhase_integerIncrement φ m :=
            hdec hm hn hmn
          have hshift :
              Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) ≤
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            sub_le_sub_right hraw (2 * Real.pi * (k : ℝ))
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m)
            hn_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ)) ≤ right)
              hm_eq.symm
              hshift))

/-- Reduced increment monotonicity for an integer-lattice shifted phase follows
from raw monotonicity and principal-branch control of the shifted increments. -/
theorem Complex.realPhase_reducedIntegerIncrementMonotoneOn_integerLatticeShift_of_principal
    (φ : ℝ → ℝ)
    (k : ℤ)
    {a b : ℕ}
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn
      (Complex.realPhase_integerLatticeShift φ k) a b := by
  exact
    Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
      (Complex.realPhase_integerLatticeShift φ k)
      (Complex.realPhase_integerIncrementMonotoneOn_integerLatticeShift
        φ k hmono)
      hprincipal

/-- Principal-branch strip for the adjacent increments after subtracting an
integer lattice slope. -/
def Complex.realPhase_integerIncrementPrincipalStrip
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (k : ℤ) : Finset ℕ :=
  (Finset.Ico a b).filter
    (fun n : ℕ =>
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))

/-- Membership in an integer-lattice principal strip. -/
theorem Complex.mem_realPhase_integerIncrementPrincipalStrip_iff
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {k : ℤ} :
    n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k ↔
      n ∈ Finset.Ico a b ∧
        Complex.realPhase_integerIncrement
            (Complex.realPhase_integerLatticeShift φ k) n ∈
          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  exact Finset.mem_filter

/-- A principal strip is contained in its ambient half-open block. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_subset_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {k : ℤ} :
    Complex.realPhase_integerIncrementPrincipalStrip φ a b k ⊆
      Finset.Ico a b := by
  intro n hn
  exact
    (Complex.mem_realPhase_integerIncrementPrincipalStrip_iff
      φ).mp hn |>.1

/-- Points of a principal strip satisfy the principal-branch condition for its
integer lattice shift. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_principal
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {k : ℤ}
    (hn : n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k) :
    Complex.realPhase_integerIncrement
        (Complex.realPhase_integerLatticeShift φ k) n ∈
      Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  exact
    (Complex.mem_realPhase_integerIncrementPrincipalStrip_iff
      φ).mp hn |>.2

/-- Negating an integer lattice shift by `2π` is the same as negating the
corresponding real integer multiple. -/
theorem Real.neg_zsmul_two_pi_eq_neg_two_pi_mul_int
    (k : ℤ) :
    (-k) • ((2 * Real.pi) : ℝ) =
      -(2 * Real.pi * (k : ℝ)) := by
  calc
    (-k) • ((2 * Real.pi) : ℝ) =
        ((-k : ℤ) : ℝ) * (2 * Real.pi) :=
      zsmul_eq_mul (2 * Real.pi) (-k)
    _ = (-(k : ℝ)) * (2 * Real.pi) :=
      congrArg (fun r : ℝ => r * (2 * Real.pi)) (Int.cast_neg k)
    _ = -((k : ℝ) * (2 * Real.pi)) :=
      neg_mul (k : ℝ) (2 * Real.pi)
    _ = -(2 * Real.pi * (k : ℝ)) :=
      congrArg Neg.neg (mul_comm (k : ℝ) (2 * Real.pi))

/-- The integer lattice translate that puts an angle in the principal
`(-π, π]` branch is unique. -/
theorem Real.sub_two_pi_mul_int_mem_principal_unique
    {θ : ℝ}
    {k l : ℤ}
    (hk :
      θ - (2 * Real.pi * (k : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (hl :
      θ - (2 * Real.pi * (l : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    k = l := by
  have hunique :
      ∃! m : ℤ,
        θ + m • ((2 * Real.pi) : ℝ) ∈
          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos θ (-Real.pi)
  have hk_add :
      θ + (-k) • ((2 * Real.pi) : ℝ) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
    have hk_eq :
        θ + (-k) • ((2 * Real.pi) : ℝ) =
          θ - (2 * Real.pi * (k : ℝ)) :=
      Eq.trans
        (congrArg
          (fun r : ℝ => θ + r)
          (Real.neg_zsmul_two_pi_eq_neg_two_pi_mul_int k))
        (sub_eq_add_neg θ (2 * Real.pi * (k : ℝ))).symm
    exact
      Eq.subst
        (motive := fun value : ℝ =>
          value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
        hk_eq.symm
        hk
  have hl_add :
      θ + (-l) • ((2 * Real.pi) : ℝ) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
    have hl_eq :
        θ + (-l) • ((2 * Real.pi) : ℝ) =
          θ - (2 * Real.pi * (l : ℝ)) :=
      Eq.trans
        (congrArg
          (fun r : ℝ => θ + r)
          (Real.neg_zsmul_two_pi_eq_neg_two_pi_mul_int l))
        (sub_eq_add_neg θ (2 * Real.pi * (l : ℝ))).symm
    exact
      Eq.subst
        (motive := fun value : ℝ =>
          value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
        hl_eq.symm
        hl
  have hneg : -k = -l :=
    ExistsUnique.unique hunique hk_add hl_add
  exact neg_injective hneg

/-- A sample belongs to at most one integer principal strip. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_center_unique
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {k l : ℤ}
    (hnk :
      n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k)
    (hnl :
      n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b l) :
    k = l := by
  have hk_shift :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ)) :=
    Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
  have hl_shift :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ l) n =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (l : ℝ)) :=
    Complex.realPhase_integerIncrement_integerLatticeShift_eq φ l n
  have hk_principal_shift :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    Complex.realPhase_integerIncrementPrincipalStrip_principal φ hnk
  have hl_principal_shift :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ l) n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    Complex.realPhase_integerIncrementPrincipalStrip_principal φ hnl
  have hk_principal :
      Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
      hk_shift
      hk_principal_shift
  have hl_principal :
      Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (l : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
      hl_shift
      hl_principal_shift
  exact
    Real.sub_two_pi_mul_int_mem_principal_unique
      hk_principal hl_principal

/-- Different principal strips are disjoint at the sample level. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_disjoint_of_ne
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {k l : ℤ}
    (hkl : k ≠ l) :
    Disjoint
      (Complex.realPhase_integerIncrementPrincipalStrip φ a b k)
      (Complex.realPhase_integerIncrementPrincipalStrip φ a b l) := by
  exact
    Finset.disjoint_left.mpr
      (fun n hn_k hn_l =>
        have hcenter :
            k = l :=
          Complex.realPhase_integerIncrementPrincipalStrip_center_unique
            φ hn_k hn_l
        hkl hcenter)

/-- Every real angle has an integer lattice translate in the principal
branch. -/
theorem Real.exists_int_sub_two_pi_mul_mem_principal
    (θ : ℝ) :
    ∃ k : ℤ,
      θ - (2 * Real.pi * (k : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  match Complex.realPhase_twoPi_toIocMod_integerDistance θ with
  | ⟨k, hk⟩ =>
      have hmod :
          toIocMod Real.two_pi_pos (-Real.pi) θ ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
        real_mem_Ioc_pi_to_periodic_upper_for_logarithmicPhase
          (real_toIocMod_mem_Ioc_pi_for_logarithmicPhase θ)
      exact Exists.intro k
        (Eq.subst
          (motive := fun value : ℝ =>
            value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
          hk.symm
          hmod)

/-- Every sample increment has an integer lattice translate in the principal
branch. -/
theorem Complex.realPhase_integerIncrement_exists_principal_latticeShift
    (φ : ℝ → ℝ)
    (n : ℕ) :
    ∃ k : ℤ,
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  match
    Real.exists_int_sub_two_pi_mul_mem_principal
      (Complex.realPhase_integerIncrement φ n) with
  | ⟨k, hk⟩ =>
      have hshift :
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n =
            Complex.realPhase_integerIncrement φ n -
              (2 * Real.pi * (k : ℝ)) :=
        Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
      exact Exists.intro k
        (Eq.subst
          (motive := fun value : ℝ =>
            value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
          hshift.symm
          hk)

/-- For a monotone real sequence, membership in a fixed half-open interval is
interval-convex. -/
theorem Real.monotoneOn_mem_Ioc_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {lower upper : ℝ}
    (hmono : MonotoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_interval : f i ∈ Set.Ioc lower upper)
    (hk_interval : f k ∈ Set.Ioc lower upper) :
    f j ∈ Set.Ioc lower upper := by
  have hleft_le : f i ≤ f j :=
    hmono hi_mem hj_mem hij
  have hright_le : f j ≤ f k :=
    hmono hj_mem hk_mem hjk
  exact
    And.intro
      (lt_of_lt_of_le hi_interval.1 hleft_le)
      (le_trans hright_le hk_interval.2)

/-- For an antitone real sequence, membership in a fixed half-open interval is
interval-convex. -/
theorem Real.antitoneOn_mem_Ioc_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {lower upper : ℝ}
    (hanti : AntitoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_interval : f i ∈ Set.Ioc lower upper)
    (hk_interval : f k ∈ Set.Ioc lower upper) :
    f j ∈ Set.Ioc lower upper := by
  have hleft_le : f k ≤ f j :=
    hanti hj_mem hk_mem hjk
  have hright_le : f j ≤ f i :=
    hanti hi_mem hj_mem hij
  exact
    And.intro
      (lt_of_lt_of_le hk_interval.1 hleft_le)
      (le_trans hright_le hi_interval.2)

/-- Principal strips for a real phase with monotone adjacent increments are
interval-convex inside the adjacent-increment index block. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_intervalConvex
    (φ : ℝ → ℝ)
    (k₀ : ℤ)
    {a b i j k : ℕ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_principal :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k₀) i ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (hk_principal :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k₀) k ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_integerIncrement
        (Complex.realPhase_integerLatticeShift φ k₀) j ∈
      Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  have hshift_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k₀) a b :=
    Complex.realPhase_integerIncrementMonotoneOn_integerLatticeShift
      φ k₀ hinc_mono
  match hshift_mono with
  | Or.inl hmono =>
      exact
        Real.monotoneOn_mem_Ioc_intervalConvex
          hmono hi_mem hj_mem hk_mem hij hjk
          hi_principal hk_principal
  | Or.inr hanti =>
      exact
        Real.antitoneOn_mem_Ioc_intervalConvex
          hanti hi_mem hj_mem hk_mem hij hjk
          hi_principal hk_principal

/-- A finite subset of a half-open natural interval that is interval-convex is
itself a half-open interval. -/
theorem Finset.exists_eq_Ico_of_subset_Ico_intervalConvex
    {S : Finset ℕ}
    {a b : ℕ}
    (hab : a ≤ b)
    (hS_block : S ⊆ Finset.Ico a b)
    (hconvex :
      ∀ i j k : ℕ,
        i ∈ S →
        k ∈ S →
        j ∈ Finset.Ico a b →
        i ≤ j →
        j ≤ k →
          j ∈ S) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ S = Finset.Ico c d := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : a ≤ n ∧ n < a :=
              Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact Exists.intro a
        (Exists.intro a
          (And.intro le_rfl
            (And.intro le_rfl
              (And.intro hab
                (Eq.trans hS_empty hIco_empty.symm)))))
  | Or.inr hS_nonempty =>
      let c : ℕ := S.min' hS_nonempty
      let r : ℕ := S.max' hS_nonempty
      let d : ℕ := r + 1
      have hc_mem : c ∈ S :=
        Finset.min'_mem S hS_nonempty
      have hr_mem : r ∈ S :=
        Finset.max'_mem S hS_nonempty
      have hc_block : c ∈ Finset.Ico a b :=
        hS_block hc_mem
      have hr_block : r ∈ Finset.Ico a b :=
        hS_block hr_mem
      have hc_bounds : a ≤ c ∧ c < b :=
        Finset.mem_Ico.mp hc_block
      have hr_bounds : a ≤ r ∧ r < b :=
        Finset.mem_Ico.mp hr_block
      have hc_le_r : c ≤ r :=
        Finset.min'_le S r hr_mem
      have hc_le_d : c ≤ d :=
        Nat.le_trans hc_le_r (Nat.le_succ r)
      have hd_right : d ≤ b :=
        Nat.succ_le_of_lt hr_bounds.2
      have hS_eq : S = Finset.Ico c d :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hc_le_n : c ≤ n :=
                  Finset.min'_le S n hn
                have hn_le_r : n ≤ r :=
                  Finset.le_max' S n hn
                have hn_lt_d : n < d :=
                  Nat.lt_succ_of_le hn_le_r
                Finset.mem_Ico.mpr (And.intro hc_le_n hn_lt_d))
              (fun hn_interval =>
                have hn_bounds : c ≤ n ∧ n < d :=
                  Finset.mem_Ico.mp hn_interval
                have hn_le_r : n ≤ r :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Ico a b :=
                  Finset.mem_Ico.mpr
                    (And.intro
                      (Nat.le_trans hc_bounds.1 hn_bounds.1)
                      (lt_of_le_of_lt hn_le_r hr_bounds.2))
                hconvex c n r hc_mem hr_mem hn_block hn_bounds.1 hn_le_r))
      exact Exists.intro c
        (Exists.intro d
          (And.intro hc_bounds.1
            (And.intro hc_le_d
              (And.intro hd_right hS_eq))))

/-- A finite principal-strip index set for monotone adjacent increments is a
half-open interval. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_exists
    (φ : ℝ → ℝ)
    (k : ℤ)
    {a b : ℕ}
    (hab : a ≤ b)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
        Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
          Finset.Ico c d := by
  have hsubset :
      Complex.realPhase_integerIncrementPrincipalStrip φ a b k ⊆
        Finset.Ico a b :=
    Complex.realPhase_integerIncrementPrincipalStrip_subset_block φ
  have hconvex :
      ∀ i j r : ℕ,
        i ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k →
          r ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k →
            j ∈ Finset.Ico a b →
              i ≤ j →
                j ≤ r →
                  j ∈ Complex.realPhase_integerIncrementPrincipalStrip
                    φ a b k := by
    intro i j r hi hr hj hij hjr
    have hi_data :
        i ∈ Finset.Ico a b ∧
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) i ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
      (Complex.mem_realPhase_integerIncrementPrincipalStrip_iff
        φ).mp hi
    have hr_data :
        r ∈ Finset.Ico a b ∧
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) r ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
      (Complex.mem_realPhase_integerIncrementPrincipalStrip_iff
        φ).mp hr
    have hj_principal :
        Complex.realPhase_integerIncrement
            (Complex.realPhase_integerLatticeShift φ k) j ∈
          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
      Complex.realPhase_integerIncrementPrincipalStrip_intervalConvex
        φ k hinc_mono hi_data.1 hj hr_data.1 hij hjr
        hi_data.2 hr_data.2
    exact
      (Complex.mem_realPhase_integerIncrementPrincipalStrip_iff
        φ).mpr
        (And.intro hj hj_principal)
  exact
    Finset.exists_eq_Ico_of_subset_Ico_intervalConvex
      hab hsubset hconvex

/-- For a monotone real sequence, the set of indices lying within a fixed
open distance from a fixed resonance center is interval-convex. -/
theorem Real.monotoneOn_abs_sub_lt_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {center lam : ℝ}
    (hmono : MonotoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res : ‖f i - center‖ < lam)
    (hk_res : ‖f k - center‖ < lam) :
    ‖f j - center‖ < lam := by
  have hi_bounds :
      -lam < f i - center ∧ f i - center < lam :=
    abs_lt.mp hi_res
  have hk_bounds :
      -lam < f k - center ∧ f k - center < lam :=
    abs_lt.mp hk_res
  have hfij : f i ≤ f j :=
    hmono hi_mem hj_mem hij
  have hfjk : f j ≤ f k :=
    hmono hj_mem hk_mem hjk
  have hleft_le :
      f i - center ≤ f j - center :=
    sub_le_sub_right hfij center
  have hright_le :
      f j - center ≤ f k - center :=
    sub_le_sub_right hfjk center
  have hleft :
      -lam < f j - center :=
    lt_of_lt_of_le hi_bounds.1 hleft_le
  have hright :
      f j - center < lam :=
    lt_of_le_of_lt hright_le hk_bounds.2
  exact abs_lt.mpr (And.intro hleft hright)

/-- For an antitone real sequence, the set of indices lying within a fixed
open distance from a fixed resonance center is interval-convex. -/
theorem Real.antitoneOn_abs_sub_lt_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {center lam : ℝ}
    (hanti : AntitoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res : ‖f i - center‖ < lam)
    (hk_res : ‖f k - center‖ < lam) :
    ‖f j - center‖ < lam := by
  have hi_bounds :
      -lam < f i - center ∧ f i - center < lam :=
    abs_lt.mp hi_res
  have hk_bounds :
      -lam < f k - center ∧ f k - center < lam :=
    abs_lt.mp hk_res
  have hfj_le_fi : f j ≤ f i :=
    hanti hi_mem hj_mem hij
  have hfk_le_fj : f k ≤ f j :=
    hanti hj_mem hk_mem hjk
  have hleft_le :
      f k - center ≤ f j - center :=
    sub_le_sub_right hfk_le_fj center
  have hright_le :
      f j - center ≤ f i - center :=
    sub_le_sub_right hfj_le_fi center
  have hleft :
      -lam < f j - center :=
    lt_of_lt_of_le hk_bounds.1 hleft_le
  have hright :
      f j - center < lam :=
    lt_of_le_of_lt hright_le hi_bounds.2
  exact abs_lt.mpr (And.intro hleft hright)

/-- Near-resonance sets for a sequence with a chosen monotonicity branch are
interval-convex. -/
theorem Real.monoOrAntiOn_abs_sub_lt_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {center lam : ℝ}
    (hmono_or_anti :
      MonotoneOn f (Finset.Ico a b : Set ℕ) ∨
        AntitoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res : ‖f i - center‖ < lam)
    (hk_res : ‖f k - center‖ < lam) :
    ‖f j - center‖ < lam :=
  match hmono_or_anti with
  | Or.inl hmono =>
      Real.monotoneOn_abs_sub_lt_intervalConvex
        hmono hi_mem hj_mem hk_mem hij hjk hi_res hk_res
  | Or.inr hanti =>
      Real.antitoneOn_abs_sub_lt_intervalConvex
        hanti hi_mem hj_mem hk_mem hij hjk hi_res hk_res

/-- Resonance windows for a real phase with monotone adjacent increments are
interval-convex inside the adjacent-increment index block. -/
theorem Complex.realPhase_integerIncrement_resonance_intervalConvex
    (φ : ℝ → ℝ)
    {a b i j k : ℕ}
    {resonance lam : ℝ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res :
      ‖Complex.realPhase_integerIncrement φ i - resonance‖ < lam)
    (hk_res :
      ‖Complex.realPhase_integerIncrement φ k - resonance‖ < lam) :
    ‖Complex.realPhase_integerIncrement φ j - resonance‖ < lam :=
  Real.monoOrAntiOn_abs_sub_lt_intervalConvex
    hinc_mono hi_mem hj_mem hk_mem hij hjk hi_res hk_res

/-- A finite resonant-index set for monotone adjacent increments is a
half-open resonant window.  The set is supplied by an extensional membership
law, so this lemma does not need to manufacture decidability for the resonance
predicate. -/
theorem Complex.realPhase_integerIncrement_resonanceWindow_exists
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {resonance lam : ℝ}
    (hab : a ≤ b)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ S = Finset.Ico c d := by
  have hS_block : S ⊆ Finset.Ico a b := by
    intro n hn
    have hn_pair :
        n ∈ Finset.Ico a b ∧
          ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam :=
      (hS n).mp hn
    exact hn_pair.1
  have hconvex :
      ∀ i j k : ℕ,
        i ∈ S →
        k ∈ S →
        j ∈ Finset.Ico a b →
        i ≤ j →
        j ≤ k →
          j ∈ S := by
    intro i j k hi hk hj_block hij hjk
    have hi_pair :
        i ∈ Finset.Ico a b ∧
          ‖Complex.realPhase_integerIncrement φ i - resonance‖ < lam :=
      (hS i).mp hi
    have hk_pair :
        k ∈ Finset.Ico a b ∧
          ‖Complex.realPhase_integerIncrement φ k - resonance‖ < lam :=
      (hS k).mp hk
    have hj_res :
        ‖Complex.realPhase_integerIncrement φ j - resonance‖ < lam :=
      Complex.realPhase_integerIncrement_resonance_intervalConvex
        φ hinc_mono hi_pair.1 hj_block hk_pair.1 hij hjk
        hi_pair.2 hk_pair.2
    exact (hS j).mpr (And.intro hj_block hj_res)
  exact
    Finset.exists_eq_Ico_of_subset_Ico_intervalConvex
      hab hS_block hconvex

/-- A point in the nonresonant complement is not in the resonant window with
the same center and width. -/
theorem Complex.not_mem_realPhase_integerIncrementResonanceWindow_of_mem_complement
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {resonance lam : ℝ}
    (hn :
      n ∈ Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b resonance lam) :
    n ∉ Complex.realPhase_integerIncrementResonanceWindow
      φ a b resonance lam := by
  have hn_data :
      n ∈ Finset.Ico a b ∧
        ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n)
      (resonance := resonance)
      (lam := lam)).mp hn
  intro hn_window
  have hn_window_data :
      n ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n)
      (resonance := resonance)
      (lam := lam)).mp hn_window
  exact hn_data.2 hn_window_data.2

/-- The resonant window and its nonresonant complement split the ambient
half-open natural block. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_union_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (resonance lam : ℝ) :
    Complex.realPhase_integerIncrementResonanceWindow φ a b resonance lam ∪
        Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b resonance lam =
      Finset.Ico a b := by
  exact
    Finset.filter_union_filter_neg_eq
      (s := Finset.Ico a b)
      (p := fun n : ℕ =>
        ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)

/-- The resonant window and its nonresonant complement are disjoint. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_disjoint_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (resonance lam : ℝ) :
    Disjoint
      (Complex.realPhase_integerIncrementResonanceWindow φ a b resonance lam)
      (Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b resonance lam) := by
  exact Finset.disjoint_filter_filter_neg
    (Finset.Ico a b)
    (Finset.Ico a b)
    (fun n : ℕ =>
      ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)

/-- A sum over a half-open block splits into the resonant window contribution
and the nonresonant complement contribution. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_sum_add_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (resonance lam : ℝ)
    (F : ℕ → ℂ) :
    (∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam, F n) +
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceWindowComplement
            φ a b resonance lam, F n) =
      ∑ n ∈ Finset.Ico a b, F n := by
  have hraw :
      (∑ n ∈ (Finset.Ico a b).filter
          (fun n : ℕ =>
            ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam),
          F n) +
        (∑ n ∈ (Finset.Ico a b).filter
          (fun n : ℕ =>
            ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam),
          F n) =
      ∑ n ∈ Finset.Ico a b, F n :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.Ico a b)
      (p := fun n : ℕ =>
        ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)
      (f := F)
  exact hraw

/-- Norm form of the resonant-window/nonresonant-complement split. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_sum_norm_le
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (resonance lam : ℝ)
    (F : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Ico a b, F n‖ ≤
      ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam, F n‖ +
        ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceWindowComplement
            φ a b resonance lam, F n‖ := by
  have hsum :
      (∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam, F n) +
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceWindowComplement
            φ a b resonance lam, F n) =
      ∑ n ∈ Finset.Ico a b, F n :=
    Complex.realPhase_integerIncrementResonanceWindow_sum_add_complement
      φ a b resonance lam F
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
              φ a b resonance lam, F n‖ +
            ‖∑ n ∈
              Complex.realPhase_integerIncrementResonanceWindowComplement
                φ a b resonance lam, F n‖)
      hsum
      (norm_add_le
        (∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam, F n)
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceWindowComplement
            φ a b resonance lam, F n))

/-- The union of a finite family of integer-centered resonance windows. -/
def Complex.realPhase_integerIncrementResonanceFamilyUnion
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) : Finset ℕ :=
  K.biUnion
    (fun k : ℤ =>
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam)

/-- The complement of a finite family of integer-centered resonance windows
inside the ambient half-open block. -/
def Complex.realPhase_integerIncrementResonanceFamilyComplement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) : Finset ℕ :=
  (Finset.Ico a b).filter
    (fun n : ℕ =>
      n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K)

/-- Membership in the finite-family resonance complement. -/
theorem Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    {n : ℕ} :
    n ∈
        Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam K ↔
      n ∈ Finset.Ico a b ∧
        n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K := by
  exact Finset.mem_filter

/-- Consecutive ordered integer lattice centers are separated by at least one
full `2π` period. -/
theorem Real.two_pi_int_center_add_period_le_of_lt
    {k₁ k₂ : ℤ}
    (hk : k₁ < k₂) :
    2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi ≤
      2 * Real.pi * (k₂ : ℝ) := by
  have hk_succ : k₁ + 1 ≤ k₂ :=
    Int.add_one_le_iff.mpr hk
  have hk_succ_real : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) :=
    calc
      (k₁ : ℝ) + 1 = ((k₁ + 1 : ℤ) : ℝ) := by
        exact
          (Eq.trans
            (Int.cast_add k₁ 1)
            (congrArg (fun r : ℝ => (k₁ : ℝ) + r) Int.cast_one)).symm
      _ ≤ (k₂ : ℝ) := Int.cast_le.mpr hk_succ
  have hmul :
      2 * Real.pi * ((k₁ : ℝ) + 1) ≤
        2 * Real.pi * (k₂ : ℝ) :=
    mul_le_mul_of_nonneg_left hk_succ_real
      (le_of_lt Real.two_pi_pos)
  have hleft :
      2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi =
        2 * Real.pi * ((k₁ : ℝ) + 1) := by
    calc
      2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi =
        2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi * 1 := by
        exact congrArg
          (fun r : ℝ => 2 * Real.pi * (k₁ : ℝ) + r)
          (mul_one (2 * Real.pi)).symm
      _ = 2 * Real.pi * ((k₁ : ℝ) + 1) :=
        (mul_add (2 * Real.pi) (k₁ : ℝ) 1).symm
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ 2 * Real.pi * (k₂ : ℝ))
      hleft.symm
      hmul

/-- If `k₁ < k₂` and the common tube radius is at most `π`, then the right
edge of the `k₁` tube lies before the left edge of the `k₂` tube. -/
theorem Real.two_pi_int_center_add_radius_le_next_center_sub_radius
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂) :
    2 * Real.pi * (k₁ : ℝ) + lam ≤
      2 * Real.pi * (k₂ : ℝ) - lam := by
  let A : ℝ := 2 * Real.pi * (k₁ : ℝ)
  let B : ℝ := 2 * Real.pi * (k₂ : ℝ)
  have hA : A = 2 * Real.pi * (k₁ : ℝ) :=
    Eq.refl A
  have hB : B = 2 * Real.pi * (k₂ : ℝ) :=
    Eq.refl B
  have hperiod : A + 2 * Real.pi ≤ B :=
    Eq.subst
      (motive := fun left : ℝ => left + 2 * Real.pi ≤ B)
      hA.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi ≤ right)
        hB.symm
        (Real.two_pi_int_center_add_period_le_of_lt hk))
  have htwo_lam_le_two_pi : lam + lam ≤ 2 * Real.pi := by
    have htwo_mul : 2 * lam ≤ 2 * Real.pi :=
      mul_le_mul_of_nonneg_left hlam zero_le_two
    have hsum_eq : lam + lam = 2 * lam :=
      (two_mul lam).symm
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ 2 * Real.pi)
        hsum_eq.symm
        htwo_mul
  have hsum_le_B : A + lam + lam ≤ B := by
    have hassoc :
        A + lam + lam = A + (lam + lam) :=
      add_assoc A lam lam
    have hA_lams_le_A_period :
        A + (lam + lam) ≤ A + 2 * Real.pi :=
      add_le_add_left htwo_lam_le_two_pi A
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ B)
        hassoc.symm
        (le_trans hA_lams_le_A_period hperiod)
  have hA_lam_le_B_sub_lam : A + lam ≤ B - lam :=
    (le_sub_iff_add_le).mpr hsum_le_B
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left + lam ≤ 2 * Real.pi * (k₂ : ℝ) - lam)
      hA
      (Eq.subst
        (motive := fun right : ℝ => A + lam ≤ right - lam)
        hB
        hA_lam_le_B_sub_lam)

/-- A real number cannot lie in two distinct integer-centered `2π` tubes of
radius at most `π`. -/
theorem Real.not_abs_sub_two_pi_int_centers_lt_of_ne_of_le_pi
    {θ lam : ℝ}
    {k₁ k₂ : ℤ}
    (hlam : lam ≤ Real.pi)
    (hne : k₁ ≠ k₂)
    (h₁ : ‖θ - (2 * Real.pi * (k₁ : ℝ))‖ < lam) :
    ¬ ‖θ - (2 * Real.pi * (k₂ : ℝ))‖ < lam := by
  intro h₂
  let A : ℝ := 2 * Real.pi * (k₁ : ℝ)
  let B : ℝ := 2 * Real.pi * (k₂ : ℝ)
  have hA : A = 2 * Real.pi * (k₁ : ℝ) :=
    Eq.refl A
  have hB : B = 2 * Real.pi * (k₂ : ℝ) :=
    Eq.refl B
  have h₁_abs : |θ - A| < lam :=
    Eq.subst
      (motive := fun center : ℝ => |θ - center| < lam)
      hA.symm
      (Eq.subst
        (motive := fun r : ℝ => r < lam)
        (Real.norm_eq_abs (θ - (2 * Real.pi * (k₁ : ℝ))))
        h₁)
  have h₂_abs : |θ - B| < lam :=
    Eq.subst
      (motive := fun center : ℝ => |θ - center| < lam)
      hB.symm
      (Eq.subst
        (motive := fun r : ℝ => r < lam)
        (Real.norm_eq_abs (θ - (2 * Real.pi * (k₂ : ℝ))))
        h₂)
  have hθ_lt_A_add : θ < A + lam :=
    calc
      θ < lam + A := (sub_lt_iff_lt_add).mp (abs_lt.mp h₁_abs).2
      _ = A + lam := add_comm lam A
  have hB_sub_lt_θ : B - lam < θ := by
    have hleft : -lam < θ - B :=
      (abs_lt.mp h₂_abs).1
    have hshift : -lam + B < θ :=
      (lt_sub_iff_add_lt).mp hleft
    calc
      B - lam = -lam + B := by
        exact (sub_eq_add_neg B lam).trans (add_comm B (-lam))
      _ < θ := hshift
  have hB_lt_A_two_lam : B < A + (lam + lam) := by
    have hB_lt_θ_add : B < θ + lam :=
      (sub_lt_iff_lt_add).mp hB_sub_lt_θ
    have hθ_add_lt : θ + lam < A + lam + lam :=
      add_lt_add_right hθ_lt_A_add lam
    have htarget :
        A + lam + lam = A + (lam + lam) :=
      add_assoc A lam lam
    exact
      Eq.subst
        (motive := fun right : ℝ => B < right)
        htarget
        (lt_trans hB_lt_θ_add hθ_add_lt)
  have htwo_lam_le_two_pi : lam + lam ≤ 2 * Real.pi := by
    have htwo_mul : 2 * lam ≤ 2 * Real.pi :=
      mul_le_mul_of_nonneg_left hlam zero_le_two
    have hsum_eq : lam + lam = 2 * lam :=
      (two_mul lam).symm
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ 2 * Real.pi)
        hsum_eq.symm
        htwo_mul
  have hA_two_lam_le_A_two_pi :
      A + (lam + lam) ≤ A + 2 * Real.pi :=
    add_le_add_left htwo_lam_le_two_pi A
  match lt_or_gt_of_ne hne with
  | Or.inl hk₁₂ =>
      have hsep :
        A + 2 * Real.pi ≤ B :=
        Eq.subst
          (motive := fun left : ℝ => left + 2 * Real.pi ≤ B)
          hA.symm
          (Eq.subst
            (motive := fun right : ℝ =>
              2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi ≤ right)
            hB.symm
            (Real.two_pi_int_center_add_period_le_of_lt hk₁₂))
      have hB_lt_B : B < B :=
        lt_of_lt_of_le hB_lt_A_two_lam
          (le_trans hA_two_lam_le_A_two_pi hsep)
      exact (lt_irrefl B) hB_lt_B
  | Or.inr hk₂₁ =>
      have hsep :
        B + 2 * Real.pi ≤ A :=
        Eq.subst
          (motive := fun left : ℝ => left + 2 * Real.pi ≤ A)
          hB.symm
          (Eq.subst
            (motive := fun right : ℝ =>
              2 * Real.pi * (k₂ : ℝ) + 2 * Real.pi ≤ right)
            hA.symm
            (Real.two_pi_int_center_add_period_le_of_lt hk₂₁))
      have hA_lt_B_two_lam :
          A < B + (lam + lam) := by
          have hA_sub_lt_θ : A - lam < θ := by
            have hleft : -lam < θ - A :=
              (abs_lt.mp h₁_abs).1
            have hshift : -lam + A < θ :=
              (lt_sub_iff_add_lt).mp hleft
            calc
              A - lam = -lam + A := by
                exact (sub_eq_add_neg A lam).trans (add_comm A (-lam))
              _ < θ := hshift
          have hA_lt_θ_add : A < θ + lam :=
            (sub_lt_iff_lt_add).mp hA_sub_lt_θ
          have hθ_lt_B_add : θ < B + lam :=
            calc
              θ < lam + B := (sub_lt_iff_lt_add).mp (abs_lt.mp h₂_abs).2
              _ = B + lam := add_comm lam B
          have hA_lt_B_two_lam : A < B + (lam + lam) := by
            have hθ_add_lt : θ + lam < B + lam + lam :=
              add_lt_add_right hθ_lt_B_add lam
            have htarget :
                B + lam + lam = B + (lam + lam) :=
              add_assoc B lam lam
            exact
              Eq.subst
                (motive := fun right : ℝ => A < right)
                htarget
                (lt_trans hA_lt_θ_add hθ_add_lt)
          exact hA_lt_B_two_lam
      have hA_lt_B_two_pi : A < B + 2 * Real.pi :=
        lt_of_lt_of_le hA_lt_B_two_lam
          (add_le_add_left htwo_lam_le_two_pi B)
      have hA_lt_A : A < A :=
        lt_of_lt_of_le hA_lt_B_two_pi hsep
      exact (lt_irrefl A) hA_lt_A

/-- Distinct integer-centered resonance windows are disjoint when their common
radius is at most `π`. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_disjoint_of_ne_of_le_pi
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hlam : lam ≤ Real.pi)
    (hne : k₁ ≠ k₂) :
    Disjoint
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam)
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₂ : ℝ)) lam) := by
  exact
    Finset.disjoint_left.mpr
      (fun n hn₁ hn₂ =>
        have hres₁ :
            ‖Complex.realPhase_integerIncrement φ n -
                (2 * Real.pi * (k₁ : ℝ))‖ < lam :=
          (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
            (φ := φ)
            (a := a)
            (b := b)
            (n := n)
            (resonance := 2 * Real.pi * (k₁ : ℝ))
            (lam := lam)).mp hn₁ |>.2
        have hres₂ :
            ‖Complex.realPhase_integerIncrement φ n -
                (2 * Real.pi * (k₂ : ℝ))‖ < lam :=
          (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
            (φ := φ)
            (a := a)
            (b := b)
            (n := n)
            (resonance := 2 * Real.pi * (k₂ : ℝ))
            (lam := lam)).mp hn₂ |>.2
        Real.not_abs_sub_two_pi_int_centers_lt_of_ne_of_le_pi
          hlam hne hres₁ hres₂)

/-- Any finite family of distinct integer-centered resonance windows is
pairwise disjoint once the common radius is at most `π`. -/
theorem Complex.realPhase_integerIncrementResonanceFamily_pairwiseDisjoint_of_le_pi
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (hlam : lam ≤ Real.pi) :
    ∀ k₁ ∈ K,
      ∀ k₂ ∈ K,
        k₁ ≠ k₂ →
          Disjoint
            (Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k₁ : ℝ)) lam)
            (Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k₂ : ℝ)) lam) := by
  intro k₁ _hk₁ k₂ _hk₂ hne
  exact
    Complex.realPhase_integerIncrementResonanceWindow_disjoint_of_ne_of_le_pi
      φ hlam hne

/-- In the thin-tube regime, the resonance-family union cardinal is exactly
the sum of the cardinalities of the integer-centered windows. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_card_eq_sum_window_cards_of_le_pi
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (hlam : lam ≤ Real.pi) :
    (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K).card =
      ∑ k ∈ K,
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card := by
  exact
    Finset.card_biUnion
      (Complex.realPhase_integerIncrementResonanceFamily_pairwiseDisjoint_of_le_pi
        φ hlam)

/-- Real-valued cardinal formula for a thin family of integer-centered
resonance windows. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_card_real_eq_sum_window_cards_of_le_pi
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (hlam : lam ≤ Real.pi) :
    ((Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K).card :
        ℝ) =
      ((∑ k ∈ K,
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℕ) : ℝ) := by
  exact
    congrArg
      (fun n : ℕ => (n : ℝ))
      (Complex.realPhase_integerIncrementResonanceFamilyUnion_card_eq_sum_window_cards_of_le_pi
        φ a b lam K hlam)

/-- For monotone increasing increments, samples in lower integer-centered
thin resonance windows occur strictly before samples in higher windows. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_sample_lt_of_monotone_of_center_lt
    (φ : ℝ → ℝ)
    {a b n₁ n₂ : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hmono :
      MonotoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico a b : Set ℕ))
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂)
    (hn₁ :
      n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam)
    (hn₂ :
      n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₂ : ℝ)) lam) :
    n₁ < n₂ := by
  let θ₁ : ℝ := Complex.realPhase_integerIncrement φ n₁
  let θ₂ : ℝ := Complex.realPhase_integerIncrement φ n₂
  let A : ℝ := 2 * Real.pi * (k₁ : ℝ)
  let B : ℝ := 2 * Real.pi * (k₂ : ℝ)
  have hA : A = 2 * Real.pi * (k₁ : ℝ) :=
    Eq.refl A
  have hB : B = 2 * Real.pi * (k₂ : ℝ) :=
    Eq.refl B
  have hθ₁ : θ₁ = Complex.realPhase_integerIncrement φ n₁ :=
    Eq.refl θ₁
  have hθ₂ : θ₂ = Complex.realPhase_integerIncrement φ n₂ :=
    Eq.refl θ₂
  have hn₁_data :
      n₁ ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n₁ -
          (2 * Real.pi * (k₁ : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n₁)
      (resonance := 2 * Real.pi * (k₁ : ℝ))
      (lam := lam)).mp hn₁
  have hn₂_data :
      n₂ ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n₂ -
          (2 * Real.pi * (k₂ : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n₂)
      (resonance := 2 * Real.pi * (k₂ : ℝ))
      (lam := lam)).mp hn₂
  have hres₁_abs : |θ₁ - A| < lam :=
    Eq.subst
      (motive := fun left : ℝ => |left - A| < lam)
      hθ₁.symm
      (Eq.subst
        (motive := fun center : ℝ =>
          |Complex.realPhase_integerIncrement φ n₁ - center| < lam)
        hA.symm
        (Eq.subst
          (motive := fun r : ℝ => r < lam)
          (Real.norm_eq_abs
            (Complex.realPhase_integerIncrement φ n₁ -
              (2 * Real.pi * (k₁ : ℝ))))
          hn₁_data.2))
  have hres₂_abs : |θ₂ - B| < lam :=
    Eq.subst
      (motive := fun left : ℝ => |left - B| < lam)
      hθ₂.symm
      (Eq.subst
        (motive := fun center : ℝ =>
          |Complex.realPhase_integerIncrement φ n₂ - center| < lam)
        hB.symm
        (Eq.subst
          (motive := fun r : ℝ => r < lam)
          (Real.norm_eq_abs
            (Complex.realPhase_integerIncrement φ n₂ -
              (2 * Real.pi * (k₂ : ℝ))))
          hn₂_data.2))
  have hθ₁_lt_A_lam : θ₁ < A + lam :=
    calc
      θ₁ < lam + A := (sub_lt_iff_lt_add).mp (abs_lt.mp hres₁_abs).2
      _ = A + lam := add_comm lam A
  have hB_lam_lt_θ₂ : B - lam < θ₂ := by
    have hleft : -lam < θ₂ - B :=
      (abs_lt.mp hres₂_abs).1
    have hshift : -lam + B < θ₂ :=
      (lt_sub_iff_add_lt).mp hleft
    calc
      B - lam = -lam + B := by
        exact (sub_eq_add_neg B lam).trans (add_comm B (-lam))
      _ < θ₂ := hshift
  have hedge :
      A + lam ≤ B - lam :=
    Eq.subst
      (motive := fun left : ℝ => left + lam ≤ B - lam)
      hA.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          2 * Real.pi * (k₁ : ℝ) + lam ≤ right - lam)
        hB.symm
        (Real.two_pi_int_center_add_radius_le_next_center_sub_radius
          hlam hk))
  have hnot_n₂_le_n₁ : ¬ n₂ ≤ n₁ := by
    intro hn₂_le_n₁
    have hθ₂_le_θ₁_raw :
        Complex.realPhase_integerIncrement φ n₂ ≤
          Complex.realPhase_integerIncrement φ n₁ :=
      hmono hn₂_data.1 hn₁_data.1 hn₂_le_n₁
    have hθ₂_le_θ₁ : θ₂ ≤ θ₁ :=
      Eq.subst
        (motive := fun left : ℝ => left ≤ θ₁)
        hθ₂.symm
        (Eq.subst
          (motive := fun right : ℝ =>
            Complex.realPhase_integerIncrement φ n₂ ≤ right)
          hθ₁.symm
          hθ₂_le_θ₁_raw)
    have hB_lam_lt_A_lam : B - lam < A + lam :=
      lt_trans hB_lam_lt_θ₂
        (lt_of_le_of_lt hθ₂_le_θ₁ hθ₁_lt_A_lam)
    have hB_lam_lt_B_lam : B - lam < B - lam :=
      lt_of_lt_of_le hB_lam_lt_A_lam hedge
    exact (lt_irrefl (B - lam)) hB_lam_lt_B_lam
  exact Nat.lt_of_not_ge hnot_n₂_le_n₁

/-- For monotone decreasing increments, samples in lower integer-centered
thin resonance windows occur strictly after samples in higher windows. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_sample_gt_of_antitone_of_center_lt
    (φ : ℝ → ℝ)
    {a b n₁ n₂ : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hanti :
      AntitoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico a b : Set ℕ))
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂)
    (hn₁ :
      n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam)
    (hn₂ :
      n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₂ : ℝ)) lam) :
    n₂ < n₁ := by
  let θ₁ : ℝ := Complex.realPhase_integerIncrement φ n₁
  let θ₂ : ℝ := Complex.realPhase_integerIncrement φ n₂
  let A : ℝ := 2 * Real.pi * (k₁ : ℝ)
  let B : ℝ := 2 * Real.pi * (k₂ : ℝ)
  have hA : A = 2 * Real.pi * (k₁ : ℝ) :=
    Eq.refl A
  have hB : B = 2 * Real.pi * (k₂ : ℝ) :=
    Eq.refl B
  have hθ₁ : θ₁ = Complex.realPhase_integerIncrement φ n₁ :=
    Eq.refl θ₁
  have hθ₂ : θ₂ = Complex.realPhase_integerIncrement φ n₂ :=
    Eq.refl θ₂
  have hn₁_data :
      n₁ ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n₁ -
          (2 * Real.pi * (k₁ : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n₁)
      (resonance := 2 * Real.pi * (k₁ : ℝ))
      (lam := lam)).mp hn₁
  have hn₂_data :
      n₂ ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n₂ -
          (2 * Real.pi * (k₂ : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n₂)
      (resonance := 2 * Real.pi * (k₂ : ℝ))
      (lam := lam)).mp hn₂
  have hres₁_abs : |θ₁ - A| < lam :=
    Eq.subst
      (motive := fun left : ℝ => |left - A| < lam)
      hθ₁.symm
      (Eq.subst
        (motive := fun center : ℝ =>
          |Complex.realPhase_integerIncrement φ n₁ - center| < lam)
        hA.symm
        (Eq.subst
          (motive := fun r : ℝ => r < lam)
          (Real.norm_eq_abs
            (Complex.realPhase_integerIncrement φ n₁ -
              (2 * Real.pi * (k₁ : ℝ))))
          hn₁_data.2))
  have hres₂_abs : |θ₂ - B| < lam :=
    Eq.subst
      (motive := fun left : ℝ => |left - B| < lam)
      hθ₂.symm
      (Eq.subst
        (motive := fun center : ℝ =>
          |Complex.realPhase_integerIncrement φ n₂ - center| < lam)
        hB.symm
        (Eq.subst
          (motive := fun r : ℝ => r < lam)
          (Real.norm_eq_abs
            (Complex.realPhase_integerIncrement φ n₂ -
              (2 * Real.pi * (k₂ : ℝ))))
          hn₂_data.2))
  have hθ₁_lt_A_lam : θ₁ < A + lam :=
    calc
      θ₁ < lam + A := (sub_lt_iff_lt_add).mp (abs_lt.mp hres₁_abs).2
      _ = A + lam := add_comm lam A
  have hB_lam_lt_θ₂ : B - lam < θ₂ := by
    have hleft : -lam < θ₂ - B :=
      (abs_lt.mp hres₂_abs).1
    have hshift : -lam + B < θ₂ :=
      (lt_sub_iff_add_lt).mp hleft
    calc
      B - lam = -lam + B := by
        exact (sub_eq_add_neg B lam).trans (add_comm B (-lam))
      _ < θ₂ := hshift
  have hedge :
      A + lam ≤ B - lam :=
    Eq.subst
      (motive := fun left : ℝ => left + lam ≤ B - lam)
      hA.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          2 * Real.pi * (k₁ : ℝ) + lam ≤ right - lam)
        hB.symm
        (Real.two_pi_int_center_add_radius_le_next_center_sub_radius
          hlam hk))
  have hnot_n₁_le_n₂ : ¬ n₁ ≤ n₂ := by
    intro hn₁_le_n₂
    have hθ₂_le_θ₁_raw :
        Complex.realPhase_integerIncrement φ n₂ ≤
          Complex.realPhase_integerIncrement φ n₁ :=
      hanti hn₁_data.1 hn₂_data.1 hn₁_le_n₂
    have hθ₂_le_θ₁ : θ₂ ≤ θ₁ :=
      Eq.subst
        (motive := fun left : ℝ => left ≤ θ₁)
        hθ₂.symm
        (Eq.subst
          (motive := fun right : ℝ =>
            Complex.realPhase_integerIncrement φ n₂ ≤ right)
          hθ₁.symm
          hθ₂_le_θ₁_raw)
    have hB_lam_lt_A_lam : B - lam < A + lam :=
      lt_trans hB_lam_lt_θ₂
        (lt_of_le_of_lt hθ₂_le_θ₁ hθ₁_lt_A_lam)
    have hB_lam_lt_B_lam : B - lam < B - lam :=
      lt_of_lt_of_le hB_lam_lt_A_lam hedge
    exact (lt_irrefl (B - lam)) hB_lam_lt_B_lam
  exact Nat.lt_of_not_ge hnot_n₁_le_n₂

/-- Under a chosen monotone-increment branch, samples in distinct thin
integer-centered windows are strictly ordered by their centers.  The direction
records whether the branch is increasing or decreasing. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_samples_ordered_of_center_lt
    (φ : ℝ → ℝ)
    {a b n₁ n₂ : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂)
    (hn₁ :
      n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam)
    (hn₂ :
      n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₂ : ℝ)) lam) :
    n₁ < n₂ ∨ n₂ < n₁ := by
  match hinc_mono with
  | Or.inl hmono =>
      exact Or.inl
        (Complex.realPhase_integerIncrementResonanceWindow_sample_lt_of_monotone_of_center_lt
          φ hmono hlam hk hn₁ hn₂)
  | Or.inr hanti =>
      exact Or.inr
        (Complex.realPhase_integerIncrementResonanceWindow_sample_gt_of_antitone_of_center_lt
          φ hanti hlam hk hn₁ hn₂)

/-- In the increasing branch, every sample in a lower-center thin window lies
before every sample in a higher-center thin window. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_forall_lt_of_monotone_of_center_lt
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hmono :
      MonotoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico a b : Set ℕ))
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂) :
    ∀ n₁ : ℕ,
      n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam →
        ∀ n₂ : ℕ,
          n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k₂ : ℝ)) lam →
            n₁ < n₂ := by
  intro n₁ hn₁ n₂ hn₂
  exact
    Complex.realPhase_integerIncrementResonanceWindow_sample_lt_of_monotone_of_center_lt
      φ hmono hlam hk hn₁ hn₂

/-- In the decreasing branch, every sample in a higher-center thin window lies
before every sample in a lower-center thin window. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_forall_gt_of_antitone_of_center_lt
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hanti :
      AntitoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico a b : Set ℕ))
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂) :
    ∀ n₁ : ℕ,
      n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam →
        ∀ n₂ : ℕ,
          n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k₂ : ℝ)) lam →
            n₂ < n₁ := by
  intro n₁ hn₁ n₂ hn₂
  exact
    Complex.realPhase_integerIncrementResonanceWindow_sample_gt_of_antitone_of_center_lt
      φ hanti hlam hk hn₁ hn₂

/-- If every sample of `Ico c₁ d₁` lies before every sample of `Ico c₂ d₂`,
then a nonempty left interval ends no later than the start of the nonempty
right interval. -/
theorem Nat.Ico_right_le_left_of_forall_lt
    {c₁ d₁ c₂ d₂ : ℕ}
    (hleft : c₁ < d₁)
    (hright : c₂ < d₂)
    (horder :
      ∀ n₁ : ℕ,
        n₁ ∈ Finset.Ico c₁ d₁ →
          ∀ n₂ : ℕ,
            n₂ ∈ Finset.Ico c₂ d₂ →
              n₁ < n₂) :
    d₁ ≤ c₂ := by
  have hd₁_pred_mem :
      d₁ - 1 ∈ Finset.Ico c₁ d₁ := by
    have hc₁_le_pred : c₁ ≤ d₁ - 1 :=
      Nat.le_sub_one_of_lt hleft
    have hpred_lt : d₁ - 1 < d₁ :=
      Nat.sub_one_lt_of_lt hleft
    exact Finset.mem_Ico.mpr (And.intro hc₁_le_pred hpred_lt)
  have hc₂_mem :
      c₂ ∈ Finset.Ico c₂ d₂ :=
    Finset.mem_Ico.mpr (And.intro le_rfl hright)
  have hpred_lt_c₂ : d₁ - 1 < c₂ :=
    horder (d₁ - 1) hd₁_pred_mem c₂ hc₂_mem
  have hd₁_pos : 0 < d₁ :=
    lt_of_le_of_lt (Nat.zero_le c₁) hleft
  have hsucc_eq : (d₁ - 1).succ = d₁ :=
    Nat.succ_pred_eq_of_pos hd₁_pos
  exact
    Eq.subst
      (motive := fun r : ℕ => r ≤ c₂)
      hsucc_eq
      (Nat.succ_le_of_lt hpred_lt_c₂)

/-- Endpoint order for two nonempty increasing-branch integer-centered
resonance windows after they have been identified as half-open intervals. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_Ico_order_of_monotone_of_center_lt
    (φ : ℝ → ℝ)
    {a b c₁ d₁ c₂ d₂ : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hmono :
      MonotoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico a b : Set ℕ))
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂)
    (hw₁ :
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam =
          Finset.Ico c₁ d₁)
    (hw₂ :
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₂ : ℝ)) lam =
          Finset.Ico c₂ d₂)
    (hleft : c₁ < d₁)
    (hright : c₂ < d₂) :
    d₁ ≤ c₂ := by
  have horder :
      ∀ n₁ : ℕ,
        n₁ ∈ Finset.Ico c₁ d₁ →
          ∀ n₂ : ℕ,
            n₂ ∈ Finset.Ico c₂ d₂ →
              n₁ < n₂ := by
    intro n₁ hn₁ n₂ hn₂
    have hn₁_window :
        n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k₁ : ℝ)) lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n₁ ∈ S)
        hw₁.symm
        hn₁
    have hn₂_window :
        n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k₂ : ℝ)) lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n₂ ∈ S)
        hw₂.symm
        hn₂
    exact
      Complex.realPhase_integerIncrementResonanceWindow_sample_lt_of_monotone_of_center_lt
        φ hmono hlam hk hn₁_window hn₂_window
  exact Nat.Ico_right_le_left_of_forall_lt hleft hright horder

/-- Endpoint order for two nonempty decreasing-branch integer-centered
resonance windows after they have been identified as half-open intervals. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_Ico_order_of_antitone_of_center_lt
    (φ : ℝ → ℝ)
    {a b c₁ d₁ c₂ d₂ : ℕ}
    {lam : ℝ}
    {k₁ k₂ : ℤ}
    (hanti :
      AntitoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico a b : Set ℕ))
    (hlam : lam ≤ Real.pi)
    (hk : k₁ < k₂)
    (hw₁ :
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₁ : ℝ)) lam =
          Finset.Ico c₁ d₁)
    (hw₂ :
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k₂ : ℝ)) lam =
          Finset.Ico c₂ d₂)
    (hleft : c₁ < d₁)
    (hright : c₂ < d₂) :
    d₂ ≤ c₁ := by
  have horder :
      ∀ n₂ : ℕ,
        n₂ ∈ Finset.Ico c₂ d₂ →
          ∀ n₁ : ℕ,
            n₁ ∈ Finset.Ico c₁ d₁ →
              n₂ < n₁ := by
    intro n₂ hn₂ n₁ hn₁
    have hn₁_window :
        n₁ ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k₁ : ℝ)) lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n₁ ∈ S)
        hw₁.symm
        hn₁
    have hn₂_window :
        n₂ ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k₂ : ℝ)) lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n₂ ∈ S)
        hw₂.symm
        hn₂
    exact
      Complex.realPhase_integerIncrementResonanceWindow_sample_gt_of_antitone_of_center_lt
        φ hanti hlam hk hn₁_window hn₂_window
  exact Nat.Ico_right_le_left_of_forall_lt hright hleft horder

/-- The two open gaps left in a half-open natural block after removing one
half-open subinterval. -/
def Nat.IcoTwoGapComplement
    (a b c d : ℕ) : Finset (ℕ × ℕ) :=
  insert (a, c) (Finset.singleton (d, b))

/-- The two-gap complement family has cardinality at most two. -/
theorem Nat.IcoTwoGapComplement_card_le_two
    (a b c d : ℕ) :
    (Nat.IcoTwoGapComplement a b c d).card ≤ 2 := by
  have hcard_insert :
      (insert (a, c) (Finset.singleton (d, b))).card ≤
        (Finset.singleton (d, b)).card + 1 :=
    Finset.card_insert_le (a, c) (Finset.singleton (d, b))
  have hsingle :
      (Finset.singleton (d, b)).card + 1 = 2 := by
    have hsingle_card :
        (Finset.singleton (d, b)).card = 1 :=
      Finset.card_singleton (d, b)
    exact congrArg (fun n : ℕ => n + 1) hsingle_card
  exact
    Eq.subst
      (motive := fun right : ℕ =>
        (Nat.IcoTwoGapComplement a b c d).card ≤ right)
      hsingle
      hcard_insert

/-- A point of the left gap lies in the ambient block and outside the removed
subinterval. -/
theorem Nat.mem_left_Ico_gap_complement
    {a b c d n : ℕ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hn : n ∈ Finset.Ico a c) :
    n ∈ Finset.Ico a b ∧ n ∉ Finset.Ico c d := by
  have hn_bounds : a ≤ n ∧ n < c :=
    Finset.mem_Ico.mp hn
  have hn_block : n ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr
      (And.intro hn_bounds.1
        (lt_of_lt_of_le hn_bounds.2
          (Nat.le_trans hcd hdb)))
  have hn_not_removed : n ∉ Finset.Ico c d := by
    intro hn_removed
    have hremoved_bounds : c ≤ n ∧ n < d :=
      Finset.mem_Ico.mp hn_removed
    exact (not_lt_of_ge hremoved_bounds.1) hn_bounds.2
  exact And.intro hn_block hn_not_removed

/-- A point of the right gap lies in the ambient block and outside the removed
subinterval. -/
theorem Nat.mem_right_Ico_gap_complement
    {a b c d n : ℕ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hn : n ∈ Finset.Ico d b) :
    n ∈ Finset.Ico a b ∧ n ∉ Finset.Ico c d := by
  have hn_bounds : d ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn
  have ha_le_n : a ≤ n :=
    Nat.le_trans hac (Nat.le_trans hcd hn_bounds.1)
  have hn_block_fixed : n ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr (And.intro ha_le_n hn_bounds.2)
  have hn_not_removed : n ∉ Finset.Ico c d := by
    intro hn_removed
    have hremoved_bounds : c ≤ n ∧ n < d :=
      Finset.mem_Ico.mp hn_removed
    exact (not_lt_of_ge hn_bounds.1) hremoved_bounds.2
  exact And.intro hn_block_fixed hn_not_removed

/-- A point of an ambient block outside a removed half-open subinterval lies
in the left or right gap. -/
theorem Nat.mem_left_or_right_Ico_gap_of_mem_complement
    {a b c d n : ℕ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hn_block : n ∈ Finset.Ico a b)
    (hn_removed : n ∉ Finset.Ico c d) :
    n ∈ Finset.Ico a c ∨ n ∈ Finset.Ico d b := by
  have hn_bounds : a ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn_block
  match lt_or_ge n c with
  | Or.inl hn_lt_c =>
      exact Or.inl
        (Finset.mem_Ico.mpr (And.intro hn_bounds.1 hn_lt_c))
  | Or.inr hc_le_n =>
      have hd_le_n : d ≤ n := by
        match lt_or_ge n d with
        | Or.inl hn_lt_d =>
            have hn_in_removed : n ∈ Finset.Ico c d :=
              Finset.mem_Ico.mpr (And.intro hc_le_n hn_lt_d)
            exact False.elim (hn_removed hn_in_removed)
        | Or.inr hd_le_n =>
            exact hd_le_n
      exact Or.inr
        (Finset.mem_Ico.mpr (And.intro hd_le_n hn_bounds.2))

/-- The two canonical gaps cover exactly the complement of one half-open
subinterval inside an ambient half-open block. -/
theorem Nat.IcoTwoGapComplement_biUnion_eq_filter_not_Ico
    {a b c d : ℕ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b) :
    (Nat.IcoTwoGapComplement a b c d).biUnion
        (fun p : ℕ × ℕ => Finset.Ico p.1 p.2) =
      (Finset.Ico a b).filter
        (fun n : ℕ => n ∉ Finset.Ico c d) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ p : ℕ × ℕ,
                p ∈ Nat.IcoTwoGapComplement a b c d ∧
                  n ∈ Finset.Ico p.1 p.2 :=
            Finset.mem_biUnion.mp hn
          match hmem with
          | ⟨p, hp, hn_gap⟩ =>
              have hp_cases :
                  p = (a, c) ∨ p ∈ Finset.singleton (d, b) :=
                Finset.mem_insert.mp hp
              match hp_cases with
              | Or.inl hp_left =>
                  have hn_left : n ∈ Finset.Ico a c :=
                    Eq.subst
                      (motive := fun q : ℕ × ℕ =>
                        n ∈ Finset.Ico q.1 q.2)
                      hp_left
                      hn_gap
                  have hn_data :
                      n ∈ Finset.Ico a b ∧ n ∉ Finset.Ico c d :=
                    Nat.mem_left_Ico_gap_complement hac hcd hdb hn_left
                  Finset.mem_filter.mpr hn_data
              | Or.inr hp_single =>
                  have hp_right : p = (d, b) :=
                    Finset.mem_singleton.mp hp_single
                  have hn_right : n ∈ Finset.Ico d b :=
                    Eq.subst
                      (motive := fun q : ℕ × ℕ =>
                        n ∈ Finset.Ico q.1 q.2)
                      hp_right
                      hn_gap
                  have hn_data :
                      n ∈ Finset.Ico a b ∧ n ∉ Finset.Ico c d :=
                    Nat.mem_right_Ico_gap_complement hac hcd hn_right
                  Finset.mem_filter.mpr hn_data)
        (fun hn =>
          have hn_data :
              n ∈ Finset.Ico a b ∧ n ∉ Finset.Ico c d :=
            Finset.mem_filter.mp hn
          have hn_gap :
              n ∈ Finset.Ico a c ∨ n ∈ Finset.Ico d b :=
            Nat.mem_left_or_right_Ico_gap_of_mem_complement
              hac hcd hn_data.1 hn_data.2
          match hn_gap with
          | Or.inl hn_left =>
              Finset.mem_biUnion.mpr
                (Exists.intro (a, c)
                  (And.intro
                    (Finset.mem_insert_self (a, c)
                      (Finset.singleton (d, b)))
                    hn_left))
          | Or.inr hn_right =>
              Finset.mem_biUnion.mpr
                (Exists.intro (d, b)
                  (And.intro
                    (Finset.mem_insert_of_mem
                      (Finset.mem_singleton_self (d, b)))
                    hn_right))))

/-- The left and right gaps around one removed half-open interval are
disjoint. -/
theorem Nat.Ico_left_right_gap_disjoint
    {a b c d : ℕ}
    (hcd : c ≤ d) :
    Disjoint (Finset.Ico a c) (Finset.Ico d b) := by
  exact Finset.disjoint_left.mpr
    (fun n hn_left hn_right =>
      have hn_left_bounds : a ≤ n ∧ n < c :=
        Finset.mem_Ico.mp hn_left
      have hn_right_bounds : d ≤ n ∧ n < b :=
        Finset.mem_Ico.mp hn_right
      have hc_le_n : c ≤ n :=
        Nat.le_trans hcd hn_right_bounds.1
      (not_lt_of_ge hc_le_n) hn_left_bounds.2)

/-- The canonical two-gap family around one removed interval is pairwise
disjoint. -/
theorem Nat.IcoTwoGapComplement_pairwiseDisjoint
    {a b c d : ℕ}
    (hcd : c ≤ d) :
    ∀ p₁ : ℕ × ℕ,
      p₁ ∈ Nat.IcoTwoGapComplement a b c d →
        ∀ p₂ : ℕ × ℕ,
          p₂ ∈ Nat.IcoTwoGapComplement a b c d →
            p₁ ≠ p₂ →
              Disjoint (Finset.Ico p₁.1 p₁.2)
                (Finset.Ico p₂.1 p₂.2) := by
  intro p₁ hp₁ p₂ hp₂ hne
  have hp₁_cases :
      p₁ = (a, c) ∨ p₁ ∈ Finset.singleton (d, b) :=
    Finset.mem_insert.mp hp₁
  have hp₂_cases :
      p₂ = (a, c) ∨ p₂ ∈ Finset.singleton (d, b) :=
    Finset.mem_insert.mp hp₂
  match hp₁_cases with
  | Or.inl hp₁_left =>
      match hp₂_cases with
      | Or.inl hp₂_left =>
          have hp_eq : p₁ = p₂ :=
            Eq.trans hp₁_left hp₂_left.symm
          exact False.elim (hne hp_eq)
      | Or.inr hp₂_single =>
          have hp₂_right : p₂ = (d, b) :=
            Finset.mem_singleton.mp hp₂_single
          exact
            Eq.subst
              (motive := fun q₁ : ℕ × ℕ =>
                Disjoint (Finset.Ico q₁.1 q₁.2)
                  (Finset.Ico p₂.1 p₂.2))
              hp₁_left.symm
              (Eq.subst
                (motive := fun q₂ : ℕ × ℕ =>
                  Disjoint (Finset.Ico a c)
                    (Finset.Ico q₂.1 q₂.2))
                hp₂_right.symm
                (Nat.Ico_left_right_gap_disjoint hcd))
  | Or.inr hp₁_single =>
      have hp₁_right : p₁ = (d, b) :=
        Finset.mem_singleton.mp hp₁_single
      match hp₂_cases with
      | Or.inl hp₂_left =>
          exact
            Eq.subst
              (motive := fun q₁ : ℕ × ℕ =>
                Disjoint (Finset.Ico q₁.1 q₁.2)
                  (Finset.Ico p₂.1 p₂.2))
              hp₁_right.symm
              (Eq.subst
                (motive := fun q₂ : ℕ × ℕ =>
                  Disjoint (Finset.Ico d b)
                    (Finset.Ico q₂.1 q₂.2))
                hp₂_left.symm
                (Nat.Ico_left_right_gap_disjoint hcd).symm)
      | Or.inr hp₂_single =>
          have hp₂_right : p₂ = (d, b) :=
            Finset.mem_singleton.mp hp₂_single
          have hp_eq : p₁ = p₂ :=
            Eq.trans hp₁_right hp₂_right.symm
          exact False.elim (hne hp_eq)

/-- The two gaps left in a half-open natural block after removing one point. -/
def Nat.IcoPointComplement
    (a b x : ℕ) : Finset (ℕ × ℕ) :=
  insert (a, x) (Finset.singleton (x + 1, b))

/-- The point-complement gap family has cardinality at most two. -/
theorem Nat.IcoPointComplement_card_le_two
    (a b x : ℕ) :
    (Nat.IcoPointComplement a b x).card ≤ 2 := by
  have hcard_insert :
      (insert (a, x) (Finset.singleton (x + 1, b))).card ≤
        (Finset.singleton (x + 1, b)).card + 1 :=
    Finset.card_insert_le (a, x) (Finset.singleton (x + 1, b))
  have hsingle :
      (Finset.singleton (x + 1, b)).card + 1 = 2 := by
    have hsingle_card :
        (Finset.singleton (x + 1, b)).card = 1 :=
      Finset.card_singleton (x + 1, b)
    exact congrArg (fun n : ℕ => n + 1) hsingle_card
  exact
    Eq.subst
      (motive := fun right : ℕ =>
        (Nat.IcoPointComplement a b x).card ≤ right)
      hsingle
      hcard_insert

/-- A point in the left gap around `x` lies in the ambient block and is not
the removed point. -/
theorem Nat.mem_left_Ico_point_complement
    {a b x n : ℕ}
    (hxb : x < b)
    (hn : n ∈ Finset.Ico a x) :
    n ∈ Finset.Ico a b ∧ n ≠ x := by
  have hn_bounds : a ≤ n ∧ n < x :=
    Finset.mem_Ico.mp hn
  have hn_block : n ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr
      (And.intro hn_bounds.1 (lt_trans hn_bounds.2 hxb))
  have hn_ne : n ≠ x := by
    intro hnx
    have hx_lt_x : x < x :=
      Eq.subst
        (motive := fun r : ℕ => r < x)
        hnx
        hn_bounds.2
    exact (Nat.lt_irrefl x) hx_lt_x
  exact And.intro hn_block hn_ne

/-- A point in the right gap around `x` lies in the ambient block and is not
the removed point. -/
theorem Nat.mem_right_Ico_point_complement
    {a b x n : ℕ}
    (hax : a ≤ x)
    (hn : n ∈ Finset.Ico (x + 1) b) :
    n ∈ Finset.Ico a b ∧ n ≠ x := by
  have hn_bounds : x + 1 ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn
  have hx_le_n : x ≤ n :=
    Nat.le_trans (Nat.le_succ x) hn_bounds.1
  have ha_le_n : a ≤ n :=
    Nat.le_trans hax hx_le_n
  have hn_block : n ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr (And.intro ha_le_n hn_bounds.2)
  have hn_ne : n ≠ x := by
    intro hnx
    have hx_succ_le_x : x + 1 ≤ x :=
      Eq.subst
        (motive := fun r : ℕ => x + 1 ≤ r)
        hnx
        hn_bounds.1
    have hx_lt_x : x < x :=
      Nat.lt_of_succ_le hx_succ_le_x
    exact (Nat.lt_irrefl x) hx_lt_x
  exact And.intro hn_block hn_ne

/-- A point of an ambient block other than `x` lies on the left or right side
of `x`. -/
theorem Nat.mem_left_or_right_Ico_point_gap_of_ne
    {a b x n : ℕ}
    (hn_block : n ∈ Finset.Ico a b)
    (hne : n ≠ x) :
    n ∈ Finset.Ico a x ∨ n ∈ Finset.Ico (x + 1) b := by
  have hn_bounds : a ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn_block
  match lt_or_ge n x with
  | Or.inl hn_lt_x =>
      exact Or.inl
        (Finset.mem_Ico.mpr (And.intro hn_bounds.1 hn_lt_x))
  | Or.inr hx_le_n =>
      have hx_lt_n : x < n :=
        lt_of_le_of_ne hx_le_n (Ne.symm hne)
      have hx_succ_le_n : x + 1 ≤ n :=
        Nat.succ_le_of_lt hx_lt_n
      exact Or.inr
        (Finset.mem_Ico.mpr (And.intro hx_succ_le_n hn_bounds.2))

/-- The two point gaps cover exactly the ambient interval with one point
removed. -/
theorem Nat.IcoPointComplement_biUnion_eq_filter_ne
    {a b x : ℕ}
    (hax : a ≤ x)
    (hxb : x < b) :
    (Nat.IcoPointComplement a b x).biUnion
        (fun p : ℕ × ℕ => Finset.Ico p.1 p.2) =
      (Finset.Ico a b).filter
        (fun n : ℕ => n ≠ x) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ p : ℕ × ℕ,
                p ∈ Nat.IcoPointComplement a b x ∧
                  n ∈ Finset.Ico p.1 p.2 :=
            Finset.mem_biUnion.mp hn
          match hmem with
          | ⟨p, hp, hn_gap⟩ =>
              have hp_cases :
                  p = (a, x) ∨ p ∈ Finset.singleton (x + 1, b) :=
                Finset.mem_insert.mp hp
              match hp_cases with
              | Or.inl hp_left =>
                  have hn_left : n ∈ Finset.Ico a x :=
                    Eq.subst
                      (motive := fun q : ℕ × ℕ =>
                        n ∈ Finset.Ico q.1 q.2)
                      hp_left
                      hn_gap
                  have hn_data : n ∈ Finset.Ico a b ∧ n ≠ x :=
                    Nat.mem_left_Ico_point_complement hxb hn_left
                  Finset.mem_filter.mpr hn_data
              | Or.inr hp_single =>
                  have hp_right : p = (x + 1, b) :=
                    Finset.mem_singleton.mp hp_single
                  have hn_right : n ∈ Finset.Ico (x + 1) b :=
                    Eq.subst
                      (motive := fun q : ℕ × ℕ =>
                        n ∈ Finset.Ico q.1 q.2)
                      hp_right
                      hn_gap
                  have hn_data : n ∈ Finset.Ico a b ∧ n ≠ x :=
                    Nat.mem_right_Ico_point_complement hax hn_right
                  Finset.mem_filter.mpr hn_data)
        (fun hn =>
          have hn_data : n ∈ Finset.Ico a b ∧ n ≠ x :=
            Finset.mem_filter.mp hn
          have hn_gap :
              n ∈ Finset.Ico a x ∨ n ∈ Finset.Ico (x + 1) b :=
            Nat.mem_left_or_right_Ico_point_gap_of_ne
              hn_data.1 hn_data.2
          match hn_gap with
          | Or.inl hn_left =>
              Finset.mem_biUnion.mpr
                (Exists.intro (a, x)
                  (And.intro
                    (Finset.mem_insert_self (a, x)
                      (Finset.singleton (x + 1, b)))
                    hn_left))
          | Or.inr hn_right =>
              Finset.mem_biUnion.mpr
                (Exists.intro (x + 1, b)
                  (And.intro
                    (Finset.mem_insert_of_mem
                      (Finset.mem_singleton_self (x + 1, b)))
                    hn_right))))

/-- The left and right point gaps are disjoint. -/
theorem Nat.Ico_left_right_point_gap_disjoint
    {a b x : ℕ} :
    Disjoint (Finset.Ico a x) (Finset.Ico (x + 1) b) := by
  exact Finset.disjoint_left.mpr
    (fun n hn_left hn_right =>
      have hn_left_bounds : a ≤ n ∧ n < x :=
        Finset.mem_Ico.mp hn_left
      have hn_right_bounds : x + 1 ≤ n ∧ n < b :=
        Finset.mem_Ico.mp hn_right
      have hx_le_n : x ≤ n :=
        Nat.le_trans (Nat.le_succ x) hn_right_bounds.1
      (not_lt_of_ge hx_le_n) hn_left_bounds.2)

/-- The canonical point-complement gap family is pairwise disjoint. -/
theorem Nat.IcoPointComplement_pairwiseDisjoint
    {a b x : ℕ} :
    ∀ p₁ : ℕ × ℕ,
      p₁ ∈ Nat.IcoPointComplement a b x →
        ∀ p₂ : ℕ × ℕ,
          p₂ ∈ Nat.IcoPointComplement a b x →
            p₁ ≠ p₂ →
              Disjoint (Finset.Ico p₁.1 p₁.2)
                (Finset.Ico p₂.1 p₂.2) := by
  intro p₁ hp₁ p₂ hp₂ hne
  have hp₁_cases :
      p₁ = (a, x) ∨ p₁ ∈ Finset.singleton (x + 1, b) :=
    Finset.mem_insert.mp hp₁
  have hp₂_cases :
      p₂ = (a, x) ∨ p₂ ∈ Finset.singleton (x + 1, b) :=
    Finset.mem_insert.mp hp₂
  match hp₁_cases with
  | Or.inl hp₁_left =>
      match hp₂_cases with
      | Or.inl hp₂_left =>
          have hp_eq : p₁ = p₂ :=
            Eq.trans hp₁_left hp₂_left.symm
          exact False.elim (hne hp_eq)
      | Or.inr hp₂_single =>
          have hp₂_right : p₂ = (x + 1, b) :=
            Finset.mem_singleton.mp hp₂_single
          exact
            Eq.subst
              (motive := fun q₁ : ℕ × ℕ =>
                Disjoint (Finset.Ico q₁.1 q₁.2)
                  (Finset.Ico p₂.1 p₂.2))
              hp₁_left.symm
              (Eq.subst
                (motive := fun q₂ : ℕ × ℕ =>
                  Disjoint (Finset.Ico a x)
                    (Finset.Ico q₂.1 q₂.2))
                hp₂_right.symm
                Nat.Ico_left_right_point_gap_disjoint)
  | Or.inr hp₁_single =>
      have hp₁_right : p₁ = (x + 1, b) :=
        Finset.mem_singleton.mp hp₁_single
      match hp₂_cases with
      | Or.inl hp₂_left =>
          exact
            Eq.subst
              (motive := fun q₁ : ℕ × ℕ =>
                Disjoint (Finset.Ico q₁.1 q₁.2)
                  (Finset.Ico p₂.1 p₂.2))
              hp₁_right.symm
              (Eq.subst
                (motive := fun q₂ : ℕ × ℕ =>
                  Disjoint (Finset.Ico (x + 1) b)
                    (Finset.Ico q₂.1 q₂.2))
                hp₂_left.symm
                Nat.Ico_left_right_point_gap_disjoint.symm)
      | Or.inr hp₂_single =>
          have hp₂_right : p₂ = (x + 1, b) :=
            Finset.mem_singleton.mp hp₂_single
          have hp_eq : p₁ = p₂ :=
            Eq.trans hp₁_right hp₂_right.symm
          exact False.elim (hne hp_eq)

/-- A padded finite interval of integer centers whose `2π` lattice frequencies
can meet the `lam`-tube around one sample increment. -/
def Complex.realPhase_integerIncrementSampleActiveCenters
    (φ : ℝ → ℝ)
    (lam : ℝ)
    (n : ℕ) : Finset ℤ :=
  Finset.Icc
    (⌊((Complex.realPhase_integerIncrement φ n - lam) /
      (2 * Real.pi))⌋ - 1)
    (⌊((Complex.realPhase_integerIncrement φ n + lam) /
      (2 * Real.pi))⌋ + 1)

/-- The finite active integer-center family generated by all sample increments
in a half-open block. -/
def Complex.realPhase_integerIncrementActiveCenters
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ) : Finset ℤ :=
  (Finset.Ico a b).biUnion
    (fun n : ℕ =>
      Complex.realPhase_integerIncrementSampleActiveCenters φ lam n)

/-- A padded finite interval of integer centers determined by an a priori
increment range `[lo, hi]`.  This is the counting-friendly active family for a
monotone increment block. -/
def Complex.realPhase_integerIncrementRangeActiveCenters
    (lo hi lam : ℝ) : Finset ℤ :=
  Finset.Icc
    (⌊((lo - lam) / (2 * Real.pi))⌋ - 1)
    (⌊((hi + lam) / (2 * Real.pi))⌋ + 1)

/-- Exact cardinal formula for the range-active center interval. -/
theorem Complex.realPhase_integerIncrementRangeActiveCenters_card_eq
    (lo hi lam : ℝ) :
    (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam).card =
      (⌊((hi + lam) / (2 * Real.pi))⌋ + 1 + 1 -
        (⌊((lo - lam) / (2 * Real.pi))⌋ - 1)).toNat := by
  exact
    Int.card_Icc
      (⌊((lo - lam) / (2 * Real.pi))⌋ - 1)
      (⌊((hi + lam) / (2 * Real.pi))⌋ + 1)

/-- Membership in the samplewise active-center interval follows from the
corresponding divided lower and upper lattice bounds. -/
theorem Complex.mem_realPhase_integerIncrementSampleActiveCenters_of_divided_bounds
    (φ : ℝ → ℝ)
    {lam : ℝ}
    {n : ℕ}
    {k : ℤ}
    (hlower :
      ((Complex.realPhase_integerIncrement φ n - lam) /
        (2 * Real.pi)) < (k : ℝ))
    (hupper :
      (k : ℝ) ≤
        ((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi))) :
    k ∈ Complex.realPhase_integerIncrementSampleActiveCenters φ lam n := by
  let lower : ℝ :=
    (Complex.realPhase_integerIncrement φ n - lam) / (2 * Real.pi)
  let upper : ℝ :=
    (Complex.realPhase_integerIncrement φ n + lam) / (2 * Real.pi)
  have hlower_to_floor :
      ⌊lower⌋ ≤ k := by
    have hk_le_k_add_one : (k : ℝ) ≤ (k : ℝ) + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hlower_lt_k_add_one : lower < (k : ℝ) + 1 :=
      lt_of_lt_of_le hlower hk_le_k_add_one
    exact Int.floor_le_iff.mpr hlower_lt_k_add_one
  have hlower_padded :
      ⌊lower⌋ - 1 ≤ k :=
    le_trans
      (sub_le_self ⌊lower⌋ zero_le_one)
      hlower_to_floor
  have hupper_to_floor :
      k ≤ ⌊upper⌋ :=
    Int.le_floor.mpr hupper
  have hupper_padded :
      k ≤ ⌊upper⌋ + 1 :=
    le_trans hupper_to_floor
      (le_add_of_nonneg_right zero_le_one)
  exact
    Finset.mem_Icc.mpr
      (And.intro hlower_padded hupper_padded)

/-- Membership in an a priori range active-center interval follows from the
corresponding divided lower and upper lattice bounds. -/
theorem Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_divided_bounds
    {lo hi lam : ℝ}
    {k : ℤ}
    (hlower :
      ((lo - lam) / (2 * Real.pi)) < (k : ℝ))
    (hupper :
      (k : ℝ) ≤ ((hi + lam) / (2 * Real.pi))) :
    k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  let lower : ℝ := (lo - lam) / (2 * Real.pi)
  let upper : ℝ := (hi + lam) / (2 * Real.pi)
  have hlower_to_floor :
      ⌊lower⌋ ≤ k := by
    have hk_le_k_add_one : (k : ℝ) ≤ (k : ℝ) + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hlower_lt_k_add_one : lower < (k : ℝ) + 1 :=
      lt_of_lt_of_le hlower hk_le_k_add_one
    exact Int.floor_le_iff.mpr hlower_lt_k_add_one
  have hlower_padded :
      ⌊lower⌋ - 1 ≤ k :=
    le_trans
      (sub_le_self ⌊lower⌋ zero_le_one)
      hlower_to_floor
  have hupper_to_floor :
      k ≤ ⌊upper⌋ :=
    Int.le_floor.mpr hupper
  have hupper_padded :
      k ≤ ⌊upper⌋ + 1 :=
    le_trans hupper_to_floor
      (le_add_of_nonneg_right zero_le_one)
  exact
    Finset.mem_Icc.mpr
      (And.intro hlower_padded hupper_padded)

/-- Membership in a range-active center interval also follows from a closed
lower divided bound; the left padding absorbs endpoint equality. -/
theorem Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_closed_lower_divided_bounds
    {lo hi lam : ℝ}
    {k : ℤ}
    (hlower :
      ((lo - lam) / (2 * Real.pi)) ≤ (k : ℝ))
    (hupper :
      (k : ℝ) ≤ ((hi + lam) / (2 * Real.pi))) :
    k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  let lower : ℝ := (lo - lam) / (2 * Real.pi)
  let upper : ℝ := (hi + lam) / (2 * Real.pi)
  have hk_lt_k_add_one : (k : ℝ) < (k : ℝ) + 1 :=
    lt_add_of_pos_right (k : ℝ) zero_lt_one
  have hlower_lt_k_add_one : lower < (k : ℝ) + 1 :=
    lt_of_le_of_lt hlower hk_lt_k_add_one
  have hlower_to_floor :
      ⌊lower⌋ ≤ k :=
    Int.floor_le_iff.mpr hlower_lt_k_add_one
  have hlower_padded :
      ⌊lower⌋ - 1 ≤ k :=
    le_trans
      (sub_le_self ⌊lower⌋ zero_le_one)
      hlower_to_floor
  have hupper_to_floor :
      k ≤ ⌊upper⌋ :=
    Int.le_floor.mpr hupper
  have hupper_padded :
      k ≤ ⌊upper⌋ + 1 :=
    le_trans hupper_to_floor
      (le_add_of_nonneg_right zero_le_one)
  exact
    Finset.mem_Icc.mpr
      (And.intro hlower_padded hupper_padded)

/-- An integer lattice representative that puts a sample increment in the
principal branch belongs to the range-active center interval with radius `π`,
provided the sample increment lies in the chosen range. -/
theorem Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_principal_in_range
    {lo hi θ : ℝ}
    {k : ℤ}
    (hlo : lo ≤ θ)
    (hhi : θ ≤ hi)
    (hprincipal :
      θ - (2 * Real.pi * (k : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    k ∈ Complex.realPhase_integerIncrementRangeActiveCenters
      lo hi Real.pi := by
  let center : ℝ := 2 * Real.pi * (k : ℝ)
  have hupper_principal_period :
      θ - center ≤ -Real.pi + (2 * Real.pi) :=
    hprincipal.2
  have hupper_principal :
      θ - center ≤ Real.pi := by
    have hperiod :
        -Real.pi + (2 * Real.pi) = Real.pi := by
      calc
        -Real.pi + (2 * Real.pi) =
            -Real.pi + (Real.pi + Real.pi) := by
          exact congrArg (fun r : ℝ => -Real.pi + r)
            (two_mul Real.pi)
        _ = (-Real.pi + Real.pi) + Real.pi :=
          (add_assoc (-Real.pi) Real.pi Real.pi).symm
        _ = 0 + Real.pi :=
          congrArg (fun r : ℝ => r + Real.pi)
            (neg_add_cancel Real.pi)
        _ = Real.pi :=
          zero_add Real.pi
    exact
      Eq.subst
        (motive := fun upper : ℝ => θ - center ≤ upper)
        hperiod
        hupper_principal_period
  have hcenter_lower : θ - Real.pi ≤ center :=
    have htheta_minus_center_add_center_le :
        θ - center + center ≤ Real.pi + center :=
      add_le_add_right hupper_principal center
    have htheta_le_pi_add_center : θ ≤ Real.pi + center :=
      Eq.subst
        (motive := fun left : ℝ => left ≤ Real.pi + center)
        (by
          calc
            θ - center + center = θ :=
              sub_add_cancel θ center)
        htheta_minus_center_add_center_le
    have htheta_sub_pi_le_pi_add_center_sub_pi :
        θ - Real.pi ≤ (Real.pi + center) - Real.pi :=
      sub_le_sub_right htheta_le_pi_add_center Real.pi
    have hright_eq : (Real.pi + center) - Real.pi = center := by
      calc
        (Real.pi + center) - Real.pi =
            (center + Real.pi) - Real.pi := by
          exact congrArg (fun r : ℝ => r - Real.pi)
            (add_comm Real.pi center)
        _ = center :=
          add_sub_cancel_right center Real.pi
    Eq.subst
      (motive := fun right : ℝ => θ - Real.pi ≤ right)
      hright_eq
      htheta_sub_pi_le_pi_add_center_sub_pi
  have hlo_sub_le : lo - Real.pi ≤ θ - Real.pi :=
    sub_le_sub_right hlo Real.pi
  have hleft_range_mul : lo - Real.pi ≤ center :=
    le_trans hlo_sub_le hcenter_lower
  have hlower :
      ((lo - Real.pi) / (2 * Real.pi)) ≤ (k : ℝ) :=
    (div_le_iff₀' Real.two_pi_pos).mpr hleft_range_mul
  have hlower_principal : -Real.pi < θ - center :=
    hprincipal.1
  have hcenter_upper : center < θ + Real.pi :=
    have hneg_add_center_lt_theta : -Real.pi + center < θ :=
      add_lt_of_lt_sub_right hlower_principal
    have hneg_add_center_add_pi_lt_theta_add_pi :
        (-Real.pi + center) + Real.pi < θ + Real.pi :=
      add_lt_add_right hneg_add_center_lt_theta Real.pi
    have hleft_eq : (-Real.pi + center) + Real.pi = center := by
      calc
        (-Real.pi + center) + Real.pi =
            -Real.pi + (center + Real.pi) :=
          add_assoc (-Real.pi) center Real.pi
        _ = -Real.pi + (Real.pi + center) := by
          exact congrArg (fun r : ℝ => -Real.pi + r)
            (add_comm center Real.pi)
        _ = (-Real.pi + Real.pi) + center :=
          (add_assoc (-Real.pi) Real.pi center).symm
        _ = 0 + center := by
          exact congrArg (fun r : ℝ => r + center)
            (neg_add_cancel Real.pi)
        _ = center :=
          zero_add center
    Eq.subst
      (motive := fun left : ℝ => left < θ + Real.pi)
      hleft_eq
      hneg_add_center_add_pi_lt_theta_add_pi
  have hhi_add_le : θ + Real.pi ≤ hi + Real.pi :=
    add_le_add_right hhi Real.pi
  have hright_range_mul : center ≤ hi + Real.pi :=
    le_trans (le_of_lt hcenter_upper) hhi_add_le
  have hupper :
      (k : ℝ) ≤ ((hi + Real.pi) / (2 * Real.pi)) :=
    (le_div_iff₀' Real.two_pi_pos).mpr hright_range_mul
  exact
    Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_closed_lower_divided_bounds
      hlower hupper

/-- A principal-strip sample whose raw increment lies in a fixed range has its
strip center in the corresponding finite range-active family with radius
`π`. -/
theorem Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_principalStrip_sample_in_range
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lo hi : ℝ}
    {k : ℤ}
    (hlo : lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi : Complex.realPhase_integerIncrement φ n ≤ hi)
    (hn :
      n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k) :
    k ∈ Complex.realPhase_integerIncrementRangeActiveCenters
      lo hi Real.pi := by
  have hprincipal_shift :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    Complex.realPhase_integerIncrementPrincipalStrip_principal φ hn
  have hshift :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ)) :=
    Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
  have hprincipal_raw :
      Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
      hshift
      hprincipal_shift
  exact
    Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_principal_in_range
      hlo hhi hprincipal_raw

/-- Finite union of principal strips indexed by a finite set of lattice
centers. -/
def Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (K : Finset ℤ) : Finset ℕ :=
  K.biUnion
    (fun k : ℤ =>
      Complex.realPhase_integerIncrementPrincipalStrip φ a b k)

/-- Membership in a finite principal-strip union. -/
theorem Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_iff
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {K : Finset ℤ} :
    n ∈ Complex.realPhase_integerIncrementPrincipalStripFamilyUnion φ a b K ↔
      ∃ k : ℤ,
        k ∈ K ∧
          n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k := by
  exact Finset.mem_biUnion

/-- The range-active principal centers cover every sample whose raw increment
lies in the chosen range. -/
theorem Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_rangeActiveCenters_of_sample_in_range
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lo hi : ℝ}
    (hn_block : n ∈ Finset.Ico a b)
    (hlo : lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi : Complex.realPhase_integerIncrement φ n ≤ hi) :
    n ∈ Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
      φ a b
      (Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi) := by
  match Complex.realPhase_integerIncrement_exists_principal_latticeShift φ n with
  | ⟨k, hk_principal⟩ =>
      have hn_strip :
          n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k :=
        (Complex.mem_realPhase_integerIncrementPrincipalStrip_iff φ).mpr
          (And.intro hn_block hk_principal)
      have hk_active :
          k ∈ Complex.realPhase_integerIncrementRangeActiveCenters
            lo hi Real.pi :=
        Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_principalStrip_sample_in_range
          φ hlo hhi hn_strip
      exact
        (Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_iff
          φ).mpr
          (Exists.intro k (And.intro hk_active hn_strip))

/-- The principal-strip range-active cover is contained in the ambient
half-open block. -/
theorem Complex.realPhase_integerIncrementPrincipalStripFamilyUnion_subset_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {K : Finset ℤ} :
    Complex.realPhase_integerIncrementPrincipalStripFamilyUnion φ a b K ⊆
      Finset.Ico a b := by
  intro n hn
  have hmem :
      ∃ k : ℤ,
        k ∈ K ∧
          n ∈ Complex.realPhase_integerIncrementPrincipalStrip φ a b k :=
    (Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_iff
      φ).mp hn
  match hmem with
  | ⟨k, _hk, hn_strip⟩ =>
      exact
        Complex.realPhase_integerIncrementPrincipalStrip_subset_block
          (φ := φ)
          (a := a)
          (b := b)
          (k := k)
          hn_strip

/-- Principal strips indexed by distinct integer centers are pairwise
disjoint inside any fixed sample block. -/
theorem Complex.realPhase_integerIncrementPrincipalStrip_pairwise_disjoint
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (K : Finset ℤ) :
    ∀ k ∈ K,
      ∀ l ∈ K,
        k ≠ l →
          Disjoint
            (Complex.realPhase_integerIncrementPrincipalStrip φ a b k)
            (Complex.realPhase_integerIncrementPrincipalStrip φ a b l) := by
  intro k _hk l _hl hkl
  exact
    Complex.realPhase_integerIncrementPrincipalStrip_disjoint_of_ne
      φ hkl

/-- The cardinality of a finite principal-strip family is the sum of the
cardinalities of the individual strips. -/
theorem Complex.realPhase_integerIncrementPrincipalStripFamilyUnion_card_eq_sum_cards
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (K : Finset ℤ) :
    (Complex.realPhase_integerIncrementPrincipalStripFamilyUnion φ a b K).card =
      ∑ k ∈ K,
        (Complex.realPhase_integerIncrementPrincipalStrip φ a b k).card := by
  exact
    Finset.card_biUnion
      (Complex.realPhase_integerIncrementPrincipalStrip_pairwise_disjoint
        φ K)

/-- Real-valued cardinality of a finite principal-strip family. -/
theorem Complex.realPhase_integerIncrementPrincipalStripFamilyUnion_card_real_eq_sum_cards
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (K : Finset ℤ) :
    ((Complex.realPhase_integerIncrementPrincipalStripFamilyUnion φ a b K).card :
        ℝ) =
      ∑ k ∈ K,
        ((Complex.realPhase_integerIncrementPrincipalStrip φ a b k).card : ℝ) := by
  exact
    Eq.trans
      (congrArg
        (fun n : ℕ => (n : ℝ))
        (Complex.realPhase_integerIncrementPrincipalStripFamilyUnion_card_eq_sum_cards
          φ K))
      (Nat.cast_sum K
        (fun k : ℤ =>
          (Complex.realPhase_integerIncrementPrincipalStrip φ a b k).card))

/-- A samplewise active-center interval is contained in the range-active
interval when the sample increment lies in that range. -/
theorem Complex.realPhase_integerIncrementSampleActiveCenters_subset_rangeActiveCenters
    (φ : ℝ → ℝ)
    {lo hi lam : ℝ}
    {n : ℕ}
    (hlo :
      lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi :
      Complex.realPhase_integerIncrement φ n ≤ hi) :
    Complex.realPhase_integerIncrementSampleActiveCenters φ lam n ⊆
      Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  intro k hk
  have hk_bounds :
      ⌊((Complex.realPhase_integerIncrement φ n - lam) /
          (2 * Real.pi))⌋ - 1 ≤ k ∧
        k ≤
          ⌊((Complex.realPhase_integerIncrement φ n + lam) /
            (2 * Real.pi))⌋ + 1 :=
    Finset.mem_Icc.mp hk
  have hleft_arg :
      ((lo - lam) / (2 * Real.pi)) ≤
        ((Complex.realPhase_integerIncrement φ n - lam) /
          (2 * Real.pi)) := by
    have hnum :
        lo - lam ≤ Complex.realPhase_integerIncrement φ n - lam :=
      sub_le_sub_right hlo lam
    exact (div_le_div_right Real.two_pi_pos).mpr hnum
  have hleft_floor :
      ⌊((lo - lam) / (2 * Real.pi))⌋ ≤
        ⌊((Complex.realPhase_integerIncrement φ n - lam) /
          (2 * Real.pi))⌋ :=
    Int.floor_mono hleft_arg
  have hleft_padded :
      ⌊((lo - lam) / (2 * Real.pi))⌋ - 1 ≤
        ⌊((Complex.realPhase_integerIncrement φ n - lam) /
          (2 * Real.pi))⌋ - 1 :=
    sub_le_sub_right hleft_floor 1
  have hleft :
      ⌊((lo - lam) / (2 * Real.pi))⌋ - 1 ≤ k :=
    le_trans hleft_padded hk_bounds.1
  have hright_arg :
      ((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi)) ≤
        ((hi + lam) / (2 * Real.pi)) := by
    have hnum :
        Complex.realPhase_integerIncrement φ n + lam ≤ hi + lam :=
      add_le_add_right hhi lam
    exact (div_le_div_right Real.two_pi_pos).mpr hnum
  have hright_floor :
      ⌊((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi))⌋ ≤
        ⌊((hi + lam) / (2 * Real.pi))⌋ :=
    Int.floor_mono hright_arg
  have hright_padded :
      ⌊((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi))⌋ + 1 ≤
        ⌊((hi + lam) / (2 * Real.pi))⌋ + 1 :=
    add_le_add_right hright_floor 1
  have hright :
      k ≤ ⌊((hi + lam) / (2 * Real.pi))⌋ + 1 :=
    le_trans hk_bounds.2 hright_padded
  exact Finset.mem_Icc.mpr (And.intro hleft hright)

/-- If all sample increments on a half-open block lie in a fixed real range,
then the generated active-center family is contained in the range-active
center family. -/
theorem Complex.realPhase_integerIncrementActiveCenters_subset_rangeActiveCenters
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lo hi lam : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi) :
    Complex.realPhase_integerIncrementActiveCenters φ a b lam ⊆
      Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  intro k hk
  have hk_data :
      ∃ n : ℕ,
        n ∈ Finset.Ico a b ∧
          k ∈ Complex.realPhase_integerIncrementSampleActiveCenters φ lam n :=
    Finset.mem_biUnion.mp hk
  match hk_data with
  | ⟨n, hn, hk_sample⟩ =>
      have hn_range :
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi :=
        hrange n hn
      exact
        Complex.realPhase_integerIncrementSampleActiveCenters_subset_rangeActiveCenters
          φ hn_range.1 hn_range.2 hk_sample

/-- Cardinal form of the range-active containment for active centers. -/
theorem Complex.realPhase_integerIncrementActiveCenters_card_le_rangeActiveCenters_card
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lo hi lam : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi) :
    (Complex.realPhase_integerIncrementActiveCenters φ a b lam).card ≤
      (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam).card := by
  exact
    Finset.card_le_card
      (Complex.realPhase_integerIncrementActiveCenters_subset_rangeActiveCenters
        φ hrange)

/-- A center active at one sample belongs to the finite active-center family
of the ambient block. -/
theorem Complex.mem_realPhase_integerIncrementActiveCenters_of_sample
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hn : n ∈ Finset.Ico a b)
    (hk :
      k ∈ Complex.realPhase_integerIncrementSampleActiveCenters φ lam n) :
    k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam := by
  exact
    Finset.mem_biUnion.mpr
      (Exists.intro n (And.intro hn hk))

/-- Samplewise divided lattice bounds put the resonance center into the
finite active-center family of the whole ambient block. -/
theorem Complex.mem_realPhase_integerIncrementActiveCenters_of_sample_divided_bounds
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hn : n ∈ Finset.Ico a b)
    (hlower :
      ((Complex.realPhase_integerIncrement φ n - lam) /
        (2 * Real.pi)) < (k : ℝ))
    (hupper :
      (k : ℝ) ≤
        ((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi))) :
    k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam := by
  exact
    Complex.mem_realPhase_integerIncrementActiveCenters_of_sample
      φ hn
      (Complex.mem_realPhase_integerIncrementSampleActiveCenters_of_divided_bounds
        φ hlower hupper)

/-- A `2πk` resonance inequality forces the divided lattice coordinate of
`k` to lie between the lower and upper `lam`-padded increment coordinates. -/
theorem Complex.realPhase_integerIncrement_resonance_divided_bounds
    (φ : ℝ → ℝ)
    {n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hres :
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ < lam) :
    ((Complex.realPhase_integerIncrement φ n - lam) /
        (2 * Real.pi)) < (k : ℝ) ∧
      (k : ℝ) ≤
        ((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi)) := by
  let θ : ℝ := Complex.realPhase_integerIncrement φ n
  let A : ℝ := 2 * Real.pi * (k : ℝ)
  have htheta :
      θ = Complex.realPhase_integerIncrement φ n :=
    Eq.refl θ
  have hA :
      A = 2 * Real.pi * (k : ℝ) :=
    Eq.refl A
  have h_abs :
      |θ - A| < lam :=
    Eq.subst
      (motive := fun left : ℝ => |left - A| < lam)
      htheta.symm
      (Eq.subst
        (motive := fun center : ℝ =>
          |Complex.realPhase_integerIncrement φ n - center| < lam)
        hA.symm
        (Eq.subst
          (motive := fun r : ℝ => r < lam)
          (Real.norm_eq_abs
            (Complex.realPhase_integerIncrement φ n -
              (2 * Real.pi * (k : ℝ))))
          hres))
  have hleft_abs : -lam < θ - A :=
    (abs_lt.mp h_abs).1
  have hright_abs : θ - A < lam :=
    (abs_lt.mp h_abs).2
  have htheta_lt_A_add_lam :
      θ < A + lam :=
    calc
      θ < lam + A := (sub_lt_iff_lt_add).mp hright_abs
      _ = A + lam := add_comm lam A
  have htheta_sub_lam_lt_A :
      θ - lam < A :=
    (sub_lt_iff_lt_add).mpr htheta_lt_A_add_lam
  have hneg_add_A_lt_theta :
      -lam + A < θ :=
    (lt_sub_iff_add_lt).mp hleft_abs
  have hneg_add_A_eq_A_sub_lam :
      -lam + A = A - lam :=
    Eq.trans
      (add_comm (-lam) A)
      (sub_eq_add_neg A lam).symm
  have hA_sub_lam_lt_theta :
      A - lam < θ :=
    Eq.subst
      (motive := fun r : ℝ => r < θ)
      hneg_add_A_eq_A_sub_lam
      hneg_add_A_lt_theta
  have hA_lt_theta_add_lam :
      A < θ + lam :=
    (sub_lt_iff_lt_add).mp hA_sub_lam_lt_theta
  have hlower :
      ((θ - lam) / (2 * Real.pi)) < (k : ℝ) :=
    (div_lt_iff₀' Real.two_pi_pos).mpr
      (Eq.subst
        (motive := fun right : ℝ => θ - lam < right)
        hA
        htheta_sub_lam_lt_A)
  have hupper_lt :
      (k : ℝ) < ((θ + lam) / (2 * Real.pi)) :=
    (lt_div_iff₀' Real.two_pi_pos).mpr
      (Eq.subst
        (motive := fun left : ℝ => left < θ + lam)
        hA
        hA_lt_theta_add_lam)
  have hbounds_theta :
      ((θ - lam) / (2 * Real.pi)) < (k : ℝ) ∧
        (k : ℝ) ≤ ((θ + lam) / (2 * Real.pi)) :=
    And.intro hlower (le_of_lt hupper_lt)
  exact
    Eq.subst
      (motive := fun theta' : ℝ =>
        ((theta' - lam) / (2 * Real.pi)) < (k : ℝ) ∧
          (k : ℝ) ≤ ((theta' + lam) / (2 * Real.pi)))
      htheta
      hbounds_theta

/-- A resonant sample whose increment lies in an a priori range has its center
in the corresponding range active-center family. -/
theorem Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_resonance_in_range
    (φ : ℝ → ℝ)
    {n : ℕ}
    {lo hi lam : ℝ}
    {k : ℤ}
    (hlo :
      lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi :
      Complex.realPhase_integerIncrement φ n ≤ hi)
    (hres :
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ < lam) :
    k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  let θ : ℝ := Complex.realPhase_integerIncrement φ n
  have htheta :
      θ = Complex.realPhase_integerIncrement φ n :=
    Eq.refl θ
  have hloθ : lo ≤ θ :=
    Eq.subst
      (motive := fun r : ℝ => lo ≤ r)
      htheta.symm
      hlo
  have hθhi : θ ≤ hi :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ hi)
      htheta.symm
      hhi
  have hbounds :
      ((θ - lam) / (2 * Real.pi)) < (k : ℝ) ∧
        (k : ℝ) ≤ ((θ + lam) / (2 * Real.pi)) :=
    Eq.subst
      (motive := fun r : ℝ =>
        ((r - lam) / (2 * Real.pi)) < (k : ℝ) ∧
          (k : ℝ) ≤ ((r + lam) / (2 * Real.pi)))
      htheta.symm
      (Complex.realPhase_integerIncrement_resonance_divided_bounds
        φ hres)
  have hleft_mul :
      θ - lam < 2 * Real.pi * (k : ℝ) :=
    (div_lt_iff₀' Real.two_pi_pos).mp hbounds.1
  have hlo_sub_le :
      lo - lam ≤ θ - lam :=
    sub_le_sub_right hloθ lam
  have hleft_range_mul :
      lo - lam < 2 * Real.pi * (k : ℝ) :=
    lt_of_le_of_lt hlo_sub_le hleft_mul
  have hlower :
      ((lo - lam) / (2 * Real.pi)) < (k : ℝ) :=
    (div_lt_iff₀' Real.two_pi_pos).mpr hleft_range_mul
  have hright_mul :
      2 * Real.pi * (k : ℝ) ≤ θ + lam :=
    (le_div_iff₀' Real.two_pi_pos).mp hbounds.2
  have hθ_add_le :
      θ + lam ≤ hi + lam :=
    add_le_add_right hθhi lam
  have hright_range_mul :
      2 * Real.pi * (k : ℝ) ≤ hi + lam :=
    le_trans hright_mul hθ_add_le
  have hupper :
      (k : ℝ) ≤ ((hi + lam) / (2 * Real.pi)) :=
    (le_div_iff₀' Real.two_pi_pos).mpr hright_range_mul
  exact
    Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_divided_bounds
      hlower hupper

/-- Every resonant sample whose increment lies in an a priori range is covered
by the range-active resonance-family union. -/
theorem Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_rangeActiveCenters_of_window_sample_in_range
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lo hi lam : ℝ}
    {k : ℤ}
    (hlo :
      lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi :
      Complex.realPhase_integerIncrement φ n ≤ hi)
    (hn_window :
      n ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam) :
    n ∈
      Complex.realPhase_integerIncrementResonanceFamilyUnion
        φ a b lam
        (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam) := by
  have hres :
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n)
      (resonance := 2 * Real.pi * (k : ℝ))
      (lam := lam)).mp hn_window |>.2
  have hk :
      k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam :=
    Complex.mem_realPhase_integerIncrementRangeActiveCenters_of_resonance_in_range
      φ hlo hhi hres
  exact
    Finset.mem_biUnion.mpr
      (Exists.intro k (And.intro hk hn_window))

/-- A point outside a range-active resonance-family union is separated from
every integer center, provided its increment lies in the range used to choose
the active family. -/
theorem Complex.realPhase_integerIncrementRangeActiveCentersComplement_separated_from_any_center
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lo hi lam : ℝ}
    (hn :
      n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam
        (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam))
    (hlo :
      lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi :
      Complex.realPhase_integerIncrement φ n ≤ hi)
    (k : ℤ) :
    lam ≤
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ := by
  have hn_data :
      n ∈ Finset.Ico a b ∧
        n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam
          (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam) :=
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mp hn
  have hnot_lt :
      ¬ ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ < lam := by
    intro hlt
    have hn_window :
        n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
      (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
        (φ := φ)
        (a := a)
        (b := b)
        (n := n)
        (resonance := 2 * Real.pi * (k : ℝ))
        (lam := lam)).mpr
        (And.intro hn_data.1 hlt)
    have hn_union :
        n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam
          (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam) :=
      Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_rangeActiveCenters_of_window_sample_in_range
        φ hlo hhi hn_window
    exact hn_data.2 hn_union
  exact le_of_not_gt hnot_lt

/-- Any interval contained in a range-active complement has separated
increments when every point of the interval remains inside the chosen
increment range. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_rangeActiveCentersFamilyComplement
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lo hi lam : ℝ}
    (hgap_subset :
      Finset.Ico c d ⊆
        Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam
          (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam))
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  have hn_range :
      lo ≤ Complex.realPhase_integerIncrement φ n ∧
        Complex.realPhase_integerIncrement φ n ≤ hi :=
    hrange n hn
  exact
    Complex.realPhase_integerIncrementRangeActiveCentersComplement_separated_from_any_center
      φ (hgap_subset hn) hn_range.1 hn_range.2 k

/-- If a center has a resonant sample in the ambient block and the associated
divided lattice bounds hold at that sample, then the center belongs to the
finite active-center family. -/
theorem Complex.mem_realPhase_integerIncrementActiveCenters_of_window_sample_divided_bounds
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hn_window :
      n ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam)
    (hlower :
      ((Complex.realPhase_integerIncrement φ n - lam) /
        (2 * Real.pi)) < (k : ℝ))
    (hupper :
      (k : ℝ) ≤
        ((Complex.realPhase_integerIncrement φ n + lam) /
          (2 * Real.pi))) :
    k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam := by
  have hn_block :
      n ∈ Finset.Ico a b :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n)
      (resonance := 2 * Real.pi * (k : ℝ))
      (lam := lam)).mp hn_window |>.1
  exact
    Complex.mem_realPhase_integerIncrementActiveCenters_of_sample_divided_bounds
      φ hn_block hlower hupper

/-- Any integer center with a resonant sample in the ambient block belongs to
the finite active-center family. -/
theorem Complex.mem_realPhase_integerIncrementActiveCenters_of_window_sample
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hn_window :
      n ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam) :
    k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam := by
  have hdata :
      n ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n)
      (resonance := 2 * Real.pi * (k : ℝ))
      (lam := lam)).mp hn_window
  have hbounds :
      ((Complex.realPhase_integerIncrement φ n - lam) /
          (2 * Real.pi)) < (k : ℝ) ∧
        (k : ℝ) ≤
          ((Complex.realPhase_integerIncrement φ n + lam) /
            (2 * Real.pi)) :=
    Complex.realPhase_integerIncrement_resonance_divided_bounds
      φ hdata.2
  exact
    Complex.mem_realPhase_integerIncrementActiveCenters_of_sample_divided_bounds
      φ hdata.1 hbounds.1 hbounds.2

/-- A nonempty integer-centered resonance window has its center in the finite
active-center family. -/
theorem Complex.mem_realPhase_integerIncrementActiveCenters_of_nonempty_window
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hne :
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam).Nonempty) :
    k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam := by
  match hne with
  | ⟨n, hn_window⟩ =>
      exact
        Complex.mem_realPhase_integerIncrementActiveCenters_of_window_sample
          φ hn_window

/-- Every sample resonant for an arbitrary integer center is covered by the
finite active-center resonance-family union. -/
theorem Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_activeCenters_of_window
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hn_window :
      n ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam) :
    n ∈
      Complex.realPhase_integerIncrementResonanceFamilyUnion
        φ a b lam
        (Complex.realPhase_integerIncrementActiveCenters φ a b lam) := by
  have hk :
      k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam :=
    Complex.mem_realPhase_integerIncrementActiveCenters_of_window_sample
      φ hn_window
  exact
    Finset.mem_biUnion.mpr
      (Exists.intro k (And.intro hk hn_window))

/-- The active-center family cardinal is bounded by the sum of the padded
samplewise center-interval cardinalities. -/
theorem Complex.realPhase_integerIncrementActiveCenters_card_le_sum_sample_cards
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ) :
    (Complex.realPhase_integerIncrementActiveCenters φ a b lam).card ≤
      ∑ n ∈ Finset.Ico a b,
        (Complex.realPhase_integerIncrementSampleActiveCenters φ lam n).card := by
  exact Finset.card_biUnion_le

/-- Real cardinality form of the active-center counting reduction. -/
theorem Complex.realPhase_integerIncrementActiveCenters_card_real_le_sum_sample_cards
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ) :
    ((Complex.realPhase_integerIncrementActiveCenters φ a b lam).card : ℝ) ≤
      ((∑ n ∈ Finset.Ico a b,
        (Complex.realPhase_integerIncrementSampleActiveCenters φ lam n).card :
          ℕ) : ℝ) := by
  exact
    Nat.cast_le.mpr
      (Complex.realPhase_integerIncrementActiveCenters_card_le_sum_sample_cards
        φ a b lam)

/-- Membership in the finite integer-centered resonance family union. -/
theorem Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    {n : ℕ} :
    n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K ↔
      ∃ k : ℤ,
        k ∈ K ∧
          n ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam := by
  exact Finset.mem_biUnion

/-- The finite-family resonance union is contained in the ambient block. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_subset_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {K : Finset ℤ} :
    Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K ⊆
      Finset.Ico a b := by
  intro n hn
  have hmem :
      ∃ k : ℤ,
        k ∈ K ∧
          n ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam :=
    (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
      φ).mp hn
  match hmem with
  | ⟨k, _hk, hn_window⟩ =>
      exact
        (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          (φ := φ)
          (a := a)
          (b := b)
          (n := n)
          (resonance := 2 * Real.pi * (k : ℝ))
          (lam := lam)).mp hn_window |>.1

/-- The finite-family resonance complement is contained in the ambient block. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyComplement_subset_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {K : Finset ℤ} :
    Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K ⊆
      Finset.Ico a b := by
  intro n hn
  exact
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mp hn |>.1

/-- A point in the finite-family complement is separated from every center in
the chosen integer-center family. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyComplement_separated_from_mem_center
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    {k : ℤ}
    (hn :
      n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam K)
    (hk : k ∈ K) :
    lam ≤
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ := by
  have hn_data :
      n ∈ Finset.Ico a b ∧
        n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K :=
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mp hn
  have hnot_lt :
      ¬ ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ < lam := by
    intro hlt
    have hn_window :
        n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
      (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
        (φ := φ)
        (a := a)
        (b := b)
        (n := n)
        (resonance := 2 * Real.pi * (k : ℝ))
        (lam := lam)).mpr
        (And.intro hn_data.1 hlt)
    have hn_union :
        n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K :=
      (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
        φ).mpr
        (Exists.intro k (And.intro hk hn_window))
    exact hn_data.2 hn_union
  exact le_of_not_gt hnot_lt

/-- A point outside the active-center resonance family is separated from every
active center. -/
theorem Complex.realPhase_integerIncrementActiveCentersComplement_separated_from_mem_center
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (hn :
      n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam
        (Complex.realPhase_integerIncrementActiveCenters φ a b lam))
    (hk :
      k ∈ Complex.realPhase_integerIncrementActiveCenters φ a b lam) :
    lam ≤
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ :=
  Complex.realPhase_integerIncrementResonanceFamilyComplement_separated_from_mem_center
    φ hn hk

/-- A point outside the active-center resonance family is separated from every
integer lattice center.  If it were resonant for an arbitrary center, that
center would be active by the samplewise construction, and the point would lie
in the active-family union. -/
theorem Complex.realPhase_integerIncrementActiveCentersComplement_separated_from_any_center
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    (hn :
      n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam
        (Complex.realPhase_integerIncrementActiveCenters φ a b lam))
    (k : ℤ) :
    lam ≤
      ‖Complex.realPhase_integerIncrement φ n -
        (2 * Real.pi * (k : ℝ))‖ := by
  have hn_data :
      n ∈ Finset.Ico a b ∧
        n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam
          (Complex.realPhase_integerIncrementActiveCenters φ a b lam) :=
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mp hn
  have hnot_lt :
      ¬ ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ < lam := by
    intro hlt
    have hn_window :
        n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
      (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
        (φ := φ)
        (a := a)
        (b := b)
        (n := n)
        (resonance := 2 * Real.pi * (k : ℝ))
        (lam := lam)).mpr
        (And.intro hn_data.1 hlt)
    have hn_union :
        n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam
          (Complex.realPhase_integerIncrementActiveCenters φ a b lam) :=
      Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_activeCenters_of_window
        φ hn_window
    exact hn_data.2 hn_union
  exact le_of_not_gt hnot_lt

/-- Any subblock contained in the complement of the active integer-center
resonance family has the standard separated-increment hypothesis. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_activeCentersFamilyComplement
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hgap_subset :
      Finset.Ico c d ⊆
        Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam
          (Complex.realPhase_integerIncrementActiveCenters φ a b lam)) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  exact
    Complex.realPhase_integerIncrementActiveCentersComplement_separated_from_any_center
      φ (hgap_subset hn) k

/-- The finite-family resonance union and complement are disjoint. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_disjoint_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) :
    Disjoint
      (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K)
      (Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K) := by
  exact
    Finset.disjoint_left.mpr
      (fun n hn_union hn_complement =>
        have hn_not_union :
            n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
              φ a b lam K :=
          (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
            φ).mp hn_complement |>.2
        hn_not_union hn_union)

/-- The finite-family resonance union together with its complement covers the
ambient half-open block. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_union_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) :
    Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K ∪
        Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K =
      Finset.Ico a b := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          match Finset.mem_union.mp hn with
          | Or.inl hn_union =>
              Complex.realPhase_integerIncrementResonanceFamilyUnion_subset_block
                φ hn_union
          | Or.inr hn_complement =>
              Complex.realPhase_integerIncrementResonanceFamilyComplement_subset_block
                φ hn_complement)
        (fun hn_block =>
          match Classical.em
              (n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                φ a b lam K) with
          | Or.inl hn_union =>
              Finset.mem_union_left
                (Complex.realPhase_integerIncrementResonanceFamilyComplement
                  φ a b lam K)
                hn_union
          | Or.inr hn_not_union =>
              Finset.mem_union_right
                (Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam K)
                ((Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
                  φ).mpr (And.intro hn_block hn_not_union))))

/-- Additive split of a block sum into the finite resonance-family union and
its complement. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_add_complement
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (F : ℕ → ℂ) :
    (∑ n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
        F n) +
      (∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam K, F n) =
      ∑ n ∈ Finset.Ico a b, F n := by
  have hdisjoint :
      Disjoint
        (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K)
        (Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam K) :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_disjoint_complement
      φ a b lam K
  have hsum_union :
      (∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K ∪
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K, F n) =
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
            F n) +
          ∑ n ∈
            Complex.realPhase_integerIncrementResonanceFamilyComplement
              φ a b lam K, F n :=
    Finset.sum_union hdisjoint
  have hcover :
      Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K ∪
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K =
        Finset.Ico a b :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_union_complement
      φ a b lam K
  have hblock_sum :
      (∑ n ∈ Finset.Ico a b, F n) =
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
            F n) +
          ∑ n ∈
            Complex.realPhase_integerIncrementResonanceFamilyComplement
              φ a b lam K, F n :=
    Eq.trans
      (congrArg (fun S : Finset ℕ => ∑ n ∈ S, F n) hcover.symm)
      hsum_union
  exact hblock_sum.symm

/-- Norm split of a block sum into the finite resonance-family union and its
nonresonant complement. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (F : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Ico a b, F n‖ ≤
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
          F n‖ +
        ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K, F n‖ := by
  have hsum :
      (∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
          F n) +
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K, F n) =
        ∑ n ∈ Finset.Ico a b, F n :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_add_complement
      φ a b lam K F
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ n ∈
            Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
              F n‖ +
            ‖∑ n ∈
              Complex.realPhase_integerIncrementResonanceFamilyComplement
                φ a b lam K, F n‖)
      hsum
      (norm_add_le
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
            F n)
        (∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K, F n))

/-- The sample union attached to a finite family of half-open integer
intervals. -/
def Complex.realPhase_IcoFamilyUnion
    (gaps : Finset (ℕ × ℕ)) : Finset ℕ :=
  gaps.biUnion (fun p : ℕ × ℕ => Finset.Ico p.1 p.2)

/-- The singleton half-open interval family covers exactly that interval. -/
theorem Complex.realPhase_IcoFamilyUnion_singleton
    (a b : ℕ) :
    Complex.realPhase_IcoFamilyUnion (Finset.singleton (a, b)) =
      Finset.Ico a b := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ p : ℕ × ℕ,
                p ∈ Finset.singleton (a, b) ∧
                  n ∈ Finset.Ico p.1 p.2 :=
            Finset.mem_biUnion.mp hn
          match hmem with
          | ⟨p, hp, hn_p⟩ =>
              have hp_eq : p = (a, b) :=
                Finset.mem_singleton.mp hp
              Eq.subst
                (motive := fun q : ℕ × ℕ =>
                  n ∈ Finset.Ico q.1 q.2)
                hp_eq
                hn_p)
        (fun hn =>
          Finset.mem_biUnion.mpr
            (Exists.intro (a, b)
              (And.intro (Finset.mem_singleton_self (a, b)) hn))))

/-- `Complex.realPhase_IcoFamilyUnion` form of the two-gap complement cover. -/
theorem Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_eq_filter_not_Ico
    {a b c d : ℕ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b) :
    Complex.realPhase_IcoFamilyUnion
        (Nat.IcoTwoGapComplement a b c d) =
      (Finset.Ico a b).filter
        (fun n : ℕ => n ∉ Finset.Ico c d) := by
  exact Nat.IcoTwoGapComplement_biUnion_eq_filter_not_Ico
    hac hcd hdb

/-- The two-gap complement family is pairwise disjoint in the generic gap
family sense. -/
theorem Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_pairwiseDisjoint
    {a b c d : ℕ}
    (hcd : c ≤ d) :
    ∀ p₁ : ℕ × ℕ,
      p₁ ∈ Nat.IcoTwoGapComplement a b c d →
        ∀ p₂ : ℕ × ℕ,
          p₂ ∈ Nat.IcoTwoGapComplement a b c d →
            p₁ ≠ p₂ →
              Disjoint (Finset.Ico p₁.1 p₁.2)
                (Finset.Ico p₂.1 p₂.2) :=
  Nat.IcoTwoGapComplement_pairwiseDisjoint hcd

/-- Cardinality bound for the generic two-gap complement family. -/
theorem Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_card_le_two
    (a b c d : ℕ) :
    (Nat.IcoTwoGapComplement a b c d).card ≤ 2 :=
  Nat.IcoTwoGapComplement_card_le_two a b c d

/-- `Complex.realPhase_IcoFamilyUnion` form of the one-point complement cover. -/
theorem Complex.realPhase_IcoFamilyUnion_IcoPointComplement_eq_filter_ne
    {a b x : ℕ}
    (hax : a ≤ x)
    (hxb : x < b) :
    Complex.realPhase_IcoFamilyUnion
        (Nat.IcoPointComplement a b x) =
      (Finset.Ico a b).filter
        (fun n : ℕ => n ≠ x) := by
  exact Nat.IcoPointComplement_biUnion_eq_filter_ne hax hxb

/-- The one-point complement family is pairwise disjoint in the generic gap
family sense. -/
theorem Complex.realPhase_IcoFamilyUnion_IcoPointComplement_pairwiseDisjoint
    {a b x : ℕ} :
    ∀ p₁ : ℕ × ℕ,
      p₁ ∈ Nat.IcoPointComplement a b x →
        ∀ p₂ : ℕ × ℕ,
          p₂ ∈ Nat.IcoPointComplement a b x →
            p₁ ≠ p₂ →
              Disjoint (Finset.Ico p₁.1 p₁.2)
                (Finset.Ico p₂.1 p₂.2) :=
  Nat.IcoPointComplement_pairwiseDisjoint

/-- Cardinality bound for the generic one-point complement family. -/
theorem Complex.realPhase_IcoFamilyUnion_IcoPointComplement_card_le_two
    (a b x : ℕ) :
    (Nat.IcoPointComplement a b x).card ≤ 2 :=
  Nat.IcoPointComplement_card_le_two a b x

/-- A disjoint finite family of half-open integer intervals expands the sum
over its sample union as the sum of interval sums. -/
theorem Complex.realPhase_IcoFamilyUnion_sum_eq_intervalSums
    (gaps : Finset (ℕ × ℕ))
    (F : ℕ → ℂ)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2)) :
    (∑ n ∈ Complex.realPhase_IcoFamilyUnion gaps, F n) =
      ∑ p ∈ gaps, ∑ n ∈ Finset.Ico p.1 p.2, F n := by
  exact Finset.sum_biUnion hdisjoint

/-- If a finite disjoint half-open interval family covers a set and each
interval sum has the same bound, then the covered sum has the cardinality
times bound estimate. -/
theorem Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
    (S : Finset ℕ)
    (gaps : Finset (ℕ × ℕ))
    (F : ℕ → ℂ)
    {B : ℝ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤ B) :
    ‖∑ n ∈ S, F n‖ ≤ ((gaps.card : ℝ) * B) := by
  have hsum_cover :
      (∑ n ∈ S, F n) =
        ∑ n ∈ Complex.realPhase_IcoFamilyUnion gaps, F n :=
    congrArg (fun U : Finset ℕ => ∑ n ∈ U, F n) hcover.symm
  have hsum_family :
      (∑ n ∈ Complex.realPhase_IcoFamilyUnion gaps, F n) =
        ∑ p ∈ gaps, ∑ n ∈ Finset.Ico p.1 p.2, F n :=
    Complex.realPhase_IcoFamilyUnion_sum_eq_intervalSums gaps F hdisjoint
  have htriangle :
      ‖∑ p ∈ gaps, ∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
        ∑ p ∈ gaps, ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ :=
    norm_sum_le gaps
      (fun p : ℕ × ℕ => ∑ n ∈ Finset.Ico p.1 p.2, F n)
  have hsum_bound :
      (∑ p ∈ gaps, ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖) ≤
        ∑ p ∈ gaps, B :=
    Finset.sum_le_sum hgap
  have hconstant :
      (∑ p ∈ gaps, B) = ((gaps.card : ℝ) * B) :=
    Eq.trans
      (Finset.sum_const B)
      (nsmul_eq_mul gaps.card B)
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ ((gaps.card : ℝ) * B))
      (Eq.trans hsum_cover hsum_family).symm
      (le_trans htriangle
        (le_trans hsum_bound
          (le_of_eq hconstant)))

/-- If the two gaps around one removed interval each satisfy a common sum
bound, then the whole complement satisfies twice that bound. -/
theorem Complex.realPhase_sum_norm_le_two_mul_of_IcoTwoGapComplement
    {a b c d : ℕ}
    (F : ℕ → ℂ)
    {B : ℝ}
    (hB : 0 ≤ B)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hgap :
      ∀ p : ℕ × ℕ,
        p ∈ Nat.IcoTwoGapComplement a b c d →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤ B) :
    ‖∑ n ∈ (Finset.Ico a b).filter
        (fun n : ℕ => n ∉ Finset.Ico c d), F n‖ ≤
      2 * B := by
  let gaps : Finset (ℕ × ℕ) := Nat.IcoTwoGapComplement a b c d
  have hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        (Finset.Ico a b).filter
          (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_eq_filter_not_Ico
      hac hcd hdb
  have hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_pairwiseDisjoint
      hcd
  have hcard_nat : gaps.card ≤ 2 :=
    Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_card_le_two
      a b c d
  have hcard_real : (gaps.card : ℝ) ≤ 2 :=
    Nat.cast_le.mpr hcard_nat
  have hcard_bound :
      ((gaps.card : ℝ) * B) ≤ 2 * B :=
    mul_le_mul_of_nonneg_right hcard_real hB
  have hgeneric :
      ‖∑ n ∈ (Finset.Ico a b).filter
          (fun n : ℕ => n ∉ Finset.Ico c d), F n‖ ≤
        ((gaps.card : ℝ) * B) :=
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      ((Finset.Ico a b).filter
        (fun n : ℕ => n ∉ Finset.Ico c d))
      gaps F hcover hdisjoint hgap
  exact le_trans hgeneric hcard_bound

/-- If the two gaps around one removed point each satisfy a common sum bound,
then the whole one-point complement satisfies twice that bound. -/
theorem Complex.realPhase_sum_norm_le_two_mul_of_IcoPointComplement
    {a b x : ℕ}
    (F : ℕ → ℂ)
    {B : ℝ}
    (hB : 0 ≤ B)
    (hax : a ≤ x)
    (hxb : x < b)
    (hgap :
      ∀ p : ℕ × ℕ,
        p ∈ Nat.IcoPointComplement a b x →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤ B) :
    ‖∑ n ∈ (Finset.Ico a b).filter
        (fun n : ℕ => n ≠ x), F n‖ ≤
      2 * B := by
  let gaps : Finset (ℕ × ℕ) := Nat.IcoPointComplement a b x
  have hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        (Finset.Ico a b).filter
          (fun n : ℕ => n ≠ x) :=
    Complex.realPhase_IcoFamilyUnion_IcoPointComplement_eq_filter_ne
      hax hxb
  have hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamilyUnion_IcoPointComplement_pairwiseDisjoint
  have hcard_nat : gaps.card ≤ 2 :=
    Complex.realPhase_IcoFamilyUnion_IcoPointComplement_card_le_two
      a b x
  have hcard_real : (gaps.card : ℝ) ≤ 2 :=
    Nat.cast_le.mpr hcard_nat
  have hcard_bound :
      ((gaps.card : ℝ) * B) ≤ 2 * B :=
    mul_le_mul_of_nonneg_right hcard_real hB
  have hgeneric :
      ‖∑ n ∈ (Finset.Ico a b).filter
          (fun n : ℕ => n ≠ x), F n‖ ≤
        ((gaps.card : ℝ) * B) :=
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      ((Finset.Ico a b).filter
        (fun n : ℕ => n ≠ x))
      gaps F hcover hdisjoint hgap
  exact le_trans hgeneric hcard_bound

/-- Split one selected half-open gap by one point, leaving all other gaps
unchanged. -/
def Complex.realPhase_IcoFamily_splitGapAtPoint
    (gaps : Finset (ℕ × ℕ))
    (p : ℕ × ℕ)
    (x : ℕ) : Finset (ℕ × ℕ) :=
  (gaps.erase p) ∪ Nat.IcoPointComplement p.1 p.2 x

/-- Splitting one selected gap by one point increases the number of gaps by at
most one. -/
theorem Complex.realPhase_IcoFamily_splitGapAtPoint_card_le_succ
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    (hp : p ∈ gaps)
    (x : ℕ) :
    (Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x).card ≤
      gaps.card + 1 := by
  have herase_card :
      (gaps.erase p).card = gaps.card - 1 :=
    Finset.card_erase_of_mem hp
  have hpoint_card :
      (Nat.IcoPointComplement p.1 p.2 x).card ≤ 2 :=
    Nat.IcoPointComplement_card_le_two p.1 p.2 x
  have hunion_card :
      ((gaps.erase p) ∪ Nat.IcoPointComplement p.1 p.2 x).card ≤
        (gaps.erase p).card +
          (Nat.IcoPointComplement p.1 p.2 x).card :=
    Finset.card_union_le (gaps.erase p)
      (Nat.IcoPointComplement p.1 p.2 x)
  have hsum_card :
      (gaps.erase p).card +
          (Nat.IcoPointComplement p.1 p.2 x).card ≤
        (gaps.card - 1) + 2 :=
    add_le_add
      (le_of_eq herase_card)
      hpoint_card
  have hgap_pos : 0 < gaps.card :=
    Finset.card_pos.mpr (Exists.intro p hp)
  have harith :
      (gaps.card - 1) + 2 = gaps.card + 1 := by
    have hpred_succ :
        gaps.card - 1 + 1 = gaps.card :=
      Nat.sub_one_add_one (Nat.ne_of_gt hgap_pos)
    calc
      (gaps.card - 1) + 2 =
          ((gaps.card - 1) + 1) + 1 := by
        exact add_assoc (gaps.card - 1) 1 1
      _ = gaps.card + 1 :=
        congrArg (fun n : ℕ => n + 1) hpred_succ
  exact
    Eq.subst
      (motive := fun right : ℕ =>
        (Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x).card ≤
          right)
      harith
      (le_trans hunion_card hsum_card)

/-- Every interval in the point-complement of a gap is contained in the
original gap. -/
theorem Nat.IcoPointComplement_interval_subset
    {p q : ℕ × ℕ}
    {x : ℕ}
    (hx : x ∈ Finset.Ico p.1 p.2)
    (hq : q ∈ Nat.IcoPointComplement p.1 p.2 x) :
    Finset.Ico q.1 q.2 ⊆ Finset.Ico p.1 p.2 := by
  have hx_bounds : p.1 ≤ x ∧ x < p.2 :=
    Finset.mem_Ico.mp hx
  have hq_cases :
      q = (p.1, x) ∨ q ∈ Finset.singleton (x + 1, p.2) :=
    Finset.mem_insert.mp hq
  match hq_cases with
  | Or.inl hq_left =>
      intro n hn
      have hn_left : n ∈ Finset.Ico p.1 x :=
        Eq.subst
          (motive := fun r : ℕ × ℕ => n ∈ Finset.Ico r.1 r.2)
          hq_left
          hn
      have hn_bounds : p.1 ≤ n ∧ n < x :=
        Finset.mem_Ico.mp hn_left
      exact Finset.mem_Ico.mpr
        (And.intro hn_bounds.1
          (lt_trans hn_bounds.2 hx_bounds.2))
  | Or.inr hq_single =>
      have hq_right : q = (x + 1, p.2) :=
        Finset.mem_singleton.mp hq_single
      intro n hn
      have hn_right : n ∈ Finset.Ico (x + 1) p.2 :=
        Eq.subst
          (motive := fun r : ℕ × ℕ => n ∈ Finset.Ico r.1 r.2)
          hq_right
          hn
      have hn_bounds : x + 1 ≤ n ∧ n < p.2 :=
        Finset.mem_Ico.mp hn_right
      have hp1_le_n : p.1 ≤ n :=
        Nat.le_trans hx_bounds.1
          (Nat.le_trans (Nat.le_succ x) hn_bounds.1)
      exact Finset.mem_Ico.mpr (And.intro hp1_le_n hn_bounds.2)

/-- Splitting a selected disjoint gap by a point covers exactly the old gap
union with that point removed. -/
theorem Complex.realPhase_IcoFamilyUnion_splitGapAtPoint_eq_filter_ne
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    {x : ℕ}
    (hp : p ∈ gaps)
    (hx : x ∈ Finset.Ico p.1 p.2)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2)) :
    Complex.realPhase_IcoFamilyUnion
        (Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x) =
      (Complex.realPhase_IcoFamilyUnion gaps).filter
        (fun n : ℕ => n ≠ x) := by
  have hx_bounds : p.1 ≤ x ∧ x < p.2 :=
    Finset.mem_Ico.mp hx
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ q : ℕ × ℕ,
                q ∈ Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x ∧
                  n ∈ Finset.Ico q.1 q.2 :=
            Finset.mem_biUnion.mp hn
          match hmem with
          | ⟨q, hq_split, hn_q⟩ =>
              have hq_cases :
                  q ∈ gaps.erase p ∨
                    q ∈ Nat.IcoPointComplement p.1 p.2 x :=
                Finset.mem_union.mp hq_split
              match hq_cases with
              | Or.inl hq_erase =>
                  have hq_erase_data : q ≠ p ∧ q ∈ gaps :=
                    Finset.mem_erase.mp hq_erase
                  have hn_old :
                      n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro q
                        (And.intro hq_erase_data.2 hn_q))
                  have hn_ne_x : n ≠ x := by
                    intro hnx
                    have hx_in_q : x ∈ Finset.Ico q.1 q.2 :=
                      Eq.subst
                        (motive := fun r : ℕ => r ∈ Finset.Ico q.1 q.2)
                        hnx
                        hn_q
                    have hdis :
                        Disjoint (Finset.Ico p.1 p.2)
                          (Finset.Ico q.1 q.2) :=
                      hdisjoint p hp q hq_erase_data.2
                        hq_erase_data.1.symm
                    exact
                      (Finset.disjoint_left.mp hdis) hx hx_in_q
                  Finset.mem_filter.mpr (And.intro hn_old hn_ne_x)
              | Or.inr hq_point =>
                  have hpoint_cover :
                      Complex.realPhase_IcoFamilyUnion
                          (Nat.IcoPointComplement p.1 p.2 x) =
                        (Finset.Ico p.1 p.2).filter
                          (fun m : ℕ => m ≠ x) :=
                    Complex.realPhase_IcoFamilyUnion_IcoPointComplement_eq_filter_ne
                      hx_bounds.1 hx_bounds.2
                  have hn_point_union :
                      n ∈ Complex.realPhase_IcoFamilyUnion
                        (Nat.IcoPointComplement p.1 p.2 x) :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro q (And.intro hq_point hn_q))
                  have hn_point_filter :
                      n ∈ (Finset.Ico p.1 p.2).filter
                        (fun m : ℕ => m ≠ x) :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hpoint_cover
                      hn_point_union
                  have hn_point_data :
                      n ∈ Finset.Ico p.1 p.2 ∧ n ≠ x :=
                    Finset.mem_filter.mp hn_point_filter
                  have hn_old :
                      n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro p
                        (And.intro hp hn_point_data.1))
                  Finset.mem_filter.mpr
                    (And.intro hn_old hn_point_data.2))
        (fun hn =>
          have hn_data :
              n ∈ Complex.realPhase_IcoFamilyUnion gaps ∧ n ≠ x :=
            Finset.mem_filter.mp hn
          have hmem_old :
              ∃ q : ℕ × ℕ,
                q ∈ gaps ∧ n ∈ Finset.Ico q.1 q.2 :=
            Finset.mem_biUnion.mp hn_data.1
          match hmem_old with
          | ⟨q, hq, hn_q⟩ =>
              match Classical.decEq (ℕ × ℕ) q p with
              | isTrue hq_eq_p =>
                  have hn_p : n ∈ Finset.Ico p.1 p.2 :=
                    Eq.subst
                      (motive := fun r : ℕ × ℕ =>
                        n ∈ Finset.Ico r.1 r.2)
                      hq_eq_p
                      hn_q
                  have hpoint_cover :
                      Complex.realPhase_IcoFamilyUnion
                          (Nat.IcoPointComplement p.1 p.2 x) =
                        (Finset.Ico p.1 p.2).filter
                          (fun m : ℕ => m ≠ x) :=
                    Complex.realPhase_IcoFamilyUnion_IcoPointComplement_eq_filter_ne
                      hx_bounds.1 hx_bounds.2
                  have hn_point_filter :
                      n ∈ (Finset.Ico p.1 p.2).filter
                        (fun m : ℕ => m ≠ x) :=
                    Finset.mem_filter.mpr
                      (And.intro hn_p hn_data.2)
                  have hn_point_union :
                      n ∈ Complex.realPhase_IcoFamilyUnion
                        (Nat.IcoPointComplement p.1 p.2 x) :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hpoint_cover.symm
                      hn_point_filter
                  have hpoint_union_data :
                      ∃ r : ℕ × ℕ,
                        r ∈ Nat.IcoPointComplement p.1 p.2 x ∧
                          n ∈ Finset.Ico r.1 r.2 :=
                    Finset.mem_biUnion.mp hn_point_union
                  have hpoint_subset :
                      Nat.IcoPointComplement p.1 p.2 x ⊆
                        Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x := by
                    intro r hr
                    exact Finset.mem_union.mpr (Or.inr hr)
                  have hsplit_mem :
                      n ∈ Complex.realPhase_IcoFamilyUnion
                        (Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x) :=
                    match hpoint_union_data with
                    | ⟨r, hr, hn_r⟩ =>
                        Finset.mem_biUnion.mpr
                          (Exists.intro r
                            (And.intro (hpoint_subset hr) hn_r))
                  hsplit_mem
              | isFalse hq_ne_p =>
                  have hq_erase : q ∈ gaps.erase p :=
                    Finset.mem_erase.mpr
                      (And.intro hq_ne_p hq)
                  have hq_split :
                      q ∈ Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x :=
                    Finset.mem_union.mpr (Or.inl hq_erase)
                  Finset.mem_biUnion.mpr
                    (Exists.intro q (And.intro hq_split hn_q))))

/-- Splitting one selected gap in a disjoint gap family preserves pairwise
disjointness. -/
theorem Complex.realPhase_IcoFamily_splitGapAtPoint_pairwiseDisjoint
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    {x : ℕ}
    (hp : p ∈ gaps)
    (hx : x ∈ Finset.Ico p.1 p.2)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2)) :
    ∀ q₁ : ℕ × ℕ,
      q₁ ∈ Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x →
        ∀ q₂ : ℕ × ℕ,
          q₂ ∈ Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x →
            q₁ ≠ q₂ →
              Disjoint (Finset.Ico q₁.1 q₁.2)
                (Finset.Ico q₂.1 q₂.2) := by
  intro q₁ hq₁ q₂ hq₂ hne
  have hq₁_cases :
      q₁ ∈ gaps.erase p ∨
        q₁ ∈ Nat.IcoPointComplement p.1 p.2 x :=
    Finset.mem_union.mp hq₁
  have hq₂_cases :
      q₂ ∈ gaps.erase p ∨
        q₂ ∈ Nat.IcoPointComplement p.1 p.2 x :=
    Finset.mem_union.mp hq₂
  match hq₁_cases with
  | Or.inl hq₁_erase =>
      have hq₁_data : q₁ ≠ p ∧ q₁ ∈ gaps :=
        Finset.mem_erase.mp hq₁_erase
      match hq₂_cases with
      | Or.inl hq₂_erase =>
          have hq₂_data : q₂ ≠ p ∧ q₂ ∈ gaps :=
            Finset.mem_erase.mp hq₂_erase
          exact hdisjoint q₁ hq₁_data.2 q₂ hq₂_data.2 hne
      | Or.inr hq₂_point =>
          have hsubset₂ :
              Finset.Ico q₂.1 q₂.2 ⊆ Finset.Ico p.1 p.2 :=
            Nat.IcoPointComplement_interval_subset hx hq₂_point
          have hdis_old :
              Disjoint (Finset.Ico q₁.1 q₁.2)
                (Finset.Ico p.1 p.2) :=
            hdisjoint q₁ hq₁_data.2 p hp hq₁_data.1
          exact Finset.disjoint_left.mpr
              (fun n hn₁ hn₂ =>
              (Finset.disjoint_left.mp hdis_old) hn₁
                (hsubset₂ hn₂))
  | Or.inr hq₁_point =>
      match hq₂_cases with
      | Or.inl hq₂_erase =>
          have hq₂_data : q₂ ≠ p ∧ q₂ ∈ gaps :=
            Finset.mem_erase.mp hq₂_erase
          have hsubset₁ :
              Finset.Ico q₁.1 q₁.2 ⊆ Finset.Ico p.1 p.2 :=
            Nat.IcoPointComplement_interval_subset hx hq₁_point
          have hdis_old :
              Disjoint (Finset.Ico p.1 p.2)
                (Finset.Ico q₂.1 q₂.2) :=
            hdisjoint p hp q₂ hq₂_data.2 hq₂_data.1.symm
          exact Finset.disjoint_left.mpr
            (fun n hn₁ hn₂ =>
              (Finset.disjoint_left.mp hdis_old)
                (hsubset₁ hn₁) hn₂)
      | Or.inr hq₂_point =>
          exact
            Nat.IcoPointComplement_pairwiseDisjoint
              q₁ hq₁_point q₂ hq₂_point hne

/-- One-step package for the finite gap-cover induction: if a disjoint gap
family covers `S` and the next removed point lies in a selected gap, splitting
that gap gives a disjoint cover of `S.filter (· ≠ x)` with at most one more
gap. -/
theorem Complex.exists_IcoFamily_cover_filter_ne_of_splitGapAtPoint
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {p : ℕ × ℕ}
    {x : ℕ}
    (hp : p ∈ gaps)
    (hx : x ∈ Finset.Ico p.1 p.2)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ S.card + 1) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ≠ x) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ S.card + 1 + 1 := by
  let newGaps : Finset (ℕ × ℕ) :=
    Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x
  have hsplit_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun n : ℕ => n ≠ x) :=
    Complex.realPhase_IcoFamilyUnion_splitGapAtPoint_eq_filter_ne
      gaps hp hx hdisjoint
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        S.filter (fun n : ℕ => n ≠ x) :=
    Eq.trans hsplit_cover
      (congrArg
        (fun U : Finset ℕ => U.filter (fun n : ℕ => n ≠ x))
        hcover)
  have hnew_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ newGaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ newGaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamily_splitGapAtPoint_pairwiseDisjoint
      gaps hp hx hdisjoint
  have hnew_card_to_gaps :
      newGaps.card ≤ gaps.card + 1 :=
    Complex.realPhase_IcoFamily_splitGapAtPoint_card_le_succ
      gaps hp x
  have hgap_card_target :
      gaps.card + 1 ≤ S.card + 1 + 1 :=
    add_le_add_right hcard 1
  have hnew_card :
      newGaps.card ≤ S.card + 1 + 1 :=
    le_trans hnew_card_to_gaps hgap_card_target
  exact Exists.intro newGaps
    (And.intro htarget_cover
      (And.intro hnew_disjoint hnew_card))

/-- Budgeted one-step package for the finite gap-cover induction.  This is
the same split operation as
`exists_IcoFamily_cover_filter_ne_of_splitGapAtPoint`, but the cardinality
bound is measured against an external induction budget. -/
theorem Complex.exists_IcoFamily_cover_filter_ne_of_splitGapAtPoint_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {p : ℕ × ℕ}
    {x budget : ℕ}
    (hp : p ∈ gaps)
    (hx : x ∈ Finset.Ico p.1 p.2)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ≠ x) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ budget + 1 := by
  let newGaps : Finset (ℕ × ℕ) :=
    Complex.realPhase_IcoFamily_splitGapAtPoint gaps p x
  have hsplit_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun n : ℕ => n ≠ x) :=
    Complex.realPhase_IcoFamilyUnion_splitGapAtPoint_eq_filter_ne
      gaps hp hx hdisjoint
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        S.filter (fun n : ℕ => n ≠ x) :=
    Eq.trans hsplit_cover
      (congrArg
        (fun U : Finset ℕ => U.filter (fun n : ℕ => n ≠ x))
        hcover)
  have hnew_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ newGaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ newGaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamily_splitGapAtPoint_pairwiseDisjoint
      gaps hp hx hdisjoint
  have hnew_card_to_gaps :
      newGaps.card ≤ gaps.card + 1 :=
    Complex.realPhase_IcoFamily_splitGapAtPoint_card_le_succ
      gaps hp x
  have hbudget_step :
      gaps.card + 1 ≤ budget + 1 :=
    add_le_add_right hcard 1
  have hnew_card :
      newGaps.card ≤ budget + 1 :=
    le_trans hnew_card_to_gaps hbudget_step
  exact Exists.intro newGaps
    (And.intro htarget_cover
      (And.intro hnew_disjoint hnew_card))

/-- If the next removed point is absent from the currently covered set, the
same gap family covers the filtered set. -/
theorem Complex.exists_IcoFamily_cover_filter_ne_of_not_mem
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {x : ℕ}
    (hx_not : x ∉ S)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ S.card + 1) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ≠ x) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ S.card + 1 := by
  have hfilter_eq : S.filter (fun n : ℕ => n ≠ x) = S := by
    exact Finset.ext
      (fun n =>
        Iff.intro
          (fun hn => (Finset.mem_filter.mp hn).1)
          (fun hn =>
            have hn_ne_x : n ≠ x := by
              intro hnx
              have hx_mem : x ∈ S :=
                Eq.subst
                  (motive := fun r : ℕ => r ∈ S)
                  hnx
                  hn
              exact hx_not hx_mem
            Finset.mem_filter.mpr (And.intro hn hn_ne_x)))
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion gaps =
        S.filter (fun n : ℕ => n ≠ x) :=
    Eq.trans hcover hfilter_eq.symm
  exact Exists.intro gaps
    (And.intro htarget_cover
      (And.intro hdisjoint hcard))

/-- Budgeted absent-point branch for the finite gap-cover induction. -/
theorem Complex.exists_IcoFamily_cover_filter_ne_of_not_mem_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {x budget : ℕ}
    (hx_not : x ∉ S)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ≠ x) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ budget := by
  have hfilter_eq : S.filter (fun n : ℕ => n ≠ x) = S := by
    exact Finset.ext
      (fun n =>
        Iff.intro
          (fun hn => (Finset.mem_filter.mp hn).1)
          (fun hn =>
            have hn_ne_x : n ≠ x := by
              intro hnx
              have hx_mem : x ∈ S :=
                Eq.subst
                  (motive := fun r : ℕ => r ∈ S)
                  hnx
                  hn
              exact hx_not hx_mem
            Finset.mem_filter.mpr (And.intro hn hn_ne_x)))
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion gaps =
        S.filter (fun n : ℕ => n ≠ x) :=
    Eq.trans hcover hfilter_eq.symm
  exact Exists.intro gaps
    (And.intro htarget_cover
      (And.intro hdisjoint hcard))

/-- A point in a covered set lies in one of the covering half-open gaps. -/
theorem Complex.exists_gap_mem_of_mem_IcoFamily_cover
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {x : ℕ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hx : x ∈ S) :
    ∃ p : ℕ × ℕ,
      p ∈ gaps ∧ x ∈ Finset.Ico p.1 p.2 := by
  have hx_union :
      x ∈ Complex.realPhase_IcoFamilyUnion gaps :=
    Eq.subst
      (motive := fun U : Finset ℕ => x ∈ U)
      hcover.symm
      hx
  exact Finset.mem_biUnion.mp hx_union

/-- One-step finite removed-set cover update, combining the absent-point and
split-point branches. -/
theorem Complex.exists_IcoFamily_cover_filter_ne_step
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {x : ℕ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ S.card + 1) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ≠ x) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ S.card + 1 + 1 := by
  match Classical.em (x ∈ S) with
  | Or.inl hxS =>
      have hgap_exists :
          ∃ p : ℕ × ℕ,
            p ∈ gaps ∧ x ∈ Finset.Ico p.1 p.2 :=
        Complex.exists_gap_mem_of_mem_IcoFamily_cover hcover hxS
      match hgap_exists with
      | ⟨p, hp, hx_gap⟩ =>
          exact Complex.exists_IcoFamily_cover_filter_ne_of_splitGapAtPoint
            hp hx_gap hcover hdisjoint hcard
  | Or.inr hx_not =>
      have habsent :
          ∃ newGaps : Finset (ℕ × ℕ),
            Complex.realPhase_IcoFamilyUnion newGaps =
                S.filter (fun n : ℕ => n ≠ x) ∧
              (∀ p₁ : ℕ × ℕ,
                p₁ ∈ newGaps →
                  ∀ p₂ : ℕ × ℕ,
                    p₂ ∈ newGaps →
                      p₁ ≠ p₂ →
                        Disjoint (Finset.Ico p₁.1 p₁.2)
                          (Finset.Ico p₂.1 p₂.2)) ∧
              newGaps.card ≤ S.card + 1 :=
        Complex.exists_IcoFamily_cover_filter_ne_of_not_mem
          hx_not hcover hdisjoint hcard
      match habsent with
      | ⟨newGaps, hnew_cover, hnew_disjoint, hnew_card⟩ =>
          have hcard_weak :
              newGaps.card ≤ S.card + 1 + 1 :=
            le_trans hnew_card
              (Nat.le_succ (S.card + 1))
          exact Exists.intro newGaps
            (And.intro hnew_cover
              (And.intro hnew_disjoint hcard_weak))

/-- Budgeted one-step finite removed-set cover update. -/
theorem Complex.exists_IcoFamily_cover_filter_ne_step_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {x budget : ℕ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ≠ x) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ budget + 1 := by
  match Classical.em (x ∈ S) with
  | Or.inl hxS =>
      have hgap_exists :
          ∃ p : ℕ × ℕ,
            p ∈ gaps ∧ x ∈ Finset.Ico p.1 p.2 :=
        Complex.exists_gap_mem_of_mem_IcoFamily_cover hcover hxS
      match hgap_exists with
      | ⟨p, hp, hx_gap⟩ =>
          exact Complex.exists_IcoFamily_cover_filter_ne_of_splitGapAtPoint_budget
            hp hx_gap hcover hdisjoint hcard
  | Or.inr hx_not =>
      have habsent :
          ∃ newGaps : Finset (ℕ × ℕ),
            Complex.realPhase_IcoFamilyUnion newGaps =
                S.filter (fun n : ℕ => n ≠ x) ∧
              (∀ p₁ : ℕ × ℕ,
                p₁ ∈ newGaps →
                  ∀ p₂ : ℕ × ℕ,
                    p₂ ∈ newGaps →
                      p₁ ≠ p₂ →
                        Disjoint (Finset.Ico p₁.1 p₁.2)
                          (Finset.Ico p₂.1 p₂.2)) ∧
              newGaps.card ≤ budget :=
        Complex.exists_IcoFamily_cover_filter_ne_of_not_mem_budget
          hx_not hcover hdisjoint hcard
      match habsent with
      | ⟨newGaps, hnew_cover, hnew_disjoint, hnew_card⟩ =>
          have hcard_weak :
              newGaps.card ≤ budget + 1 :=
            le_trans hnew_card
              (Nat.le_succ budget)
          exact Exists.intro newGaps
            (And.intro hnew_cover
              (And.intro hnew_disjoint hcard_weak))

/-- Filtering a finite set by removing `R` and then removing `x` is the same
as filtering by removal of `insert x R`. -/
theorem Finset.filter_not_mem_filter_ne_eq_filter_not_mem_insert
    (S R : Finset ℕ)
    (x : ℕ) :
    (S.filter (fun n : ℕ => n ∉ R)).filter
        (fun n : ℕ => n ≠ x) =
      S.filter (fun n : ℕ => n ∉ insert x R) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_data :
              n ∈ S.filter (fun m : ℕ => m ∉ R) ∧ n ≠ x :=
            Finset.mem_filter.mp hn
          have hn_inner :
              n ∈ S ∧ n ∉ R :=
            Finset.mem_filter.mp hn_data.1
          have hn_not_insert : n ∉ insert x R := by
            intro hn_insert
            have hcases : n = x ∨ n ∈ R :=
              Finset.mem_insert.mp hn_insert
            match hcases with
            | Or.inl hnx =>
                exact hn_data.2 hnx
            | Or.inr hnR =>
                exact hn_inner.2 hnR
          Finset.mem_filter.mpr
            (And.intro hn_inner.1 hn_not_insert))
        (fun hn =>
          have hn_data : n ∈ S ∧ n ∉ insert x R :=
            Finset.mem_filter.mp hn
          have hn_not_R : n ∉ R := by
            intro hnR
            have hn_insert : n ∈ insert x R :=
              Finset.mem_insert_of_mem hnR
            exact hn_data.2 hn_insert
          have hn_ne_x : n ≠ x := by
            intro hnx
            have hn_insert : n ∈ insert x R :=
              Eq.subst
                (motive := fun r : ℕ => r ∈ insert x R)
                hnx.symm
                (Finset.mem_insert_self x R)
            exact hn_data.2 hn_insert
          Finset.mem_filter.mpr
            (And.intro
              (Finset.mem_filter.mpr
                (And.intro hn_data.1 hn_not_R))
              hn_ne_x)))

/-- Removing a finite set of points from a half-open natural interval leaves a
finite disjoint family of half-open gaps, with at most one more gap than the
number of removed points. -/
theorem Complex.exists_IcoFamily_cover_Ico_filter_not_mem
    (a b : ℕ)
    (R : Finset ℕ) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          (Finset.Ico a b).filter (fun n : ℕ => n ∉ R) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        gaps.card ≤ R.card + 1 := by
  let P : Finset ℕ → Prop :=
    fun T : Finset ℕ =>
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            (Finset.Ico a b).filter (fun n : ℕ => n ∉ T) ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          gaps.card ≤ T.card + 1
  have hbase : P ∅ := by
    let gaps : Finset (ℕ × ℕ) := Finset.singleton (a, b)
    have hcover_singleton :
        Complex.realPhase_IcoFamilyUnion gaps = Finset.Ico a b := by
      exact Finset.ext
        (fun n =>
          Iff.intro
            (fun hn =>
              have hmem :
                  ∃ p : ℕ × ℕ,
                    p ∈ gaps ∧ n ∈ Finset.Ico p.1 p.2 :=
                Finset.mem_biUnion.mp hn
              match hmem with
              | ⟨p, hp, hn_p⟩ =>
                  have hp_eq : p = (a, b) :=
                    Finset.mem_singleton.mp hp
                  Eq.subst
                    (motive := fun q : ℕ × ℕ =>
                      n ∈ Finset.Ico q.1 q.2)
                    hp_eq
                    hn_p)
            (fun hn =>
              Finset.mem_biUnion.mpr
                (Exists.intro (a, b)
                  (And.intro (Finset.mem_singleton_self (a, b)) hn))))
    have hfilter_empty :
        (Finset.Ico a b).filter (fun n : ℕ => n ∉ (∅ : Finset ℕ)) =
          Finset.Ico a b := by
      exact Finset.ext
        (fun n =>
          Iff.intro
            (fun hn => (Finset.mem_filter.mp hn).1)
            (fun hn =>
              have hn_not_empty : n ∉ (∅ : Finset ℕ) :=
                Finset.not_mem_empty n
              Finset.mem_filter.mpr
                (And.intro hn hn_not_empty)))
    have hcover :
        Complex.realPhase_IcoFamilyUnion gaps =
          (Finset.Ico a b).filter
            (fun n : ℕ => n ∉ (∅ : Finset ℕ)) :=
      Eq.trans hcover_singleton hfilter_empty.symm
    have hdisjoint :
        ∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2) := by
      intro p₁ hp₁ p₂ hp₂ hne
      have hp₁_eq : p₁ = (a, b) :=
        Finset.mem_singleton.mp hp₁
      have hp₂_eq : p₂ = (a, b) :=
        Finset.mem_singleton.mp hp₂
      have hp_eq : p₁ = p₂ :=
        Eq.trans hp₁_eq hp₂_eq.symm
      exact False.elim (hne hp_eq)
    have hcard_eq : gaps.card = 1 :=
      Finset.card_singleton (a, b)
    have hempty_card : (∅ : Finset ℕ).card + 1 = 1 := by
      have hempty : (∅ : Finset ℕ).card = 0 :=
        Finset.card_empty
      exact congrArg (fun n : ℕ => n + 1) hempty
    have hcard :
        gaps.card ≤ (∅ : Finset ℕ).card + 1 :=
      Eq.subst
        (motive := fun right : ℕ => gaps.card ≤ right)
        hempty_card.symm
        (le_of_eq hcard_eq)
    exact Exists.intro gaps
      (And.intro hcover (And.intro hdisjoint hcard))
  have hstep :
      ∀ ⦃x : ℕ⦄ {T : Finset ℕ}, x ∉ T → P T → P (insert x T) := by
    intro x T hx_not_T hT
    match hT with
    | ⟨gaps, hcover, hdisjoint, hcard⟩ =>
        let S : Finset ℕ :=
          (Finset.Ico a b).filter (fun n : ℕ => n ∉ T)
        have hstep_exists :
            ∃ newGaps : Finset (ℕ × ℕ),
              Complex.realPhase_IcoFamilyUnion newGaps =
                  S.filter (fun n : ℕ => n ≠ x) ∧
                (∀ p₁ : ℕ × ℕ,
                  p₁ ∈ newGaps →
                    ∀ p₂ : ℕ × ℕ,
                      p₂ ∈ newGaps →
                        p₁ ≠ p₂ →
                          Disjoint (Finset.Ico p₁.1 p₁.2)
                            (Finset.Ico p₂.1 p₂.2)) ∧
                newGaps.card ≤ (T.card + 1) + 1 :=
          Complex.exists_IcoFamily_cover_filter_ne_step_budget
            hcover hdisjoint hcard
        match hstep_exists with
        | ⟨newGaps, hnew_cover_raw, hnew_disjoint, hnew_card_raw⟩ =>
            have hfilter_insert :
                S.filter (fun n : ℕ => n ≠ x) =
                  (Finset.Ico a b).filter
                    (fun n : ℕ => n ∉ insert x T) :=
              Finset.filter_not_mem_filter_ne_eq_filter_not_mem_insert
                (Finset.Ico a b) T x
            have hnew_cover :
                Complex.realPhase_IcoFamilyUnion newGaps =
                  (Finset.Ico a b).filter
                    (fun n : ℕ => n ∉ insert x T) :=
              Eq.trans hnew_cover_raw hfilter_insert
            have hinsert_card : (insert x T).card = T.card + 1 :=
              Finset.card_insert_of_not_mem hx_not_T
            have htarget_card_eq :
                (insert x T).card + 1 = (T.card + 1) + 1 :=
              congrArg (fun n : ℕ => n + 1) hinsert_card
            have hnew_card :
                newGaps.card ≤ (insert x T).card + 1 :=
              Eq.subst
                (motive := fun right : ℕ => newGaps.card ≤ right)
                htarget_card_eq.symm
                hnew_card_raw
            exact Exists.intro newGaps
              (And.intro hnew_cover
                (And.intro hnew_disjoint hnew_card))
  exact Finset.induction_on R hbase (fun x T hx_not_T hT => hstep hx_not_T hT)

/-- Split one selected half-open gap by removing a half-open subinterval,
leaving all other gaps unchanged. -/
def Complex.realPhase_IcoFamily_splitGapAtIco
    (gaps : Finset (ℕ × ℕ))
    (p : ℕ × ℕ)
    (c d : ℕ) : Finset (ℕ × ℕ) :=
  (gaps.erase p) ∪ Nat.IcoTwoGapComplement p.1 p.2 c d

/-- Splitting one selected gap by a half-open subinterval increases the number
of gaps by at most one. -/
theorem Complex.realPhase_IcoFamily_splitGapAtIco_card_le_succ
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    (hp : p ∈ gaps)
    (c d : ℕ) :
    (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d).card ≤
      gaps.card + 1 := by
  have herase_card :
      (gaps.erase p).card = gaps.card - 1 :=
    Finset.card_erase_of_mem hp
  have htwo_card :
      (Nat.IcoTwoGapComplement p.1 p.2 c d).card ≤ 2 :=
    Nat.IcoTwoGapComplement_card_le_two p.1 p.2 c d
  have hunion_card :
      ((gaps.erase p) ∪ Nat.IcoTwoGapComplement p.1 p.2 c d).card ≤
        (gaps.erase p).card +
          (Nat.IcoTwoGapComplement p.1 p.2 c d).card :=
    Finset.card_union_le (gaps.erase p)
      (Nat.IcoTwoGapComplement p.1 p.2 c d)
  have hsum_card :
      (gaps.erase p).card +
          (Nat.IcoTwoGapComplement p.1 p.2 c d).card ≤
        (gaps.card - 1) + 2 :=
    add_le_add
      (le_of_eq herase_card)
      htwo_card
  have hgap_pos : 0 < gaps.card :=
    Finset.card_pos.mpr (Exists.intro p hp)
  have harith :
      (gaps.card - 1) + 2 = gaps.card + 1 := by
    have hpred_succ :
        gaps.card - 1 + 1 = gaps.card :=
      Nat.sub_one_add_one (Nat.ne_of_gt hgap_pos)
    calc
      (gaps.card - 1) + 2 =
          ((gaps.card - 1) + 1) + 1 := by
        exact add_assoc (gaps.card - 1) 1 1
      _ = gaps.card + 1 :=
        congrArg (fun n : ℕ => n + 1) hpred_succ
  exact
    Eq.subst
      (motive := fun right : ℕ =>
        (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d).card ≤
          right)
      harith
      (le_trans hunion_card hsum_card)

/-- Every interval in the two-gap complement of a subinterval is contained in
the original gap. -/
theorem Nat.IcoTwoGapComplement_interval_subset
    {p q : ℕ × ℕ}
    {c d : ℕ}
    (hpc : p.1 ≤ c)
    (hcd : c ≤ d)
    (hdp : d ≤ p.2)
    (hq : q ∈ Nat.IcoTwoGapComplement p.1 p.2 c d) :
    Finset.Ico q.1 q.2 ⊆ Finset.Ico p.1 p.2 := by
  have hq_cases :
      q = (p.1, c) ∨ q ∈ Finset.singleton (d, p.2) :=
    Finset.mem_insert.mp hq
  match hq_cases with
  | Or.inl hq_left =>
      intro n hn
      have hn_left : n ∈ Finset.Ico p.1 c :=
        Eq.subst
          (motive := fun r : ℕ × ℕ => n ∈ Finset.Ico r.1 r.2)
          hq_left
          hn
      have hn_bounds : p.1 ≤ n ∧ n < c :=
        Finset.mem_Ico.mp hn_left
      exact Finset.mem_Ico.mpr
        (And.intro hn_bounds.1
          (lt_of_lt_of_le hn_bounds.2 (Nat.le_trans hcd hdp)))
  | Or.inr hq_single =>
      have hq_right : q = (d, p.2) :=
        Finset.mem_singleton.mp hq_single
      intro n hn
      have hn_right : n ∈ Finset.Ico d p.2 :=
        Eq.subst
          (motive := fun r : ℕ × ℕ => n ∈ Finset.Ico r.1 r.2)
          hq_right
          hn
      have hn_bounds : d ≤ n ∧ n < p.2 :=
        Finset.mem_Ico.mp hn_right
      have hp1_le_n : p.1 ≤ n :=
        Nat.le_trans hpc (Nat.le_trans hcd hn_bounds.1)
      exact Finset.mem_Ico.mpr (And.intro hp1_le_n hn_bounds.2)

/-- Splitting a selected disjoint gap by a contained half-open interval covers
exactly the old gap union with that interval removed. -/
theorem Complex.realPhase_IcoFamilyUnion_splitGapAtIco_eq_filter_not_Ico
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    {c d : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c ≤ d)
    (hdp : d ≤ p.2)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2)) :
    Complex.realPhase_IcoFamilyUnion
        (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d) =
      (Complex.realPhase_IcoFamilyUnion gaps).filter
        (fun n : ℕ => n ∉ Finset.Ico c d) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ q : ℕ × ℕ,
                q ∈ Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d ∧
                  n ∈ Finset.Ico q.1 q.2 :=
            Finset.mem_biUnion.mp hn
          match hmem with
          | ⟨q, hq_split, hn_q⟩ =>
              have hq_cases :
                  q ∈ gaps.erase p ∨
                    q ∈ Nat.IcoTwoGapComplement p.1 p.2 c d :=
                Finset.mem_union.mp hq_split
              match hq_cases with
              | Or.inl hq_erase =>
                  have hq_data : q ≠ p ∧ q ∈ gaps :=
                    Finset.mem_erase.mp hq_erase
                  have hn_old :
                      n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro q (And.intro hq_data.2 hn_q))
                  have hn_not_removed :
                      n ∉ Finset.Ico c d := by
                    intro hn_removed
                    have hremoved_subset :
                        Finset.Ico c d ⊆ Finset.Ico p.1 p.2 := by
                      intro m hm
                      have hm_bounds : c ≤ m ∧ m < d :=
                        Finset.mem_Ico.mp hm
                      exact Finset.mem_Ico.mpr
                        (And.intro
                          (Nat.le_trans hpc hm_bounds.1)
                          (lt_of_lt_of_le hm_bounds.2 hdp))
                    have hdis :
                        Disjoint (Finset.Ico p.1 p.2)
                          (Finset.Ico q.1 q.2) :=
                      hdisjoint p hp q hq_data.2 hq_data.1.symm
                    exact
                      (Finset.disjoint_left.mp hdis)
                        (hremoved_subset hn_removed) hn_q
                  Finset.mem_filter.mpr
                    (And.intro hn_old hn_not_removed)
              | Or.inr hq_two =>
                  have htwo_cover :
                      Complex.realPhase_IcoFamilyUnion
                          (Nat.IcoTwoGapComplement p.1 p.2 c d) =
                        (Finset.Ico p.1 p.2).filter
                          (fun m : ℕ => m ∉ Finset.Ico c d) :=
                    Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_eq_filter_not_Ico
                      hpc hcd hdp
                  have hn_two_union :
                      n ∈ Complex.realPhase_IcoFamilyUnion
                        (Nat.IcoTwoGapComplement p.1 p.2 c d) :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro q (And.intro hq_two hn_q))
                  have hn_two_filter :
                      n ∈ (Finset.Ico p.1 p.2).filter
                        (fun m : ℕ => m ∉ Finset.Ico c d) :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      htwo_cover
                      hn_two_union
                  have hn_two_data :
                      n ∈ Finset.Ico p.1 p.2 ∧
                        n ∉ Finset.Ico c d :=
                    Finset.mem_filter.mp hn_two_filter
                  have hn_old :
                      n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro p (And.intro hp hn_two_data.1))
                  Finset.mem_filter.mpr
                    (And.intro hn_old hn_two_data.2))
        (fun hn =>
          have hn_data :
              n ∈ Complex.realPhase_IcoFamilyUnion gaps ∧
                n ∉ Finset.Ico c d :=
            Finset.mem_filter.mp hn
          have hmem_old :
              ∃ q : ℕ × ℕ,
                q ∈ gaps ∧ n ∈ Finset.Ico q.1 q.2 :=
            Finset.mem_biUnion.mp hn_data.1
          match hmem_old with
          | ⟨q, hq, hn_q⟩ =>
              match Classical.decEq (ℕ × ℕ) q p with
              | isTrue hq_eq_p =>
                  have hn_p : n ∈ Finset.Ico p.1 p.2 :=
                    Eq.subst
                      (motive := fun r : ℕ × ℕ =>
                        n ∈ Finset.Ico r.1 r.2)
                      hq_eq_p
                      hn_q
                  have htwo_cover :
                      Complex.realPhase_IcoFamilyUnion
                          (Nat.IcoTwoGapComplement p.1 p.2 c d) =
                        (Finset.Ico p.1 p.2).filter
                          (fun m : ℕ => m ∉ Finset.Ico c d) :=
                    Complex.realPhase_IcoFamilyUnion_IcoTwoGapComplement_eq_filter_not_Ico
                      hpc hcd hdp
                  have hn_two_filter :
                      n ∈ (Finset.Ico p.1 p.2).filter
                        (fun m : ℕ => m ∉ Finset.Ico c d) :=
                    Finset.mem_filter.mpr
                      (And.intro hn_p hn_data.2)
                  have hn_two_union :
                      n ∈ Complex.realPhase_IcoFamilyUnion
                        (Nat.IcoTwoGapComplement p.1 p.2 c d) :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      htwo_cover.symm
                      hn_two_filter
                  have htwo_union_data :
                      ∃ r : ℕ × ℕ,
                        r ∈ Nat.IcoTwoGapComplement p.1 p.2 c d ∧
                          n ∈ Finset.Ico r.1 r.2 :=
                    Finset.mem_biUnion.mp hn_two_union
                  have htwo_subset :
                      Nat.IcoTwoGapComplement p.1 p.2 c d ⊆
                        Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d := by
                    intro r hr
                    exact Finset.mem_union.mpr (Or.inr hr)
                  match htwo_union_data with
                  | ⟨r, hr, hn_r⟩ =>
                      Finset.mem_biUnion.mpr
                        (Exists.intro r
                          (And.intro (htwo_subset hr) hn_r))
              | isFalse hq_ne_p =>
                  have hq_erase : q ∈ gaps.erase p :=
                    Finset.mem_erase.mpr
                      (And.intro hq_ne_p hq)
                  have hq_split :
                      q ∈ Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d :=
                    Finset.mem_union.mpr (Or.inl hq_erase)
                  Finset.mem_biUnion.mpr
                    (Exists.intro q (And.intro hq_split hn_q))))

/-- Splitting one selected gap in a disjoint gap family by a contained
half-open interval preserves pairwise disjointness. -/
theorem Complex.realPhase_IcoFamily_splitGapAtIco_pairwiseDisjoint
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    {c d : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c ≤ d)
    (hdp : d ≤ p.2)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2)) :
    ∀ q₁ : ℕ × ℕ,
      q₁ ∈ Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d →
        ∀ q₂ : ℕ × ℕ,
          q₂ ∈ Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d →
            q₁ ≠ q₂ →
              Disjoint (Finset.Ico q₁.1 q₁.2)
                (Finset.Ico q₂.1 q₂.2) := by
  intro q₁ hq₁ q₂ hq₂ hne
  have hq₁_cases :
      q₁ ∈ gaps.erase p ∨
        q₁ ∈ Nat.IcoTwoGapComplement p.1 p.2 c d :=
    Finset.mem_union.mp hq₁
  have hq₂_cases :
      q₂ ∈ gaps.erase p ∨
        q₂ ∈ Nat.IcoTwoGapComplement p.1 p.2 c d :=
    Finset.mem_union.mp hq₂
  match hq₁_cases with
  | Or.inl hq₁_erase =>
      have hq₁_data : q₁ ≠ p ∧ q₁ ∈ gaps :=
        Finset.mem_erase.mp hq₁_erase
      match hq₂_cases with
      | Or.inl hq₂_erase =>
          have hq₂_data : q₂ ≠ p ∧ q₂ ∈ gaps :=
            Finset.mem_erase.mp hq₂_erase
          exact hdisjoint q₁ hq₁_data.2 q₂ hq₂_data.2 hne
      | Or.inr hq₂_two =>
          have hsubset₂ :
              Finset.Ico q₂.1 q₂.2 ⊆ Finset.Ico p.1 p.2 :=
            Nat.IcoTwoGapComplement_interval_subset hpc hcd hdp hq₂_two
          have hdis_old :
              Disjoint (Finset.Ico q₁.1 q₁.2)
                (Finset.Ico p.1 p.2) :=
            hdisjoint q₁ hq₁_data.2 p hp hq₁_data.1
          exact Finset.disjoint_left.mpr
            (fun n hn₁ hn₂ =>
              (Finset.disjoint_left.mp hdis_old) hn₁
                (hsubset₂ hn₂))
  | Or.inr hq₁_two =>
      match hq₂_cases with
      | Or.inl hq₂_erase =>
          have hq₂_data : q₂ ≠ p ∧ q₂ ∈ gaps :=
            Finset.mem_erase.mp hq₂_erase
          have hsubset₁ :
              Finset.Ico q₁.1 q₁.2 ⊆ Finset.Ico p.1 p.2 :=
            Nat.IcoTwoGapComplement_interval_subset hpc hcd hdp hq₁_two
          have hdis_old :
              Disjoint (Finset.Ico p.1 p.2)
                (Finset.Ico q₂.1 q₂.2) :=
            hdisjoint p hp q₂ hq₂_data.2 hq₂_data.1.symm
          exact Finset.disjoint_left.mpr
            (fun n hn₁ hn₂ =>
              (Finset.disjoint_left.mp hdis_old)
                (hsubset₁ hn₁) hn₂)
      | Or.inr hq₂_two =>
          exact
            Nat.IcoTwoGapComplement_pairwiseDisjoint hcd
              q₁ hq₁_two q₂ hq₂_two hne

/-- A nonempty half-open interval contained in an ambient half-open interval
and avoiding a removed half-open interval lies wholly in the left or right
remaining gap. -/
theorem Nat.Ico_subset_left_or_right_of_subset_Ico_of_disjoint_Ico
    {a b c d e f : ℕ}
    (hcd : c < d)
    (hef : e < f)
    (hsub : Finset.Ico e f ⊆ Finset.Ico a b)
    (havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico e f →
          n ∉ Finset.Ico c d) :
    Finset.Ico e f ⊆ Finset.Ico a c ∨
      Finset.Ico e f ⊆ Finset.Ico d b := by
  match lt_or_ge e d with
  | Or.inr hd_le_e =>
      exact Or.inr
        (fun n hn =>
          have hn_bounds : e ≤ n ∧ n < f :=
            Finset.mem_Ico.mp hn
          have hn_block_bounds : a ≤ n ∧ n < b :=
            Finset.mem_Ico.mp (hsub hn)
          Finset.mem_Ico.mpr
            (And.intro (Nat.le_trans hd_le_e hn_bounds.1)
              hn_block_bounds.2))
  | Or.inl he_lt_d =>
      match lt_or_ge c f with
      | Or.inr hf_le_c =>
          exact Or.inl
            (fun n hn =>
              have hn_bounds : e ≤ n ∧ n < f :=
                Finset.mem_Ico.mp hn
              have hn_block_bounds : a ≤ n ∧ n < b :=
                Finset.mem_Ico.mp (hsub hn)
              Finset.mem_Ico.mpr
                (And.intro hn_block_bounds.1
                  (lt_of_lt_of_le hn_bounds.2 hf_le_c)))
      | Or.inl hc_lt_f =>
          have he_le_c_or_c_le_e : e ≤ c ∨ c ≤ e :=
            le_total e c
          match he_le_c_or_c_le_e with
          | Or.inl he_le_c =>
              have hc_mem_source : c ∈ Finset.Ico e f :=
                Finset.mem_Ico.mpr (And.intro he_le_c hc_lt_f)
              have hc_mem_removed : c ∈ Finset.Ico c d :=
                Finset.mem_Ico.mpr (And.intro le_rfl hcd)
              exact False.elim ((havoid c hc_mem_source) hc_mem_removed)
          | Or.inr hc_le_e =>
              have he_mem_source : e ∈ Finset.Ico e f :=
                Finset.mem_Ico.mpr (And.intro le_rfl hef)
              have he_mem_removed : e ∈ Finset.Ico c d :=
                Finset.mem_Ico.mpr (And.intro hc_le_e he_lt_d)
              exact False.elim ((havoid e he_mem_source) he_mem_removed)

/-- A half-open interval family is interval-connected when every nonempty
half-open interval contained in its union is contained in one member of the
family. -/
def Complex.realPhase_IcoFamilyIntervalConnected
    (gaps : Finset (ℕ × ℕ)) : Prop :=
  ∀ {c d : ℕ},
    Finset.Ico c d ⊆ Complex.realPhase_IcoFamilyUnion gaps →
      c < d →
        ∃ p : ℕ × ℕ,
          p ∈ gaps ∧ Finset.Ico c d ⊆ Finset.Ico p.1 p.2

/-- The singleton ambient gap family is interval-connected. -/
theorem Complex.realPhase_IcoFamilyIntervalConnected_singleton
    (a b : ℕ) :
    Complex.realPhase_IcoFamilyIntervalConnected
      (Finset.singleton (a, b)) := by
  intro c d hsub _hcd
  have hcontained :
      Finset.Ico c d ⊆ Finset.Ico a b := by
    intro n hn
    have hn_union :
        n ∈ Complex.realPhase_IcoFamilyUnion
          (Finset.singleton (a, b)) :=
      hsub hn
    have hmem :
        ∃ p : ℕ × ℕ,
          p ∈ Finset.singleton (a, b) ∧
            n ∈ Finset.Ico p.1 p.2 :=
      Finset.mem_biUnion.mp hn_union
    match hmem with
    | ⟨p, hp, hn_p⟩ =>
        have hp_eq : p = (a, b) :=
          Finset.mem_singleton.mp hp
        exact
          Eq.subst
            (motive := fun q : ℕ × ℕ => n ∈ Finset.Ico q.1 q.2)
            hp_eq
            hn_p
  exact
    Exists.intro (a, b)
      (And.intro (Finset.mem_singleton_self (a, b)) hcontained)

/-- Endpoint bounds forced by containment of a nonempty half-open interval in
another half-open interval. -/
theorem Nat.Ico_endpoint_bounds_of_subset_of_nonempty
    {a b c d : ℕ}
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (hcd : c < d) :
    a ≤ c ∧ d ≤ b := by
  have hc_mem_source : c ∈ Finset.Ico c d :=
    Finset.mem_Ico.mpr (And.intro le_rfl hcd)
  have hc_mem_target : c ∈ Finset.Ico a b :=
    hsub hc_mem_source
  have hac : a ≤ c :=
    (Finset.mem_Ico.mp hc_mem_target).1
  let r : ℕ := d - 1
  have hd_pos : 0 < d :=
    lt_of_le_of_lt (Nat.zero_le c) hcd
  have hr_succ : r + 1 = d :=
    Nat.succ_pred_eq_of_pos hd_pos
  have hc_le_r : c ≤ r :=
    Nat.le_pred_of_lt hcd
  have hr_lt_d : r < d := by
    have hr_succ_le : r + 1 ≤ d :=
      le_of_eq hr_succ
    exact Nat.lt_of_succ_le hr_succ_le
  have hr_mem_source : r ∈ Finset.Ico c d :=
    Finset.mem_Ico.mpr (And.intro hc_le_r hr_lt_d)
  have hr_mem_target : r ∈ Finset.Ico a b :=
    hsub hr_mem_source
  have hr_lt_b : r < b :=
    (Finset.mem_Ico.mp hr_mem_target).2
  have hr_succ_le_b : r + 1 ≤ b :=
    Nat.succ_le_of_lt hr_lt_b
  have hdb : d ≤ b :=
    Eq.subst
      (motive := fun m : ℕ => m ≤ b)
      hr_succ
      hr_succ_le_b
  exact And.intro hac hdb

/-- Splitting one gap by a nonempty contained half-open interval preserves
the interval-connected cover invariant. -/
theorem Complex.realPhase_IcoFamily_splitGapAtIco_intervalConnected
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    {c d : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c < d)
    (hdp : d ≤ p.2)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps) :
    Complex.realPhase_IcoFamilyIntervalConnected
      (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d) := by
  intro e f hsub hef
  have hcd_le : c ≤ d :=
    le_of_lt hcd
  have hsplit_cover :
      Complex.realPhase_IcoFamilyUnion
          (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d) =
        (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Complex.realPhase_IcoFamilyUnion_splitGapAtIco_eq_filter_not_Ico
      gaps hp hpc hcd_le hdp hdisjoint
  have hsub_old :
      Finset.Ico e f ⊆ Complex.realPhase_IcoFamilyUnion gaps := by
    intro n hn
    have hn_split :
        n ∈ Complex.realPhase_IcoFamilyUnion
          (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d) :=
      hsub hn
    have hn_filter :
        n ∈ (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun m : ℕ => m ∉ Finset.Ico c d) :=
      Eq.subst
        (motive := fun S : Finset ℕ => n ∈ S)
        hsplit_cover
        hn_split
    exact (Finset.mem_filter.mp hn_filter).1
  have havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico e f →
          n ∉ Finset.Ico c d := by
    intro n hn
    have hn_split :
        n ∈ Complex.realPhase_IcoFamilyUnion
          (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d) :=
      hsub hn
    have hn_filter :
        n ∈ (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun m : ℕ => m ∉ Finset.Ico c d) :=
      Eq.subst
        (motive := fun S : Finset ℕ => n ∈ S)
        hsplit_cover
        hn_split
    exact (Finset.mem_filter.mp hn_filter).2
  have hcontainer :
      ∃ q : ℕ × ℕ,
        q ∈ gaps ∧ Finset.Ico e f ⊆ Finset.Ico q.1 q.2 :=
    hconnected hsub_old hef
  match hcontainer with
  | ⟨q, hq, hq_contains⟩ =>
      match Classical.decEq (ℕ × ℕ) q p with
      | isFalse hq_ne_p =>
          have hq_erase : q ∈ gaps.erase p :=
            Finset.mem_erase.mpr (And.intro hq_ne_p hq)
          have hq_split :
              q ∈ Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d :=
            Finset.mem_union.mpr (Or.inl hq_erase)
          exact Exists.intro q (And.intro hq_split hq_contains)
      | isTrue hq_eq_p =>
          have hsub_p :
              Finset.Ico e f ⊆ Finset.Ico p.1 p.2 := by
            intro n hn
            have hnq : n ∈ Finset.Ico q.1 q.2 :=
              hq_contains hn
            exact
              Eq.subst
                (motive := fun r : ℕ × ℕ => n ∈ Finset.Ico r.1 r.2)
                hq_eq_p
                hnq
          have hside :
              Finset.Ico e f ⊆ Finset.Ico p.1 c ∨
                Finset.Ico e f ⊆ Finset.Ico d p.2 :=
            Nat.Ico_subset_left_or_right_of_subset_Ico_of_disjoint_Ico
              hcd hef hsub_p havoid
          match hside with
          | Or.inl hleft =>
              have hleft_mem :
                  (p.1, c) ∈ Nat.IcoTwoGapComplement p.1 p.2 c d :=
                Finset.mem_insert_self (p.1, c)
                  (Finset.singleton (d, p.2))
              have hleft_split :
                  (p.1, c) ∈
                    Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d :=
                Finset.mem_union.mpr (Or.inr hleft_mem)
              exact
                Exists.intro (p.1, c)
                  (And.intro hleft_split hleft)
          | Or.inr hright =>
              have hright_mem :
                  (d, p.2) ∈ Nat.IcoTwoGapComplement p.1 p.2 c d :=
                Finset.mem_insert_of_mem
                  (Finset.mem_singleton_self (d, p.2))
              have hright_split :
                  (d, p.2) ∈
                    Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d :=
                Finset.mem_union.mpr (Or.inr hright_mem)
              exact
                Exists.intro (d, p.2)
                  (And.intro hright_split hright)

/-- Budgeted one-step package for removing one contained half-open interval
from a disjoint gap cover. -/
theorem Complex.exists_IcoFamily_cover_filter_not_Ico_of_splitGapAtIco_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {p : ℕ × ℕ}
    {c d budget : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c ≤ d)
    (hdp : d ≤ p.2)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ budget + 1 := by
  let newGaps : Finset (ℕ × ℕ) :=
    Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d
  have hsplit_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Complex.realPhase_IcoFamilyUnion_splitGapAtIco_eq_filter_not_Ico
      gaps hp hpc hcd hdp hdisjoint
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        S.filter (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Eq.trans hsplit_cover
      (congrArg
        (fun U : Finset ℕ =>
          U.filter (fun n : ℕ => n ∉ Finset.Ico c d))
        hcover)
  have hnew_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ newGaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ newGaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamily_splitGapAtIco_pairwiseDisjoint
      gaps hp hpc hcd hdp hdisjoint
  have hnew_card_to_gaps :
      newGaps.card ≤ gaps.card + 1 :=
    Complex.realPhase_IcoFamily_splitGapAtIco_card_le_succ
      gaps hp c d
  have hbudget_step :
      gaps.card + 1 ≤ budget + 1 :=
    add_le_add_right hcard 1
  have hnew_card :
      newGaps.card ≤ budget + 1 :=
    le_trans hnew_card_to_gaps hbudget_step
  exact Exists.intro newGaps
    (And.intro htarget_cover
      (And.intro hnew_disjoint hnew_card))

/-- Budgeted one-step package for removing one nonempty contained half-open
interval while preserving the interval-connected cover invariant. -/
theorem Complex.exists_IcoFamily_connected_cover_filter_not_Ico_of_splitGapAtIco_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {p : ℕ × ℕ}
    {c d budget : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c < d)
    (hdp : d ≤ p.2)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps)
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
        newGaps.card ≤ budget + 1 := by
  let newGaps : Finset (ℕ × ℕ) :=
    Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d
  have hcd_le : c ≤ d :=
    le_of_lt hcd
  have hsplit_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Complex.realPhase_IcoFamilyUnion_splitGapAtIco_eq_filter_not_Ico
      gaps hp hpc hcd_le hdp hdisjoint
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        S.filter (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Eq.trans hsplit_cover
      (congrArg
        (fun U : Finset ℕ =>
          U.filter (fun n : ℕ => n ∉ Finset.Ico c d))
        hcover)
  have hnew_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ newGaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ newGaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamily_splitGapAtIco_pairwiseDisjoint
      gaps hp hpc hcd_le hdp hdisjoint
  have hnew_connected :
      Complex.realPhase_IcoFamilyIntervalConnected newGaps :=
    Complex.realPhase_IcoFamily_splitGapAtIco_intervalConnected
      gaps hp hpc hcd hdp hdisjoint hconnected
  have hnew_card_to_gaps :
      newGaps.card ≤ gaps.card + 1 :=
    Complex.realPhase_IcoFamily_splitGapAtIco_card_le_succ
      gaps hp c d
  have hbudget_step :
      gaps.card + 1 ≤ budget + 1 :=
    add_le_add_right hcard 1
  have hnew_card :
      newGaps.card ≤ budget + 1 :=
    le_trans hnew_card_to_gaps hbudget_step
  exact Exists.intro newGaps
    (And.intro htarget_cover
      (And.intro hnew_disjoint
        (And.intro hnew_connected hnew_card)))

/-- Removing an empty half-open interval leaves an interval-connected cover
unchanged. -/
theorem Complex.exists_IcoFamily_connected_cover_filter_not_Ico_of_empty_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {c d budget : ℕ}
    (hdc : d ≤ c)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps)
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
        newGaps.card ≤ budget := by
  have hfilter_eq :
      S.filter (fun n : ℕ => n ∉ Finset.Ico c d) = S := by
    exact Finset.ext
      (fun n =>
        Iff.intro
          (fun hn => (Finset.mem_filter.mp hn).1)
          (fun hn =>
            have hn_not : n ∉ Finset.Ico c d := by
              intro hn_cd
              have hn_bounds : c ≤ n ∧ n < d :=
                Finset.mem_Ico.mp hn_cd
              have hd_le_n : d ≤ n :=
                Nat.le_trans hdc hn_bounds.1
              exact not_lt_of_ge hd_le_n hn_bounds.2
            Finset.mem_filter.mpr (And.intro hn hn_not)))
  have htarget :
      Complex.realPhase_IcoFamilyUnion gaps =
        S.filter (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Eq.trans hcover hfilter_eq.symm
  exact Exists.intro gaps
    (And.intro htarget
      (And.intro hdisjoint
        (And.intro hconnected hcard)))

/-- One induction step for removing a whole half-open interval from an
interval-connected gap cover.  Nonempty intervals split the unique containing
gap; empty intervals leave the cover unchanged. -/
theorem Complex.exists_IcoFamily_connected_cover_filter_not_Ico_step_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {c d budget : ℕ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps)
    (hcard : gaps.card ≤ budget)
    (hwindow_subset : Finset.Ico c d ⊆ S) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
        newGaps.card ≤ budget + 1 := by
  match lt_or_ge c d with
  | Or.inr hdc =>
      have hsame :
          ∃ newGaps : Finset (ℕ × ℕ),
            Complex.realPhase_IcoFamilyUnion newGaps =
                S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
              (∀ p₁ : ℕ × ℕ,
                p₁ ∈ newGaps →
                  ∀ p₂ : ℕ × ℕ,
                    p₂ ∈ newGaps →
                      p₁ ≠ p₂ →
                        Disjoint (Finset.Ico p₁.1 p₁.2)
                          (Finset.Ico p₂.1 p₂.2)) ∧
              Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
              newGaps.card ≤ budget :=
        Complex.exists_IcoFamily_connected_cover_filter_not_Ico_of_empty_budget
          hdc hcover hdisjoint hconnected hcard
      match hsame with
      | ⟨newGaps, hcover_new, hdisjoint_new, hconnected_new, hcard_new⟩ =>
          have hcard_succ : newGaps.card ≤ budget + 1 :=
            le_trans hcard_new (Nat.le_succ budget)
          exact Exists.intro newGaps
            (And.intro hcover_new
              (And.intro hdisjoint_new
                (And.intro hconnected_new hcard_succ)))
  | Or.inl hcd =>
      have hwindow_union :
          Finset.Ico c d ⊆ Complex.realPhase_IcoFamilyUnion gaps := by
        intro n hn
        have hnS : n ∈ S :=
          hwindow_subset hn
        exact
          Eq.subst
            (motive := fun U : Finset ℕ => n ∈ U)
            hcover.symm
            hnS
      have hp_exists :
          ∃ p : ℕ × ℕ,
            p ∈ gaps ∧ Finset.Ico c d ⊆ Finset.Ico p.1 p.2 :=
        hconnected hwindow_union hcd
      match hp_exists with
      | ⟨p, hp, hp_contains⟩ =>
          have hbounds :
              p.1 ≤ c ∧ d ≤ p.2 :=
            Nat.Ico_endpoint_bounds_of_subset_of_nonempty
              hp_contains hcd
          exact
            Complex.exists_IcoFamily_connected_cover_filter_not_Ico_of_splitGapAtIco_budget
              hp hbounds.1 hcd hbounds.2 hcover hdisjoint
              hconnected hcard

/-- Budgeted absent-interval branch for interval-removal gap covers. -/
theorem Complex.exists_IcoFamily_cover_filter_not_Ico_of_disjoint_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {c d budget : ℕ}
    (hS_disjoint : Disjoint S (Finset.Ico c d))
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        newGaps.card ≤ budget := by
  have hfilter_eq :
      S.filter (fun n : ℕ => n ∉ Finset.Ico c d) = S := by
    exact Finset.ext
      (fun n =>
        Iff.intro
          (fun hn => (Finset.mem_filter.mp hn).1)
          (fun hn =>
            have hn_not_window : n ∉ Finset.Ico c d := by
              intro hn_window
              exact (Finset.disjoint_left.mp hS_disjoint) hn hn_window
            Finset.mem_filter.mpr
              (And.intro hn hn_not_window)))
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion gaps =
        S.filter (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Eq.trans hcover hfilter_eq.symm
  exact Exists.intro gaps
    (And.intro htarget_cover
      (And.intro hdisjoint hcard))

/-- If a window is contained in the covered set and nonempty, then one of the
covering gaps contains its left endpoint. -/
theorem Complex.exists_gap_containing_window_left_endpoint_of_subset_cover
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {c d : ℕ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hwindow_subset : Finset.Ico c d ⊆ S)
    (hcd_strict : c < d) :
    ∃ p : ℕ × ℕ,
      p ∈ gaps ∧ c ∈ Finset.Ico p.1 p.2 := by
  have hc_window : c ∈ Finset.Ico c d :=
    Finset.mem_Ico.mpr (And.intro le_rfl hcd_strict)
  have hcS : c ∈ S :=
    hwindow_subset hc_window
  exact Complex.exists_gap_mem_of_mem_IcoFamily_cover hcover hcS

/-- If a new half-open window starts after the end of every earlier
half-open window, then it is disjoint from the union of those earlier
windows. -/
theorem Complex.Ico_disjoint_IcoFamilyUnion_of_forall_right_le_left
    {gaps : Finset (ℕ × ℕ)}
    {c d : ℕ}
    (horder :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          p.2 ≤ c) :
    Disjoint (Finset.Ico c d) (Complex.realPhase_IcoFamilyUnion gaps) := by
  exact Finset.disjoint_left.mpr
    (fun n hn_window hn_union =>
      have hn_window_bounds : c ≤ n ∧ n < d :=
        Finset.mem_Ico.mp hn_window
      have hmem :
          ∃ p : ℕ × ℕ,
            p ∈ gaps ∧ n ∈ Finset.Ico p.1 p.2 :=
        Finset.mem_biUnion.mp hn_union
      match hmem with
      | ⟨p, hp, hn_p⟩ =>
          have hn_p_bounds : p.1 ≤ n ∧ n < p.2 :=
            Finset.mem_Ico.mp hn_p
          have hp_right_le_c : p.2 ≤ c :=
            horder p hp
          have hn_lt_c : n < c :=
            lt_of_lt_of_le hn_p_bounds.2 hp_right_le_c
          (not_lt_of_ge hn_window_bounds.1) hn_lt_c)

/-- If a new half-open window ends before the start of every earlier
half-open window, then it is disjoint from the union of those earlier
windows. -/
theorem Complex.Ico_disjoint_IcoFamilyUnion_of_forall_right_le_start
    {gaps : Finset (ℕ × ℕ)}
    {c d : ℕ}
    (horder :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          d ≤ p.1) :
    Disjoint (Finset.Ico c d) (Complex.realPhase_IcoFamilyUnion gaps) := by
  exact Finset.disjoint_left.mpr
    (fun n hn_window hn_union =>
      have hn_window_bounds : c ≤ n ∧ n < d :=
        Finset.mem_Ico.mp hn_window
      have hmem :
          ∃ p : ℕ × ℕ,
            p ∈ gaps ∧ n ∈ Finset.Ico p.1 p.2 :=
        Finset.mem_biUnion.mp hn_union
      match hmem with
      | ⟨p, hp, hn_p⟩ =>
          have hn_p_bounds : p.1 ≤ n ∧ n < p.2 :=
            Finset.mem_Ico.mp hn_p
          have hd_le_p_left : d ≤ p.1 :=
            horder p hp
          have hd_le_n : d ≤ n :=
            Nat.le_trans hd_le_p_left hn_p_bounds.1
          (not_lt_of_ge hd_le_n) hn_window_bounds.2)

/-- A window disjoint from the removed family union is contained in the
corresponding complement exactly when it is contained in the ambient block. -/
theorem Complex.Ico_subset_filter_not_IcoFamilyUnion_of_subset_block_of_disjoint
    {a b c d : ℕ}
    {gaps : Finset (ℕ × ℕ)}
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (hdis :
      Disjoint (Finset.Ico c d)
        (Complex.realPhase_IcoFamilyUnion gaps)) :
    Finset.Ico c d ⊆
      (Finset.Ico a b).filter
        (fun n : ℕ => n ∉ Complex.realPhase_IcoFamilyUnion gaps) := by
  intro n hn
  have hn_block : n ∈ Finset.Ico a b :=
    hsub hn
  have hn_not_union :
      n ∉ Complex.realPhase_IcoFamilyUnion gaps := by
    intro hn_union
    exact (Finset.disjoint_left.mp hdis) hn hn_union
  exact Finset.mem_filter.mpr
    (And.intro hn_block hn_not_union)

/-- A finite family of resonance windows represented by half-open intervals
has a half-open interval union equal to the corresponding generic gap-family
union of those interval representatives. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_eq_IcoFamilyUnion_of_window_eq
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (cd : ℤ → ℕ × ℕ)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
            Finset.Ico (cd k).1 (cd k).2) :
    Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K =
      Complex.realPhase_IcoFamilyUnion (K.image cd) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ k : ℤ,
                k ∈ K ∧
                  n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (k : ℝ)) lam :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
              φ).mp hn
          match hmem with
          | ⟨k, hk, hn_window⟩ =>
              have hn_Ico :
                  n ∈ Finset.Ico (cd k).1 (cd k).2 :=
                Eq.subst
                  (motive := fun S : Finset ℕ => n ∈ S)
                  (hwindow k hk)
                  hn_window
              have hcd_mem : cd k ∈ K.image cd :=
                Finset.mem_image.mpr
                  (Exists.intro k (And.intro hk rfl))
              Finset.mem_biUnion.mpr
                (Exists.intro (cd k)
                  (And.intro hcd_mem hn_Ico)))
        (fun hn =>
          have hmem :
              ∃ p : ℕ × ℕ,
                p ∈ K.image cd ∧ n ∈ Finset.Ico p.1 p.2 :=
            Finset.mem_biUnion.mp hn
          match hmem with
          | ⟨p, hp, hn_p⟩ =>
              have hp_pre :
                  ∃ k : ℤ, k ∈ K ∧ cd k = p :=
                Finset.mem_image.mp hp
              match hp_pre with
              | ⟨k, hk, hcd_eq⟩ =>
                  have hn_Ico :
                      n ∈ Finset.Ico (cd k).1 (cd k).2 :=
                    Eq.subst
                      (motive := fun q : ℕ × ℕ =>
                        n ∈ Finset.Ico q.1 q.2)
                      hcd_eq.symm
                      hn_p
                  have hn_window :
                      n ∈ Complex.realPhase_integerIncrementResonanceWindow
                        φ a b (2 * Real.pi * (k : ℝ)) lam :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      (hwindow k hk).symm
                      hn_Ico
                  (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
                    φ).mpr
                    (Exists.intro k (And.intro hk hn_window))))

/-- Increasing ordered resonance-window representatives are disjoint from a
new later window. -/
theorem Complex.Ico_disjoint_previous_resonanceFamilyUnion_of_forall_window_right_le_left
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (cd : ℤ → ℕ × ℕ)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
            Finset.Ico (cd k).1 (cd k).2)
    (horder :
      ∀ k : ℤ,
        k ∈ K →
          (cd k).2 ≤ c) :
    Disjoint (Finset.Ico c d)
      (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K) := by
  have hunion :
      Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K =
        Complex.realPhase_IcoFamilyUnion (K.image cd) :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_eq_IcoFamilyUnion_of_window_eq
      φ cd hwindow
  have horder_image :
      ∀ p : ℕ × ℕ,
        p ∈ K.image cd →
          p.2 ≤ c := by
    intro p hp
    have hpre :
        ∃ k : ℤ, k ∈ K ∧ cd k = p :=
      Finset.mem_image.mp hp
    match hpre with
    | ⟨k, hk, hkp⟩ =>
        exact Eq.subst
          (motive := fun q : ℕ × ℕ => q.2 ≤ c)
          hkp
          (horder k hk)
  have hdis_image :
      Disjoint (Finset.Ico c d)
        (Complex.realPhase_IcoFamilyUnion (K.image cd)) :=
    Complex.Ico_disjoint_IcoFamilyUnion_of_forall_right_le_left
      horder_image
  exact
    Eq.subst
      (motive := fun S : Finset ℕ =>
        Disjoint (Finset.Ico c d) S)
      hunion.symm
      hdis_image

/-- Decreasing ordered resonance-window representatives are disjoint from a
new earlier window. -/
theorem Complex.Ico_disjoint_previous_resonanceFamilyUnion_of_forall_window_left_ge_right
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (cd : ℤ → ℕ × ℕ)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
            Finset.Ico (cd k).1 (cd k).2)
    (horder :
      ∀ k : ℤ,
        k ∈ K →
          d ≤ (cd k).1) :
    Disjoint (Finset.Ico c d)
      (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K) := by
  have hunion :
      Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K =
        Complex.realPhase_IcoFamilyUnion (K.image cd) :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_eq_IcoFamilyUnion_of_window_eq
      φ cd hwindow
  have horder_image :
      ∀ p : ℕ × ℕ,
        p ∈ K.image cd →
          d ≤ p.1 := by
    intro p hp
    have hpre :
        ∃ k : ℤ, k ∈ K ∧ cd k = p :=
      Finset.mem_image.mp hp
    match hpre with
    | ⟨k, hk, hkp⟩ =>
        exact Eq.subst
          (motive := fun q : ℕ × ℕ => d ≤ q.1)
          hkp
          (horder k hk)
  have hdis_image :
      Disjoint (Finset.Ico c d)
        (Complex.realPhase_IcoFamilyUnion (K.image cd)) :=
    Complex.Ico_disjoint_IcoFamilyUnion_of_forall_right_le_start
      horder_image
  exact
    Eq.subst
      (motive := fun S : Finset ℕ =>
        Disjoint (Finset.Ico c d) S)
      hunion.symm
      hdis_image

/-- Increasing ordered resonance-window representatives put a new later
window inside the previous-family complement. -/
theorem Complex.Ico_subset_resonanceFamilyComplement_of_forall_window_right_le_left
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (cd : ℤ → ℕ × ℕ)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
            Finset.Ico (cd k).1 (cd k).2)
    (horder :
      ∀ k : ℤ,
        k ∈ K →
          (cd k).2 ≤ c) :
    Finset.Ico c d ⊆
      Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam K := by
  have hdis :
      Disjoint (Finset.Ico c d)
        (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K) :=
    Complex.Ico_disjoint_previous_resonanceFamilyUnion_of_forall_window_right_le_left
      φ cd hwindow horder
  intro n hn
  have hn_block : n ∈ Finset.Ico a b :=
    hsub hn
  have hn_not_union :
      n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K := by
    intro hn_union
    exact (Finset.disjoint_left.mp hdis) hn hn_union
  exact
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mpr
      (And.intro hn_block hn_not_union)

/-- Decreasing ordered resonance-window representatives put a new earlier
window inside the previous-family complement. -/
theorem Complex.Ico_subset_resonanceFamilyComplement_of_forall_window_left_ge_right
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (cd : ℤ → ℕ × ℕ)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
            Finset.Ico (cd k).1 (cd k).2)
    (horder :
      ∀ k : ℤ,
        k ∈ K →
          d ≤ (cd k).1) :
    Finset.Ico c d ⊆
      Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam K := by
  have hdis :
      Disjoint (Finset.Ico c d)
        (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K) :=
    Complex.Ico_disjoint_previous_resonanceFamilyUnion_of_forall_window_left_ge_right
      φ cd hwindow horder
  intro n hn
  have hn_block : n ∈ Finset.Ico a b :=
    hsub hn
  have hn_not_union :
      n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K := by
    intro hn_union
    exact (Finset.disjoint_left.mp hdis) hn hn_union
  exact
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mpr
      (And.intro hn_block hn_not_union)

/-- The empty resonance-family complement is the whole ambient block. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyComplement_empty
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ) :
    Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam (∅ : Finset ℤ) =
      Finset.Ico a b := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
            φ).mp hn |>.1)
        (fun hn =>
          have hn_not_union :
              n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                φ a b lam (∅ : Finset ℤ) := by
            intro hn_union
            have hmem :
                ∃ k : ℤ,
                  k ∈ (∅ : Finset ℤ) ∧
                    n ∈ Complex.realPhase_integerIncrementResonanceWindow
                      φ a b (2 * Real.pi * (k : ℝ)) lam :=
              (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
                φ).mp hn_union
            match hmem with
            | ⟨k, hk, _hnk⟩ =>
                exact Finset.not_mem_empty k hk
          (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
            φ).mpr
            (And.intro hn hn_not_union)))

/-- A half-open representative of a resonance window lies in the previous
family complement when that window is disjoint from the previous family union. -/
theorem Complex.Ico_subset_resonanceFamilyComplement_of_window_disjoint_union
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    {k : ℤ}
    {K : Finset ℤ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam =
        Finset.Ico c d)
    (hdis :
      Disjoint
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam)
        (Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K)) :
    Finset.Ico c d ⊆
      Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam K := by
  intro n hn
  have hn_window :
      n ∈ Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam :=
    Eq.subst
      (motive := fun S : Finset ℕ => n ∈ S)
      hwindow.symm
      hn
  have hn_window_data :
      n ∈ Finset.Ico a b ∧
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ < lam :=
    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
      (φ := φ)
      (a := a)
      (b := b)
      (n := n)
      (resonance := 2 * Real.pi * (k : ℝ))
      (lam := lam)).mp hn_window
  have hn_not_union :
      n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
        φ a b lam K := by
    intro hn_union
    exact (Finset.disjoint_left.mp hdis) hn_window hn_union
  exact
    (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
      φ).mpr
      (And.intro hn_window_data.1 hn_not_union)

/-- A new thin integer-centered window is contained in the complement of any
finite family not containing its center. -/
theorem Complex.Ico_subset_resonanceFamilyComplement_of_window_eq_of_not_mem_of_le_pi
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    {k : ℤ}
    {K : Finset ℤ}
    (hlam : lam ≤ Real.pi)
    (hk : k ∉ K)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam =
        Finset.Ico c d) :
    Finset.Ico c d ⊆
      Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam K := by
  have hdis :
      Disjoint
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam)
        (Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K) := by
    exact Finset.disjoint_left.mpr
      (fun n hn_window hn_union =>
        have hmem :
            ∃ j : ℤ,
              j ∈ K ∧
                n ∈ Complex.realPhase_integerIncrementResonanceWindow
                  φ a b (2 * Real.pi * (j : ℝ)) lam :=
          (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
            φ).mp hn_union
        match hmem with
        | ⟨j, hj, hn_j⟩ =>
            match Classical.decEq ℤ k j with
            | isTrue hkj =>
                have hk_mem : k ∈ K :=
                  Eq.subst
                    (motive := fun q : ℤ => q ∈ K)
                    hkj.symm
                    hj
                False.elim (hk hk_mem)
            | isFalse hkj =>
                have hdis_kj :
                    Disjoint
                      (Complex.realPhase_integerIncrementResonanceWindow
                        φ a b (2 * Real.pi * (k : ℝ)) lam)
                      (Complex.realPhase_integerIncrementResonanceWindow
                        φ a b (2 * Real.pi * (j : ℝ)) lam) :=
                  Complex.realPhase_integerIncrementResonanceWindow_disjoint_of_ne_of_le_pi
                    φ hlam hkj
                (Finset.disjoint_left.mp hdis_kj) hn_window hn_j)
  exact
    Complex.Ico_subset_resonanceFamilyComplement_of_window_disjoint_union
      φ hwindow hdis

/-- Once a resonance window has been identified with `Ico c d`, its canonical
window complement is exactly the ambient block filtered by membership outside
that interval. -/
theorem Complex.realPhase_integerIncrementResonanceWindowComplement_eq_filter_not_Ico_of_window_eq
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b resonance lam =
      (Finset.Ico a b).filter
        (fun n : ℕ => n ∉ Finset.Ico c d) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_data :
              n ∈ Finset.Ico a b ∧
                ¬ ‖Complex.realPhase_integerIncrement φ n -
                    resonance‖ < lam :=
            (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
              (φ := φ)
              (a := a)
              (b := b)
              (n := n)
              (resonance := resonance)
              (lam := lam)).mp hn
          have hn_not_Ico : n ∉ Finset.Ico c d := by
            intro hn_Ico
            have hn_window :
                n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b resonance lam :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hwindow.symm
                hn_Ico
            have hn_window_data :
                n ∈ Finset.Ico a b ∧
                  ‖Complex.realPhase_integerIncrement φ n -
                    resonance‖ < lam :=
              (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                (φ := φ)
                (a := a)
                (b := b)
                (n := n)
                (resonance := resonance)
                (lam := lam)).mp hn_window
            exact hn_data.2 hn_window_data.2
          Finset.mem_filter.mpr (And.intro hn_data.1 hn_not_Ico))
        (fun hn =>
          have hn_data :
              n ∈ Finset.Ico a b ∧ n ∉ Finset.Ico c d :=
            Finset.mem_filter.mp hn
          have hn_not_res : ¬
              ‖Complex.realPhase_integerIncrement φ n -
                  resonance‖ < lam := by
            intro hres
            have hn_window :
                n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b resonance lam :=
              (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                (φ := φ)
                (a := a)
                (b := b)
                (n := n)
                (resonance := resonance)
                (lam := lam)).mpr
                (And.intro hn_data.1 hres)
            have hn_Ico : n ∈ Finset.Ico c d :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hwindow
                hn_window
            exact hn_data.2 hn_Ico
          (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
            (φ := φ)
            (a := a)
            (b := b)
            (n := n)
            (resonance := resonance)
            (lam := lam)).mpr
            (And.intro hn_data.1 hn_not_res)))

/-- Two-gap norm bound for the canonical complement of a resonance window
identified as a half-open interval. -/
theorem Complex.realPhase_resonanceWindowComplement_sum_norm_le_two_mul_of_window_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam B : ℝ}
    (F : ℕ → ℂ)
    (hB : 0 ≤ B)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d)
    (hgap :
      ∀ p : ℕ × ℕ,
        p ∈ Nat.IcoTwoGapComplement a b c d →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤ B) :
    ‖∑ n ∈
      Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b resonance lam, F n‖ ≤
      2 * B := by
  have hcomplement :
      Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b resonance lam =
        (Finset.Ico a b).filter
          (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Complex.realPhase_integerIncrementResonanceWindowComplement_eq_filter_not_Ico_of_window_eq
      φ hwindow
  have hfiltered :
      ‖∑ n ∈ (Finset.Ico a b).filter
          (fun n : ℕ => n ∉ Finset.Ico c d), F n‖ ≤
        2 * B :=
    Complex.realPhase_sum_norm_le_two_mul_of_IcoTwoGapComplement
      F hB hac hcd hdb hgap
  exact
    Eq.subst
      (motive := fun S : Finset ℕ =>
        ‖∑ n ∈ S, F n‖ ≤ 2 * B)
      hcomplement.symm
      hfiltered

/-- A singleton resonance-family union is the corresponding single
integer-centered resonance window. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_singleton
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (k : ℤ) :
    Complex.realPhase_integerIncrementResonanceFamilyUnion
        φ a b lam (Finset.singleton k) =
      Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (k : ℝ)) lam := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ j : ℤ,
                j ∈ Finset.singleton k ∧
                  n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (j : ℝ)) lam :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
              φ).mp hn
          match hmem with
          | ⟨j, hj, hn_window⟩ =>
              have hj_eq : j = k :=
                Finset.mem_singleton.mp hj
              Eq.subst
                (motive := fun q : ℤ =>
                  n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (q : ℝ)) lam)
                hj_eq
                hn_window)
        (fun hn =>
          (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
            φ).mpr
            (Exists.intro k
              (And.intro (Finset.mem_singleton_self k) hn))))

/-- The singleton resonance-family complement is the complement of the
corresponding single resonance window. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyComplement_singleton
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (k : ℤ) :
    Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam (Finset.singleton k) =
      Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b (2 * Real.pi * (k : ℝ)) lam := by
  have hunion :
      Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam (Finset.singleton k) =
        Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_singleton
      φ a b lam k
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_data :
              n ∈ Finset.Ico a b ∧
                n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam (Finset.singleton k) :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
              φ).mp hn
          have hn_not_window :
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam := by
            intro hn_window
            have hn_union :
                n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam (Finset.singleton k) :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hunion.symm
                hn_window
            exact hn_data.2 hn_union
          (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
            (φ := φ)
            (a := a)
            (b := b)
            (n := n)
            (resonance := 2 * Real.pi * (k : ℝ))
            (lam := lam)).mpr
            (And.intro hn_data.1
              (fun hres =>
                hn_not_window
                  ((Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                    (φ := φ)
                    (a := a)
                    (b := b)
                    (n := n)
                    (resonance := 2 * Real.pi * (k : ℝ))
                    (lam := lam)).mpr
                    (And.intro hn_data.1 hres)))))
        (fun hn =>
          have hn_data :
              n ∈ Finset.Ico a b ∧
                ¬ ‖Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ))‖ < lam :=
            (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
              (φ := φ)
              (a := a)
              (b := b)
              (n := n)
              (resonance := 2 * Real.pi * (k : ℝ))
              (lam := lam)).mp hn
          have hn_not_union :
              n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                φ a b lam (Finset.singleton k) := by
            intro hn_union
            have hn_window :
                n ∈ Complex.realPhase_integerIncrementResonanceWindow
                  φ a b (2 * Real.pi * (k : ℝ)) lam :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hunion
                hn_union
            have hn_window_data :
                n ∈ Finset.Ico a b ∧
                  ‖Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ))‖ < lam :=
              (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                (φ := φ)
                (a := a)
                (b := b)
                (n := n)
                (resonance := 2 * Real.pi * (k : ℝ))
                (lam := lam)).mp hn_window
            exact hn_data.2 hn_window_data.2
          (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
            φ).mpr
            (And.intro hn_data.1 hn_not_union)))

/-- Two-gap norm bound for the complement of a singleton integer-centered
resonance family. -/
theorem Complex.realPhase_singletonResonanceFamilyComplement_sum_norm_le_two_mul_of_window_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam B : ℝ}
    (k : ℤ)
    (F : ℕ → ℂ)
    (hB : 0 ≤ B)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam =
        Finset.Ico c d)
    (hgap :
      ∀ p : ℕ × ℕ,
        p ∈ Nat.IcoTwoGapComplement a b c d →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤ B) :
    ‖∑ n ∈
      Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam (Finset.singleton k), F n‖ ≤
      2 * B := by
  have hsingle :
      Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam (Finset.singleton k) =
        Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
    Complex.realPhase_integerIncrementResonanceFamilyComplement_singleton
      φ a b lam k
  have hwindow_complement :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b (2 * Real.pi * (k : ℝ)) lam, F n‖ ≤
        2 * B :=
    Complex.realPhase_resonanceWindowComplement_sum_norm_le_two_mul_of_window_eq_Ico
      φ F hB hac hcd hdb hwindow hgap
  exact
    Eq.subst
      (motive := fun S : Finset ℕ =>
        ‖∑ n ∈ S, F n‖ ≤ 2 * B)
      hsingle.symm
      hwindow_complement

/-- Inserting one integer center into a resonance family adds exactly the
corresponding resonance window to the family union. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_insert
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (k : ℤ)
    (K : Finset ℤ) :
    Complex.realPhase_integerIncrementResonanceFamilyUnion
        φ a b lam (insert k K) =
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam ∪
        Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hmem :
              ∃ j : ℤ,
                j ∈ insert k K ∧
                  n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (j : ℝ)) lam :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
              φ).mp hn
          match hmem with
          | ⟨j, hj, hn_window⟩ =>
              have hj_cases : j = k ∨ j ∈ K :=
                Finset.mem_insert.mp hj
              match hj_cases with
              | Or.inl hj_eq =>
                  have hn_k :
                      n ∈ Complex.realPhase_integerIncrementResonanceWindow
                        φ a b (2 * Real.pi * (k : ℝ)) lam :=
                    Eq.subst
                      (motive := fun q : ℤ =>
                        n ∈ Complex.realPhase_integerIncrementResonanceWindow
                          φ a b (2 * Real.pi * (q : ℝ)) lam)
                      hj_eq
                      hn_window
                  Finset.mem_union.mpr (Or.inl hn_k)
              | Or.inr hj_K =>
                  have hn_K :
                      n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                        φ a b lam K :=
                    (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
                      φ).mpr
                      (Exists.intro j (And.intro hj_K hn_window))
                  Finset.mem_union.mpr (Or.inr hn_K))
        (fun hn =>
          have hn_cases :
              n ∈ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (k : ℝ)) lam ∨
                n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                    φ a b lam K :=
            Finset.mem_union.mp hn
          match hn_cases with
          | Or.inl hn_k =>
              (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
                φ).mpr
                (Exists.intro k
                  (And.intro (Finset.mem_insert_self k K) hn_k))
          | Or.inr hn_K =>
              have hmem_K :
                  ∃ j : ℤ,
                    j ∈ K ∧
                      n ∈ Complex.realPhase_integerIncrementResonanceWindow
                        φ a b (2 * Real.pi * (j : ℝ)) lam :=
                (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
                  φ).mp hn_K
              match hmem_K with
              | ⟨j, hj, hn_window⟩ =>
                  (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
                    φ).mpr
                    (Exists.intro j
                      (And.intro (Finset.mem_insert_of_mem hj) hn_window))))

/-- Inserting one integer center into a resonance family filters the previous
family complement by avoidance of the newly inserted window. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyComplement_insert
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (k : ℤ)
    (K : Finset ℤ) :
    Complex.realPhase_integerIncrementResonanceFamilyComplement
        φ a b lam (insert k K) =
      (Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam K).filter
        (fun n : ℕ =>
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam) := by
  have hunion :
      Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam (insert k K) =
        Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam ∪
          Complex.realPhase_integerIncrementResonanceFamilyUnion
            φ a b lam K :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_insert
      φ a b lam k K
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_data :
              n ∈ Finset.Ico a b ∧
                n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam (insert k K) :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
              φ).mp hn
          have hn_not_window :
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam := by
            intro hn_window
            have hn_union_insert :
                n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam (insert k K) :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hunion.symm
                (Finset.mem_union.mpr (Or.inl hn_window))
            exact hn_data.2 hn_union_insert
          have hn_not_K :
              n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                φ a b lam K := by
            intro hn_K
            have hn_union_insert :
                n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam (insert k K) :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hunion.symm
                (Finset.mem_union.mpr (Or.inr hn_K))
            exact hn_data.2 hn_union_insert
          have hn_complement_K :
              n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
                φ a b lam K :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
              φ).mpr
              (And.intro hn_data.1 hn_not_K)
          Finset.mem_filter.mpr
            (And.intro hn_complement_K hn_not_window))
        (fun hn =>
          have hn_filter :
              n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
                    φ a b lam K ∧
                n ∉ Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (k : ℝ)) lam :=
            Finset.mem_filter.mp hn
          have hn_K_data :
              n ∈ Finset.Ico a b ∧
                n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                  φ a b lam K :=
            (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
              φ).mp hn_filter.1
          have hn_not_insert :
              n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
                φ a b lam (insert k K) := by
            intro hn_insert
            have hn_union :
                n ∈
                  Complex.realPhase_integerIncrementResonanceWindow
                      φ a b (2 * Real.pi * (k : ℝ)) lam ∪
                    Complex.realPhase_integerIncrementResonanceFamilyUnion
                      φ a b lam K :=
              Eq.subst
                (motive := fun S : Finset ℕ => n ∈ S)
                hunion
                hn_insert
            have hn_cases :
                n ∈ Complex.realPhase_integerIncrementResonanceWindow
                      φ a b (2 * Real.pi * (k : ℝ)) lam ∨
                  n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
                      φ a b lam K :=
              Finset.mem_union.mp hn_union
            match hn_cases with
            | Or.inl hn_window =>
                exact hn_filter.2 hn_window
            | Or.inr hn_K =>
                exact hn_K_data.2 hn_K
          (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
            φ).mpr
            (And.intro hn_K_data.1 hn_not_insert)))

/-- A thin finite family of integer-centered resonance windows has a
disjoint interval-connected gap cover of its complement with at most one more
gap than the number of centers. -/
theorem Complex.exists_IcoFamily_connected_cover_resonanceFamilyComplement_of_window_eq_of_le_pi
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (hlam : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        gaps.card ≤ K.card + 1 := by
  have hind :
      (∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d) →
        ∃ gaps : Finset (ℕ × ℕ),
          Complex.realPhase_IcoFamilyUnion gaps =
              Complex.realPhase_integerIncrementResonanceFamilyComplement
                φ a b lam K ∧
            (∀ p₁ : ℕ × ℕ,
              p₁ ∈ gaps →
                ∀ p₂ : ℕ × ℕ,
                  p₂ ∈ gaps →
                    p₁ ≠ p₂ →
                      Disjoint (Finset.Ico p₁.1 p₁.2)
                        (Finset.Ico p₂.1 p₂.2)) ∧
            Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
            gaps.card ≤ K.card + 1 :=
    Finset.induction_on K
    (fun _hwindow_empty => by
      let gaps : Finset (ℕ × ℕ) := Finset.singleton (a, b)
      have hcover_Ico :
          Complex.realPhase_IcoFamilyUnion gaps = Finset.Ico a b :=
        Complex.realPhase_IcoFamilyUnion_singleton a b
      have hcomplement_empty :
          Complex.realPhase_integerIncrementResonanceFamilyComplement
              φ a b lam (∅ : Finset ℤ) =
            Finset.Ico a b :=
        Complex.realPhase_integerIncrementResonanceFamilyComplement_empty
          φ a b lam
      have hcover :
          Complex.realPhase_IcoFamilyUnion gaps =
            Complex.realPhase_integerIncrementResonanceFamilyComplement
              φ a b lam (∅ : Finset ℤ) :=
        Eq.trans hcover_Ico hcomplement_empty.symm
      have hdisjoint :
          ∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2) := by
        intro p₁ hp₁ p₂ hp₂ hpne
        have hp₁_eq : p₁ = (a, b) :=
          Finset.mem_singleton.mp hp₁
        have hp₂_eq : p₂ = (a, b) :=
          Finset.mem_singleton.mp hp₂
        have hp_eq : p₁ = p₂ :=
          Eq.trans hp₁_eq hp₂_eq.symm
        exact False.elim (hpne hp_eq)
      have hconnected :
          Complex.realPhase_IcoFamilyIntervalConnected gaps :=
        Complex.realPhase_IcoFamilyIntervalConnected_singleton a b
      have hcard_one : gaps.card = 1 :=
        Finset.card_singleton (a, b)
      have hcard : gaps.card ≤ (∅ : Finset ℤ).card + 1 := by
        have hzero_add : (∅ : Finset ℤ).card + 1 = 1 :=
          congrArg (fun n : ℕ => n + 1) Finset.card_empty
        exact
          Eq.subst
            (motive := fun right : ℕ => gaps.card ≤ right)
            hzero_add.symm
            (le_of_eq hcard_one)
      exact Exists.intro gaps
        (And.intro hcover
          (And.intro hdisjoint
            (And.intro hconnected hcard))))
    (fun k K hk_not ih hwindow_insert => by
      have hwindow_old :
          ∀ j : ℤ,
            j ∈ K →
              ∃ c d : ℕ,
                Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (j : ℝ)) lam =
                  Finset.Ico c d := by
        intro j hj
        exact hwindow_insert j (Finset.mem_insert_of_mem hj)
      have ih_data :
          ∃ gaps : Finset (ℕ × ℕ),
            Complex.realPhase_IcoFamilyUnion gaps =
                Complex.realPhase_integerIncrementResonanceFamilyComplement
                  φ a b lam K ∧
              (∀ p₁ : ℕ × ℕ,
                p₁ ∈ gaps →
                  ∀ p₂ : ℕ × ℕ,
                    p₂ ∈ gaps →
                      p₁ ≠ p₂ →
                        Disjoint (Finset.Ico p₁.1 p₁.2)
                          (Finset.Ico p₂.1 p₂.2)) ∧
              Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
              gaps.card ≤ K.card + 1 :=
        ih hwindow_old
      match ih_data with
      | ⟨gaps, hcover, hdisjoint, hconnected, hcard⟩ =>
          have hk_mem_insert : k ∈ insert k K :=
            Finset.mem_insert_self k K
          have hwindow_k_exists :
              ∃ c d : ℕ,
                Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (k : ℝ)) lam =
                  Finset.Ico c d :=
            hwindow_insert k hk_mem_insert
          match hwindow_k_exists with
          | ⟨c, d, hwindow_k⟩ =>
              have hwindow_subset :
                  Finset.Ico c d ⊆
                    Complex.realPhase_integerIncrementResonanceFamilyComplement
                      φ a b lam K :=
                Complex.Ico_subset_resonanceFamilyComplement_of_window_eq_of_not_mem_of_le_pi
                  φ hlam hk_not hwindow_k
              have hstep :
                  ∃ newGaps : Finset (ℕ × ℕ),
                    Complex.realPhase_IcoFamilyUnion newGaps =
                        (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ => n ∉ Finset.Ico c d) ∧
                      (∀ p₁ : ℕ × ℕ,
                        p₁ ∈ newGaps →
                          ∀ p₂ : ℕ × ℕ,
                            p₂ ∈ newGaps →
                              p₁ ≠ p₂ →
                                Disjoint (Finset.Ico p₁.1 p₁.2)
                                  (Finset.Ico p₂.1 p₂.2)) ∧
                      Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
                      newGaps.card ≤ (K.card + 1) + 1 :=
                Complex.exists_IcoFamily_connected_cover_filter_not_Ico_step_budget
                  hcover hdisjoint hconnected hcard hwindow_subset
              match hstep with
              | ⟨newGaps, hcover_step, hdisjoint_new,
                  hconnected_new, hcard_step⟩ =>
                  have hfilter_window :
                      (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ => n ∉ Finset.Ico c d) =
                        (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ =>
                            n ∉
                              Complex.realPhase_integerIncrementResonanceWindow
                                φ a b (2 * Real.pi * (k : ℝ)) lam) := by
                    exact Finset.ext
                      (fun n =>
                        Iff.intro
                          (fun hn =>
                            have hdata :
                                n ∈
                                    Complex.realPhase_integerIncrementResonanceFamilyComplement
                                      φ a b lam K ∧
                                  n ∉ Finset.Ico c d :=
                              Finset.mem_filter.mp hn
                            have hn_not_window :
                                n ∉
                                  Complex.realPhase_integerIncrementResonanceWindow
                                    φ a b (2 * Real.pi * (k : ℝ)) lam := by
                              intro hn_window
                              have hn_Ico : n ∈ Finset.Ico c d :=
                                Eq.subst
                                  (motive := fun S : Finset ℕ => n ∈ S)
                                  hwindow_k
                                  hn_window
                              exact hdata.2 hn_Ico
                            Finset.mem_filter.mpr
                              (And.intro hdata.1 hn_not_window))
                          (fun hn =>
                            have hdata :
                                n ∈
                                    Complex.realPhase_integerIncrementResonanceFamilyComplement
                                      φ a b lam K ∧
                                  n ∉
                                    Complex.realPhase_integerIncrementResonanceWindow
                                      φ a b (2 * Real.pi * (k : ℝ)) lam :=
                              Finset.mem_filter.mp hn
                            have hn_not_Ico : n ∉ Finset.Ico c d := by
                              intro hn_Ico
                              have hn_window :
                                  n ∈
                                    Complex.realPhase_integerIncrementResonanceWindow
                                      φ a b (2 * Real.pi * (k : ℝ)) lam :=
                                Eq.subst
                                  (motive := fun S : Finset ℕ => n ∈ S)
                                  hwindow_k.symm
                                  hn_Ico
                              exact hdata.2 hn_window
                            Finset.mem_filter.mpr
                              (And.intro hdata.1 hn_not_Ico)))
                  have hinsert_complement :
                      Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam (insert k K) =
                        (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ =>
                            n ∉
                              Complex.realPhase_integerIncrementResonanceWindow
                                φ a b (2 * Real.pi * (k : ℝ)) lam) :=
                    Complex.realPhase_integerIncrementResonanceFamilyComplement_insert
                      φ a b lam k K
                  have hcover_new :
                      Complex.realPhase_IcoFamilyUnion newGaps =
                        Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam (insert k K) :=
                    Eq.trans hcover_step
                      (Eq.trans hfilter_window hinsert_complement.symm)
                  have hinsert_card :
                      (insert k K).card = K.card + 1 :=
                    Finset.card_insert_of_not_mem hk_not
                  have hcard_new :
                      newGaps.card ≤ (insert k K).card + 1 :=
                    Eq.subst
                      (motive := fun m : ℕ => newGaps.card ≤ m + 1)
                      hinsert_card.symm
                      hcard_step
                  exact Exists.intro newGaps
                    (And.intro hcover_new
                      (And.intro hdisjoint_new
                        (And.intro hconnected_new hcard_new))))
  exact hind hwindow

/-- The finite resonance-family union has cardinality bounded by the sum of
the cardinalities of its integer-centered windows.  No disjointness of the
windows is required. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_card_le_sum_window_cards
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) :
    (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K).card ≤
      ∑ k ∈ K,
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card := by
  exact Finset.card_biUnion_le

/-- Real cardinality form of the finite resonance-family union bound. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_card_real_le_sum_window_cards
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) :
    ((Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K).card :
        ℝ) ≤
      ((∑ k ∈ K,
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℕ) : ℝ) := by
  exact
    Nat.cast_le.mpr
      (Complex.realPhase_integerIncrementResonanceFamilyUnion_card_le_sum_window_cards
        φ a b lam K)

/-- The resonant-family exponential sum is bounded by the total cardinality
of the integer-centered resonance windows. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_sum_window_cards
    (φ ψ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ) :
    ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
      ((∑ k ∈ K,
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℕ) : ℝ) := by
  have hunit :
      ∀ n : ℕ,
        n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K →
          ‖Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ 1 := by
    intro n _hn
    exact le_of_eq (Complex.realPhase_exp_I_norm ψ n)
  have hcard_bound :
      ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
          Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
        ((Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K).card : ℝ) :=
    Complex.finite_sum_norm_le_card_of_norm_le_one
      (Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K)
      (fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ)))
      hunit
  exact
    le_trans hcard_bound
      (Complex.realPhase_integerIncrementResonanceFamilyUnion_card_real_le_sum_window_cards
        φ a b lam K)

/-- The resonant-family exponential sum is bounded by a uniform window-length
budget times the number of active integer centers. -/
theorem Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_card_mul_window_bound
    (φ ψ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    {W : ℝ}
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          ((Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W) :
    ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
      ((K.card : ℝ) * W) := by
  have hsum_cards :
      ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
          Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
        ((∑ k ∈ K,
          (Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℕ) : ℝ) :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_sum_window_cards
      φ ψ a b lam K
  have hcast_sum :
      ((∑ k ∈ K,
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℕ) : ℝ) =
        ∑ k ∈ K,
          ((Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℝ) :=
    Nat.cast_sum K
      (fun k : ℤ =>
        (Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam).card)
  have hsum_bound :
      (∑ k ∈ K,
          ((Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℝ)) ≤
        ∑ k ∈ K, W :=
    Finset.sum_le_sum hwindow
  have hconst :
      (∑ k ∈ K, W) = ((K.card : ℝ) * W) :=
    Eq.trans
      (Finset.sum_const W)
      (nsmul_eq_mul K.card W)
  exact
    le_trans hsum_cards
      (le_trans
        (Eq.subst
          (motive := fun r : ℝ =>
            r ≤ ∑ k ∈ K, W)
          hcast_sum.symm
          hsum_bound)
        (le_of_eq hconst))

/-- The range-active resonant union is bounded by a uniform window-length
budget times the cardinality of the single padded range of integer centers. -/
theorem Complex.realPhase_integerIncrementRangeActiveCentersUnion_sum_norm_le_card_mul_window_bound
    (φ ψ : ℝ → ℝ)
    (a b : ℕ)
    {lo hi lam W : ℝ}
    (hwindow :
      ∀ k : ℤ,
        k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W) :
    ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam
          (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam),
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
      (((Complex.realPhase_integerIncrementRangeActiveCenters
        lo hi lam).card : ℝ) * W) := by
  exact
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_card_mul_window_bound
      φ ψ a b lam
      (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam)
      hwindow

/-- If the resonant-family union and its complement have been bounded, then
the whole half-open block sum is bounded by the sum of those two bounds. -/
theorem Complex.realPhase_integerIncrementResonanceFamily_Ico_sum_norm_le_of_union_complement_bounds
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (F : ℕ → ℂ)
    {R G M : ℝ}
    (hunion :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
          F n‖ ≤ R)
    (hgap :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K,
          F n‖ ≤ G)
    (hmajor : R + G ≤ M) :
    ‖∑ n ∈ Finset.Ico a b, F n‖ ≤ M := by
  have hsplit :
      ‖∑ n ∈ Finset.Ico a b, F n‖ ≤
        ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
            F n‖ +
          ‖∑ n ∈
            Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K,
              F n‖ :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le
      φ a b lam K F
  have hparts :
      ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
            F n‖ +
        ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K,
            F n‖ ≤
        R + G :=
    add_le_add hunion hgap
  exact le_trans (le_trans hsplit hparts) hmajor

/-- Exponential-sum specialization of the finite all-integer resonance-family
block estimate. -/
theorem Complex.realPhase_integerIncrementResonanceFamily_exp_Ico_sum_norm_le_of_union_complement_bounds
    (φ ψ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    {R G M : ℝ}
    (hunion :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion φ a b lam K,
          Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ R)
    (hgap :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyComplement φ a b lam K,
          Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ G)
    (hmajor : R + G ≤ M) :
    ‖∑ n ∈ Finset.Ico a b,
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ M :=
  Complex.realPhase_integerIncrementResonanceFamily_Ico_sum_norm_le_of_union_complement_bounds
    φ a b lam K
    (fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ)))
    hunion hgap hmajor

/-- Shifted-logarithmic specialization of the all-integer resonance-family
half-open block estimate. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_resonanceFamily_bounds
    (t : ℝ)
    {a b h : ℕ}
    (lam : ℝ)
    (K : Finset ℤ)
    {R G M : ℝ}
    (hunion :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyUnion
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) lam K,
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ ≤ R)
    (hgap :
      ‖∑ n ∈
        Complex.realPhase_integerIncrementResonanceFamilyComplement
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) lam K,
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ ≤ G)
    (hmajor : R + G ≤ M) :
    ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤ M :=
  Complex.realPhase_integerIncrementResonanceFamily_exp_Ico_sum_norm_le_of_union_complement_bounds
    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h)
    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h)
    a (b - h) lam K hunion hgap hmajor

/-- Shifted-logarithmic active-center family for one Weyl shifted-difference
phase. -/
def Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
    (t : ℝ)
    (a b h : ℕ)
    (lam : ℝ) : Finset ℤ :=
  Complex.realPhase_integerIncrementActiveCenters
    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h)
    a (b - h) lam

/-- Shifted-logarithmic active-center resonance union for one Weyl
shifted-difference phase. -/
def Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
    (t : ℝ)
    (a b h : ℕ)
    (lam : ℝ) : Finset ℕ :=
  Complex.realPhase_integerIncrementResonanceFamilyUnion
    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h)
    a (b - h) lam
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
      t a b h lam)

/-- Shifted-logarithmic active-center resonance complement for one Weyl
shifted-difference phase. -/
def Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
    (t : ℝ)
    (a b h : ℕ)
    (lam : ℝ) : Finset ℕ :=
  Complex.realPhase_integerIncrementResonanceFamilyComplement
    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h)
    a (b - h) lam
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
      t a b h lam)

/-- Shifted-logarithmic active centers are bounded by any a priori range of
shifted adjacent increments. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
    (t : ℝ)
    {a b h : ℕ}
    {lo hi lam : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card ≤
      (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam).card := by
  exact
    Complex.realPhase_integerIncrementActiveCenters_card_le_rangeActiveCenters_card
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hrange

/-- The active-center complement of a shifted logarithmic difference is
separated from every integer lattice frequency. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_separated
    (t : ℝ)
    {a b h n : ℕ}
    {lam : ℝ}
    (hn :
      n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (k : ℤ) :
    lam ≤
      ‖Complex.realPhase_integerIncrement
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          n -
        (2 * Real.pi * (k : ℝ))‖ := by
  exact
    Complex.realPhase_integerIncrementActiveCentersComplement_separated_from_any_center
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hn
      k

/-- Any interval contained in the active-center complement of a shifted
logarithmic difference has separated integer increments. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_Ico_separated
    (t : ℝ)
    {a b h c d : ℕ}
    {lam : ℝ}
    (hgap_subset :
      Finset.Ico c d ⊆
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      c d lam := by
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_activeCentersFamilyComplement
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hgap_subset

/-- Active-center specialization of the shifted-logarithmic all-integer
resonance-family split. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
    (t : ℝ)
    {a b h : ℕ}
    (lam : ℝ)
    {R G M : ℝ}
    (hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h lam,
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ ≤ R)
    (hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam,
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ ≤ G)
    (hmajor : R + G ≤ M) :
    ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤ M := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_resonanceFamily_bounds
      t lam
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam)
      hunion hgap hmajor

/-- The shifted-logarithmic active resonant union is bounded by a uniform
window-length budget times the number of active centers. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
    (t : ℝ)
    {a b h : ℕ}
    {lam W : ℝ}
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W) :
    ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) := by
  exact
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_card_mul_window_bound
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      a (b - h) lam
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam)
      hwindow

/-- A closed natural interval exponential sum is controlled by the half-open
interval sum plus the terminal unit-modulus sample. -/
theorem Complex.realPhase_Icc_sum_norm_le_Ico_sum_norm_add_one
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      ‖∑ n ∈ Finset.Ico a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ + 1 := by
  have hnot_mem : b ∉ Finset.Ico a b := by
    intro hb_mem
    have hb_bounds : a ≤ b ∧ b < b :=
      Finset.mem_Ico.mp hb_mem
    exact not_lt_of_ge (Nat.le_refl b) hb_bounds.2
  have hinsert :
      insert b (Finset.Ico a b) = Finset.Icc a b :=
    Finset.Ico_insert_right hab
  have hsum_insert :
      (∑ n ∈ insert b (Finset.Ico a b),
        Complex.exp (Complex.I * (φ n : ℂ))) =
        Complex.exp (Complex.I * (φ b : ℂ)) +
          ∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
    Finset.sum_insert hnot_mem
  have hsum_Icc :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        Complex.exp (Complex.I * (φ b : ℂ)) +
          ∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ)) := by
    exact
      Eq.trans
        (congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
          hinsert.symm)
        hsum_insert
  have htriangle :
      ‖Complex.exp (Complex.I * (φ b : ℂ)) +
          ∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ‖Complex.exp (Complex.I * (φ b : ℂ))‖ +
          ‖∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    norm_add_le
      (Complex.exp (Complex.I * (φ b : ℂ)))
      (∑ n ∈ Finset.Ico a b,
        Complex.exp (Complex.I * (φ n : ℂ)))
  have hunit :
      ‖Complex.exp (Complex.I * (φ b : ℂ))‖ = 1 :=
    Complex.realPhase_exp_I_norm φ b
  have hcomm :
      ‖Complex.exp (Complex.I * (φ b : ℂ))‖ +
          ‖∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ))‖ =
        ‖∑ n ∈ Finset.Ico a b,
          Complex.exp (Complex.I * (φ n : ℂ))‖ + 1 := by
    exact
      Eq.trans
        (congrArg
          (fun r : ℝ =>
            r +
              ‖∑ n ∈ Finset.Ico a b,
                Complex.exp (Complex.I * (φ n : ℂ))‖)
          hunit)
        (add_comm 1
          ‖∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ))‖)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ n ∈ Finset.Ico a b,
            Complex.exp (Complex.I * (φ n : ℂ))‖ + 1)
      hsum_Icc.symm
      (le_trans htriangle
        (le_of_eq hcomm))

/-- A shifted logarithmic correlation is controlled by its half-open
increment-index part plus the terminal unit-modulus sample. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
    (t : ℝ)
    {a b h : ℕ}
    (habh : a ≤ b - h) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ + 1 := by
  exact
    Complex.realPhase_Icc_sum_norm_le_Ico_sum_norm_add_one
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      habh

/-- A half-open finite exponential sum is bounded by a terminal closed-interval
bound, with the empty interval handled only from nonnegativity of the target. -/
theorem Complex.realPhase_Ico_sum_norm_le_of_terminal_Icc_bounds
    (φ : ℝ → ℝ)
    {c d : ℕ}
    {M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (hIcc :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ‖∑ n ∈ Finset.Icc c r,
              Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ M) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ M := by
  match Nat.lt_or_ge c d with
  | Or.inl hcd_strict =>
      let r : ℕ := d - 1
      have hd_pos : 0 < d :=
        lt_of_le_of_lt (Nat.zero_le c) hcd_strict
      have hd_pred_succ : r + 1 = d :=
        Nat.succ_pred_eq_of_pos hd_pos
      have hIco_succ : Finset.Ico c (r + 1) = Finset.Icc c r :=
        Nat.Ico_succ_right c r
      have hIco_eq : Finset.Ico c d = Finset.Icc c r :=
        Eq.subst
          (motive := fun right : ℕ => Finset.Ico c right = Finset.Icc c r)
          hd_pred_succ
          hIco_succ
      have hcr : c ≤ r :=
        Nat.le_pred_of_lt hcd_strict
      have hclosed :
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ M :=
        hIcc hcr hd_pred_succ
      exact
        Eq.subst
          (motive := fun S : Finset ℕ =>
            ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ M)
          hIco_eq.symm
          hclosed
  | Or.inr hdc =>
      have hIco_empty : Finset.Ico c d = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : c ≤ n ∧ n < d :=
              Finset.mem_Ico.mp hn
            have hd_le_n : d ≤ n :=
              Nat.le_trans hdc hn_bounds.1
            not_lt_of_ge hd_le_n hn_bounds.2)
      have hsum_zero :
          (∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (φ n : ℂ))) = 0 :=
        Eq.trans
          (congrArg
            (fun S : Finset ℕ =>
              ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
            hIco_empty)
          Finset.sum_empty
      have hzero_bound :
          ‖(0 : ℂ)‖ ≤ M :=
        Eq.subst
          (motive := fun left : ℝ => left ≤ M)
          (norm_zero : ‖(0 : ℂ)‖ = 0).symm
          hM_nonneg
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ M)
          hsum_zero.symm
          hzero_bound

/-- Shifted-logarithmic specialization of the terminal closed-interval
reduction for half-open sums. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_terminal_Icc_bounds
    (t : ℝ)
    {c d h : ℕ}
    {M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (hIcc :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ‖∑ n ∈ Finset.Icc c r,
              Complex.exp
                (Complex.I *
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h n : ℂ))‖ ≤ M) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤ M := by
  exact
    Complex.realPhase_Ico_sum_norm_le_of_terminal_Icc_bounds
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hM_nonneg
      hIcc

/-- The canonical resonant-index set for monotone adjacent increments is a
half-open resonant window. -/
theorem Complex.realPhase_integerIncrement_resonanceWindow_exists_canonical
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {resonance lam : ℝ}
    (hab : a ≤ b)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
        Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam = Finset.Ico c d := by
  exact
    Complex.realPhase_integerIncrement_resonanceWindow_exists
      φ hab
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam)
      (fun n =>
        Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          φ)
      hinc_mono

/-- A monotone-increment phase has a disjoint interval-connected gap cover for
the complement of any thin finite integer-centered resonance family. -/
theorem Complex.exists_IcoFamily_connected_cover_resonanceFamilyComplement_of_mono_of_le_pi
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (K : Finset ℤ)
    (hab : a ≤ b)
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hlam : lam ≤ Real.pi) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        gaps.card ≤ K.card + 1 := by
  have hwindow :
      ∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d := by
    intro k _hk
    have hcanonical :
        ∃ c d : ℕ,
          a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
            Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
                Finset.Ico c d :=
      Complex.realPhase_integerIncrement_resonanceWindow_exists_canonical
        φ hab hmono
    match hcanonical with
    | ⟨c, d, _hac, _hcd, _hdb, hwindow_eq⟩ =>
        exact Exists.intro c (Exists.intro d hwindow_eq)
  exact
    Complex.exists_IcoFamily_connected_cover_resonanceFamilyComplement_of_window_eq_of_le_pi
      φ a b lam K hlam hwindow

/-- Shifted-logarithmic active-center complements have disjoint
interval-connected gap covers with at most one more gap than the number of
active integer centers. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_IcoFamily_cover_of_mono_of_le_pi
    (t : ℝ)
    {a b h : ℕ}
    {lam : ℝ}
    (habh : a ≤ b - h)
    (hmono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hlam : lam ≤ Real.pi) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h lam ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        gaps.card ≤
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam).card + 1 := by
  exact
    Complex.exists_IcoFamily_connected_cover_resonanceFamilyComplement_of_mono_of_le_pi
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam)
      habh hmono hlam


/-- Cardinality of a canonical resonant window after its half-open interval
endpoints have been identified. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_card_eq_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    (Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam).card =
      d - c := by
  exact
    Eq.trans
      (congrArg Finset.card hwindow)
      (Nat.card_Ico c d)

/-- Real cardinality of a canonical resonant window after its half-open
interval endpoints have been identified. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_card_real_eq_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    ((Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam).card : ℝ) =
      ((d - c : ℕ) : ℝ) := by
  exact
    congrArg
      (fun n : ℕ => (n : ℝ))
      (Complex.realPhase_integerIncrementResonanceWindow_card_eq_of_eq_Ico
        φ hwindow)

/-- A zero-centered resonance window has length at most two once any two-step
subinterval in the window has spread at least twice the window radius. -/
theorem Real.resonanceWindow_Ico_length_le_two_of_two_step_spread
    {f : ℕ → ℝ}
    {c d : ℕ}
    {center lam : ℝ}
    (hwindow :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          ‖f n - center‖ < lam)
    (hspread :
      c + 2 < d →
        2 * lam ≤ ‖f (c + 2) - f c‖) :
    ((d - c : ℕ) : ℝ) ≤ 2 := by
  have hnot_three : ¬ c + 2 < d := by
    intro hc2_lt_d
    have hc_mem : c ∈ Finset.Ico c d :=
      Finset.mem_Ico.mpr
        (And.intro (le_refl c)
          (lt_of_le_of_lt (Nat.le_add_right c 2) hc2_lt_d))
    have hc2_mem : c + 2 ∈ Finset.Ico c d :=
      Finset.mem_Ico.mpr
        (And.intro (Nat.le_add_right c 2) hc2_lt_d)
    have hc_window :
        ‖f c - center‖ < lam :=
      hwindow c hc_mem
    have hc2_window :
        ‖f (c + 2) - center‖ < lam :=
      hwindow (c + 2) hc2_mem
    have htri_raw :
        ‖f (c + 2) - f c‖ ≤
          ‖f (c + 2) - center‖ + ‖center - f c‖ :=
      abs_sub_le (f (c + 2)) center (f c)
    have htri :
        ‖f (c + 2) - f c‖ ≤
          ‖f (c + 2) - center‖ + ‖f c - center‖ :=
      Eq.subst
        (motive := fun right : ℝ =>
          ‖f (c + 2) - f c‖ ≤
            ‖f (c + 2) - center‖ + right)
        (abs_sub_comm center (f c))
        htri_raw
    have hsum_lt :
        ‖f (c + 2) - center‖ + ‖f c - center‖ < lam + lam :=
      add_lt_add hc2_window hc_window
    have hdiam_lt_add :
        ‖f (c + 2) - f c‖ < lam + lam :=
      lt_of_le_of_lt htri hsum_lt
    have hdiam_lt_two :
        ‖f (c + 2) - f c‖ < 2 * lam :=
      Eq.subst
        (motive := fun right : ℝ =>
          ‖f (c + 2) - f c‖ < right)
        (two_mul lam).symm
        hdiam_lt_add
    exact not_lt_of_ge (hspread hc2_lt_d) hdiam_lt_two
  have hd_le_c_two : d ≤ c + 2 :=
    Nat.le_of_not_lt hnot_three
  have hd_le_two_c : d ≤ 2 + c :=
    Eq.subst
      (motive := fun right : ℕ => d ≤ right)
      (Nat.add_comm c 2)
      hd_le_c_two
  have hlen_nat : d - c ≤ 2 :=
    Nat.sub_le_iff_le_add.mpr hd_le_two_c
  exact Nat.cast_le.mpr hlen_nat

/-- A half-open interval has real length at most one plus the real length
from its left endpoint to its last integer point. -/
theorem Nat.Ico_length_cast_le_pred_sub_cast_add_one
    {c d : ℕ}
    (hcd : c < d) :
    ((d - c : ℕ) : ℝ) ≤ (((d - 1) - c : ℕ) : ℝ) + 1 := by
  let r : ℕ := d - 1
  have hd_pos : 0 < d :=
    lt_of_le_of_lt (Nat.zero_le c) hcd
  have hr_succ : r + 1 = d :=
    Nat.succ_pred_eq_of_pos hd_pos
  have hc_le_r : c ≤ r :=
    Nat.le_pred_of_lt hcd
  have hlength_eq :
      d - c = (r - c) + 1 := by
    have hsucc_sub :
        (r + 1) - c = (r - c) + 1 :=
      Nat.succ_sub hc_le_r
    exact
      Eq.trans
        (congrArg (fun n : ℕ => n - c) hr_succ.symm)
        hsucc_sub
  have hcast_length :
      ((d - c : ℕ) : ℝ) = (((r - c) + 1 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hlength_eq
  have hcast_succ :
      (((r - c) + 1 : ℕ) : ℝ) =
        ((r - c : ℕ) : ℝ) + 1 :=
    Eq.trans
      (Nat.cast_add (r - c) 1)
      (congrArg (fun x : ℝ => ((r - c : ℕ) : ℝ) + x) Nat.cast_one)
  have htarget_eq :
      ((r - c : ℕ) : ℝ) + 1 =
        (((d - 1) - c : ℕ) : ℝ) + 1 := by
    exact Eq.refl ((((d - 1) - c : ℕ) : ℝ) + 1)
  have hlength_final :
      ((d - c : ℕ) : ℝ) =
        (((d - 1) - c : ℕ) : ℝ) + 1 :=
    Eq.trans hcast_length
      (Eq.trans hcast_succ htarget_eq)
  exact le_of_eq hlength_final

/-- If the last-point span of a nonempty half-open interval is controlled,
then the whole half-open length is controlled with one endpoint added. -/
theorem Nat.Ico_length_cast_le_one_add_of_pred_sub_cast_le
    {c d : ℕ}
    {M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (hpred :
      c < d →
        (((d - 1) - c : ℕ) : ℝ) ≤ M) :
    ((d - c : ℕ) : ℝ) ≤ M + 1 := by
  match lt_or_ge c d with
  | Or.inl hcd =>
      have hlength :
        ((d - c : ℕ) : ℝ) ≤
          (((d - 1) - c : ℕ) : ℝ) + 1 :=
        Nat.Ico_length_cast_le_pred_sub_cast_add_one hcd
      have htail :
        (((d - 1) - c : ℕ) : ℝ) + 1 ≤ M + 1 :=
        add_le_add_right (hpred hcd) 1
      exact le_trans hlength htail
  | Or.inr hdc =>
      have hdc_zero : d - c = 0 :=
        Nat.sub_eq_zero_of_le hdc
      have hcast_zero : ((d - c : ℕ) : ℝ) = 0 :=
        Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ)) hdc_zero)
          (Nat.cast_zero)
      have hright_nonneg : 0 ≤ M + 1 :=
        add_nonneg hM_nonneg zero_le_one
      exact
        Eq.subst
          (motive := fun left : ℝ => left ≤ M + 1)
          hcast_zero.symm
          hright_nonneg

/-- Endpoint spread controls a half-open resonance window once the interval
has been identified as `[c,d)`.  The lower-spread hypothesis is deliberately
parameterized by `rho`: the logarithmic owner supplies the correct curvature
scale, instead of using the false two-step shortcut. -/
theorem Real.resonanceWindow_Ico_length_le_one_add_two_mul_div_of_endpoint_spread
    {f : ℕ → ℝ}
    {c d : ℕ}
    {center lam rho : ℝ}
    (hlam_nonneg : 0 ≤ lam)
    (hrho_pos : 0 < rho)
    (hwindow :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          ‖f n - center‖ < lam)
    (hspread :
      c < d →
        rho * (((d - 1) - c : ℕ) : ℝ) ≤
          ‖f (d - 1) - f c‖) :
    ((d - c : ℕ) : ℝ) ≤ (2 * lam) / rho + 1 := by
  exact
    Nat.Ico_length_cast_le_one_add_of_pred_sub_cast_le
      (div_nonneg
        (mul_nonneg zero_le_two hlam_nonneg)
        (le_of_lt hrho_pos))
      (fun hcd => by
        have hd_pred_mem :
            d - 1 ∈ Finset.Ico c d := by
          have hc_le_pred : c ≤ d - 1 :=
            Nat.le_pred_of_lt hcd
          have hpred_lt : d - 1 < d :=
            Nat.sub_one_lt_of_lt hcd
          exact Finset.mem_Ico.mpr (And.intro hc_le_pred hpred_lt)
        have hc_mem :
            c ∈ Finset.Ico c d :=
          Finset.mem_Ico.mpr (And.intro (le_refl c) hcd)
        have hleft :
            ‖f c - center‖ < lam :=
          hwindow c hc_mem
        have hright :
            ‖f (d - 1) - center‖ < lam :=
          hwindow (d - 1) hd_pred_mem
        have htri_raw :
            ‖f (d - 1) - f c‖ ≤
              ‖f (d - 1) - center‖ + ‖center - f c‖ :=
          abs_sub_le (f (d - 1)) center (f c)
        have htri :
            ‖f (d - 1) - f c‖ ≤
              ‖f (d - 1) - center‖ + ‖f c - center‖ :=
          Eq.subst
            (motive := fun right : ℝ =>
              ‖f (d - 1) - f c‖ ≤
                ‖f (d - 1) - center‖ + right)
            (abs_sub_comm center (f c))
            htri_raw
        have hsum_lt :
            ‖f (d - 1) - center‖ + ‖f c - center‖ < lam + lam :=
          add_lt_add hright hleft
        have hdiam_lt_add :
            ‖f (d - 1) - f c‖ < lam + lam :=
          lt_of_le_of_lt htri hsum_lt
        have hdiam_lt_two :
            ‖f (d - 1) - f c‖ < 2 * lam :=
          Eq.subst
            (motive := fun right : ℝ =>
              ‖f (d - 1) - f c‖ < right)
            (two_mul lam).symm
            hdiam_lt_add
        have hscaled_lt :
            rho * (((d - 1) - c : ℕ) : ℝ) < 2 * lam :=
          lt_of_le_of_lt (hspread hcd) hdiam_lt_two
        have htail_lt :
            (((d - 1) - c : ℕ) : ℝ) < (2 * lam) / rho :=
          (lt_div_iff₀ hrho_pos).mpr
            (Eq.subst
              (motive := fun left : ℝ => left < 2 * lam)
              (mul_comm rho (((d - 1) - c : ℕ) : ℝ))
              hscaled_lt)
        exact le_of_lt htail_lt)

/-- Canonical adjacent-increment resonance-window length bound from endpoint
spread after the monotone-window construction has identified the window as a
half-open interval. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_Ico_length_le_one_add_two_mul_div_of_endpoint_spread
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam rho : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d)
    (hlam_nonneg : 0 ≤ lam)
    (hrho_pos : 0 < rho)
    (hspread :
      c < d →
        rho * (((d - 1) - c : ℕ) : ℝ) ≤
          ‖Complex.realPhase_integerIncrement φ (d - 1) -
            Complex.realPhase_integerIncrement φ c‖) :
    ((d - c : ℕ) : ℝ) ≤ (2 * lam) / rho + 1 := by
  exact
    Real.resonanceWindow_Ico_length_le_one_add_two_mul_div_of_endpoint_spread
      hlam_nonneg
      hrho_pos
      (fun n hn =>
        have hn_window :
            n ∈ Complex.realPhase_integerIncrementResonanceWindow
              φ a b resonance lam :=
          Eq.subst
            (motive := fun S : Finset ℕ => n ∈ S)
            hwindow.symm
            hn
        have hn_data :
            n ∈ Finset.Ico a b ∧
              ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam :=
          (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
            (φ := φ)
            (a := a)
            (b := b)
            (n := n)
            (resonance := resonance)
            (lam := lam)).mp hn_window
        hn_data.2)
      hspread

/-- Cardinal form of the endpoint-spread resonance-window estimate.  The
window interval is obtained from monotonicity, then the endpoint-spread length
bound is applied to those canonical endpoints. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_card_real_le_one_add_two_mul_div_of_endpoint_spread
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {resonance lam rho : ℝ}
    (hab : a ≤ b)
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hlam_nonneg : 0 ≤ lam)
    (hrho_pos : 0 < rho)
    (hspread :
      ∀ c d : ℕ,
        Complex.realPhase_integerIncrementResonanceWindow
            φ a b resonance lam =
          Finset.Ico c d →
        c < d →
          rho * (((d - 1) - c : ℕ) : ℝ) ≤
            ‖Complex.realPhase_integerIncrement φ (d - 1) -
              Complex.realPhase_integerIncrement φ c‖) :
    ((Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam).card : ℝ) ≤
      (2 * lam) / rho + 1 := by
  have hwindow_exists :
      ∃ c d : ℕ,
        a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
          Complex.realPhase_integerIncrementResonanceWindow
              φ a b resonance lam =
            Finset.Ico c d :=
    Complex.realPhase_integerIncrement_resonanceWindow_exists
      φ hab
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam)
      (fun n =>
        Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          (φ := φ)
          (a := a)
          (b := b)
          (n := n)
          (resonance := resonance)
          (lam := lam))
      hmono
  match hwindow_exists with
  | ⟨c, d, _hac, _hcd, _hdb, hwindow⟩ =>
      have hcard_eq :
          ((Complex.realPhase_integerIncrementResonanceWindow
              φ a b resonance lam).card : ℝ) =
            ((d - c : ℕ) : ℝ) :=
        Complex.realPhase_integerIncrementResonanceWindow_card_real_eq_of_eq_Ico
          φ hwindow
      have hlength :
          ((d - c : ℕ) : ℝ) ≤ (2 * lam) / rho + 1 :=
        Complex.realPhase_integerIncrementResonanceWindow_Ico_length_le_one_add_two_mul_div_of_endpoint_spread
          φ hwindow hlam_nonneg hrho_pos
          (hspread c d hwindow)
      exact
        Eq.subst
          (motive := fun left : ℝ => left ≤ (2 * lam) / rho + 1)
          hcard_eq.symm
          hlength

/-- Shifted-logarithmic resonance-window cardinality bound from a rational
endpoint-spread lower bound.  The rational lower bound is the remaining
arithmetic input supplied by the logarithmic-gap owner lemmas. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_card_real_le_one_add_two_mul_div_of_rational_endpoint_spread
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {resonance lam rho : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hmono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
        a (b - h))
    (hlam_nonneg : 0 ≤ lam)
    (hrho_pos : 0 < rho)
    (hrational :
      ∀ c d : ℕ,
        Complex.realPhase_integerIncrementResonanceWindow
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
            a (b - h) resonance lam =
          Finset.Ico c d →
        c < d - 1 →
          rho * (((d - 1) - c : ℕ) : ℝ) ≤
            ‖t‖ *
              (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                ((h : ℝ) /
                  (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ)))) :
    ((Complex.realPhase_integerIncrementResonanceWindow
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
        a (b - h) resonance lam).card : ℝ) ≤
      (2 * lam) / rho + 1 := by
  exact
    Complex.realPhase_integerIncrementResonanceWindow_card_real_le_one_add_two_mul_div_of_endpoint_spread
      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
      habh
      hmono
      hlam_nonneg
      hrho_pos
      (fun c d hwindow hcd => by
        have hc_mem :
            c ∈ Finset.Ico c d :=
          Finset.mem_Ico.mpr (And.intro (le_refl c) hcd)
        have hc_window :
            c ∈
              Complex.realPhase_integerIncrementResonanceWindow
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                a (b - h) resonance lam :=
          Eq.subst
            (motive := fun S : Finset ℕ => c ∈ S)
            hwindow.symm
            hc_mem
        have hc_data :
            c ∈ Finset.Ico a (b - h) ∧
              ‖Complex.realPhase_integerIncrement
                  (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                  c - resonance‖ < lam :=
          (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
            (φ := Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
            (a := a)
            (b := b - h)
            (n := c)
            (resonance := resonance)
            (lam := lam)).mp hc_window
        have hc_bounds : a ≤ c ∧ c < b - h :=
          Finset.mem_Ico.mp hc_data.1
        have hc_one : 1 ≤ c :=
          le_trans ha hc_bounds.1
        have hc_le_pred : c ≤ d - 1 :=
          Nat.le_pred_of_lt hcd
        match lt_or_eq_of_le hc_le_pred with
        | Or.inl hc_lt_pred =>
            have horiented :
                ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))) ≤
                  Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c -
                    Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                      (d - 1) :=
              Complex.logarithmicPhaseRealPhase_shiftedDifference_norm_rational_endpoint_spread_le_integerIncrement_spread
                t ht_nonneg hc_one hc_le_pred
            have hrat :
                rho * (((d - 1) - c : ℕ) : ℝ) ≤
                  ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))) :=
              hrational c d hwindow hc_lt_pred
            have hto_oriented :
                rho * (((d - 1) - c : ℕ) : ℝ) ≤
                  Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c -
                    Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                      (d - 1) :=
              le_trans hrat horiented
            have horiented_le_norm :
                Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c -
                  Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                    (d - 1) ≤
                ‖Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                    (d - 1) -
                  Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c‖ := by
              let delta : ℝ :=
                Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                    (d - 1) -
                  Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c
              have hneg :
                  Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c -
                    Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                      (d - 1) =
                    -delta := by
                exact (neg_sub
                  (Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                    (d - 1))
                  (Complex.realPhase_integerIncrement
                    (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c)).symm
              have hneg_le_norm_neg : -delta ≤ ‖-delta‖ :=
                Real.le_norm_self (-delta)
              have hnorm_neg : ‖-delta‖ = ‖delta‖ :=
                norm_neg delta
              have hneg_le_norm : -delta ≤ ‖delta‖ :=
                Eq.subst
                  (motive := fun right : ℝ => -delta ≤ right)
                  hnorm_neg
                  hneg_le_norm_neg
              exact
                Eq.subst
                  (motive := fun left : ℝ =>
                    left ≤ ‖delta‖)
                  hneg.symm
                  hneg_le_norm
            exact le_trans hto_oriented horiented_le_norm
        | Or.inr hc_eq_pred =>
            have hspan_zero : (d - 1) - c = 0 :=
              Nat.sub_eq_zero_of_le (le_of_eq hc_eq_pred.symm)
            have hleft_zero :
                rho * (((d - 1) - c : ℕ) : ℝ) = 0 := by
              have hcast_span_zero :
                  (((d - 1) - c : ℕ) : ℝ) = 0 :=
                Eq.trans
                  (congrArg (fun n : ℕ => (n : ℝ)) hspan_zero)
                  Nat.cast_zero
              exact
                Eq.trans
                  (congrArg (fun x : ℝ => rho * x)
                    hcast_span_zero)
                  (mul_zero rho)
            exact
              Eq.subst
                (motive := fun left : ℝ =>
                  left ≤
                    ‖Complex.realPhase_integerIncrement
                        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                        (d - 1) -
                      Complex.realPhase_integerIncrement
                        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c‖)
                hleft_zero.symm
                (norm_nonneg
                  (Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
                      (d - 1) -
                    Complex.realPhase_integerIncrement
                      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) c)))

/-- If the canonical resonance window is the half-open interval `[c,d)`,
then its nonresonant complement inside `[a,b)` is the union of the two
outside half-open intervals. -/
theorem Complex.realPhase_integerIncrementResonanceWindowComplement_eq_left_union_right_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    Complex.realPhase_integerIncrementResonanceWindowComplement
        φ a b resonance lam =
      Finset.Ico a c ∪ Finset.Ico d b := by
  exact
    Finset.ext
      (fun n =>
        Iff.intro
          (fun hn =>
            have hn_data :
                n ∈ Finset.Ico a b ∧
                  ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam :=
              (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
                (φ := φ)
                (a := a)
                (b := b)
                (n := n)
                (resonance := resonance)
                (lam := lam)).mp hn
            have hn_block_bounds : a ≤ n ∧ n < b :=
              Finset.mem_Ico.mp hn_data.1
            match lt_or_ge n c with
            | Or.inl hn_lt_c =>
                Finset.mem_union_left
                  (Finset.Ico d b)
                  (Finset.mem_Ico.mpr
                    (And.intro hn_block_bounds.1 hn_lt_c))
            | Or.inr hc_le_n =>
                have hd_le_n : d ≤ n := by
                  match lt_or_ge n d with
                  | Or.inl hn_lt_d =>
                      have hn_window_interval : n ∈ Finset.Ico c d :=
                        Finset.mem_Ico.mpr (And.intro hc_le_n hn_lt_d)
                      have hn_window :
                          n ∈
                            Complex.realPhase_integerIncrementResonanceWindow
                              φ a b resonance lam :=
                        Eq.subst
                          (motive := fun S : Finset ℕ => n ∈ S)
                          hwindow.symm
                          hn_window_interval
                      have hn_window_data :
                          n ∈ Finset.Ico a b ∧
                            ‖Complex.realPhase_integerIncrement φ n - resonance‖ <
                              lam :=
                        (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                          (φ := φ)
                          (a := a)
                          (b := b)
                          (n := n)
                          (resonance := resonance)
                          (lam := lam)).mp hn_window
                      exact False.elim (hn_data.2 hn_window_data.2)
                  | Or.inr hd_le_n => exact hd_le_n
                Finset.mem_union_right
                  (Finset.Ico a c)
                  (Finset.mem_Ico.mpr
                    (And.intro hd_le_n hn_block_bounds.2)))
          (fun hn_union =>
            match (Finset.mem_union.mp hn_union) with
            | Or.inl hn_left =>
                have hn_left_bounds : a ≤ n ∧ n < c :=
                  Finset.mem_Ico.mp hn_left
                have hn_block : n ∈ Finset.Ico a b :=
                  Finset.mem_Ico.mpr
                    (And.intro hn_left_bounds.1
                      (lt_of_lt_of_le hn_left_bounds.2
                        (le_trans hcd hdb)))
                have hn_not_window :
                    ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ <
                      lam := by
                  intro hn_res
                  have hn_window :
                      n ∈
                        Complex.realPhase_integerIncrementResonanceWindow
                          φ a b resonance lam :=
                    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                      (φ := φ)
                      (a := a)
                      (b := b)
                      (n := n)
                      (resonance := resonance)
                      (lam := lam)).mpr
                      (And.intro hn_block hn_res)
                  have hn_window_interval : n ∈ Finset.Ico c d :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hwindow
                      hn_window
                  have hn_interval_bounds : c ≤ n ∧ n < d :=
                    Finset.mem_Ico.mp hn_window_interval
                  exact not_lt_of_ge hn_interval_bounds.1 hn_left_bounds.2
                (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
                  (φ := φ)
                  (a := a)
                  (b := b)
                  (n := n)
                  (resonance := resonance)
                  (lam := lam)).mpr
                  (And.intro hn_block hn_not_window)
            | Or.inr hn_right =>
                have hn_right_bounds : d ≤ n ∧ n < b :=
                  Finset.mem_Ico.mp hn_right
                have hn_block : n ∈ Finset.Ico a b :=
                  Finset.mem_Ico.mpr
                    (And.intro
                      (le_trans hac (le_trans hcd hn_right_bounds.1))
                      hn_right_bounds.2)
                have hn_not_window :
                    ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ <
                      lam := by
                  intro hn_res
                  have hn_window :
                      n ∈
                        Complex.realPhase_integerIncrementResonanceWindow
                          φ a b resonance lam :=
                    (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                      (φ := φ)
                      (a := a)
                      (b := b)
                      (n := n)
                      (resonance := resonance)
                      (lam := lam)).mpr
                      (And.intro hn_block hn_res)
                  have hn_window_interval : n ∈ Finset.Ico c d :=
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hwindow
                      hn_window
                  have hn_interval_bounds : c ≤ n ∧ n < d :=
                    Finset.mem_Ico.mp hn_window_interval
                  exact not_lt_of_ge hn_right_bounds.1 hn_interval_bounds.2
                (Complex.mem_realPhase_integerIncrementResonanceWindowComplement_iff
                  (φ := φ)
                  (a := a)
                  (b := b)
                  (n := n)
                  (resonance := resonance)
                  (lam := lam)).mpr
                  (And.intro hn_block hn_not_window)))

/-- The two outside intervals in a half-open resonance-window complement are
disjoint. -/
theorem Finset.Ico_left_right_disjoint_of_le
    {a c d b : ℕ}
    (hcd : c ≤ d) :
    Disjoint (Finset.Ico a c) (Finset.Ico d b) := by
  exact
    Finset.disjoint_left.mpr
      (fun n hn_left hn_right =>
        have hn_left_bounds : a ≤ n ∧ n < c :=
          Finset.mem_Ico.mp hn_left
        have hn_right_bounds : d ≤ n ∧ n < b :=
          Finset.mem_Ico.mp hn_right
        not_lt_of_ge (le_trans hcd hn_right_bounds.1) hn_left_bounds.2)

/-- The left outside interval is a subblock of the ambient interval
containing a half-open resonance window. -/
theorem Finset.Ico_left_subset_ambient_of_le
    {a b c : ℕ}
    (hcb : c ≤ b) :
    Finset.Ico a c ⊆ Finset.Ico a b := by
  intro n hn
  have hn_bounds : a ≤ n ∧ n < c :=
    Finset.mem_Ico.mp hn
  exact
    Finset.mem_Ico.mpr
      (And.intro hn_bounds.1
        (lt_of_lt_of_le hn_bounds.2 hcb))

/-- The right outside interval is a subblock of the ambient interval
containing a half-open resonance window. -/
theorem Finset.Ico_right_subset_ambient_of_le
    {a b d : ℕ}
    (had : a ≤ d) :
    Finset.Ico d b ⊆ Finset.Ico a b := by
  intro n hn
  have hn_bounds : d ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn
  exact
    Finset.mem_Ico.mpr
      (And.intro (le_trans had hn_bounds.1) hn_bounds.2)

/-- Raw integer-increment monotonicity restricts to a half-open subblock. -/
theorem Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b) :
    Complex.realPhase_integerIncrementMonotoneOn φ c d := by
  match hmono with
  | Or.inl hmono_inc =>
      exact Or.inl
        (fun m hm n hn hmn =>
          hmono_inc (hsub hm) (hsub hn) hmn)
  | Or.inr hmono_dec =>
      exact Or.inr
        (fun m hm n hn hmn =>
          hmono_dec (hsub hm) (hsub hn) hmn)

/-- Reduced integer-increment monotonicity restricts to a half-open subblock. -/
theorem Complex.realPhase_reducedIntegerIncrementMonotoneOn.mono_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    (hmono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn φ c d := by
  match hmono with
  | Or.inl hmono_inc =>
      exact Or.inl
        (fun m hm n hn hmn =>
          hmono_inc (hsub hm) (hsub hn) hmn)
  | Or.inr hmono_dec =>
      exact Or.inr
        (fun m hm n hn hmn =>
          hmono_dec (hsub hm) (hsub hn) hmn)

/-- Integer-increment separation restricts to a half-open subblock. -/
theorem Complex.realPhase_integerIncrementSeparatedOn.mono_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  exact hsep n (hsub hn) k

/-- The left outside interval avoids a canonical resonance window identified
as `[c,d)`. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_left_avoid_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    ∀ n : ℕ,
      n ∈ Finset.Ico a c →
        n ∉ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam := by
  intro n hn_left hn_window
  have hn_left_bounds : a ≤ n ∧ n < c :=
    Finset.mem_Ico.mp hn_left
  have hn_window_interval : n ∈ Finset.Ico c d :=
    Eq.subst
      (motive := fun S : Finset ℕ => n ∈ S)
      hwindow
      hn_window
  have hn_interval_bounds : c ≤ n ∧ n < d :=
    Finset.mem_Ico.mp hn_window_interval
  exact not_lt_of_ge hn_interval_bounds.1 hn_left_bounds.2

/-- The right outside interval avoids a canonical resonance window identified
as `[c,d)`. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_right_avoid_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    ∀ n : ℕ,
      n ∈ Finset.Ico d b →
        n ∉ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam := by
  intro n hn_right hn_window
  have hn_right_bounds : d ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn_right
  have hn_window_interval : n ∈ Finset.Ico c d :=
    Eq.subst
      (motive := fun S : Finset ℕ => n ∈ S)
      hwindow
      hn_window
  have hn_interval_bounds : c ≤ n ∧ n < d :=
    Finset.mem_Ico.mp hn_window_interval
  exact not_lt_of_ge hn_right_bounds.1 hn_interval_bounds.2

/-- Norm split for a sum over the nonresonant complement after the resonant
window has been identified as a half-open interval. -/
theorem Complex.realPhase_integerIncrementResonanceWindowComplement_sum_norm_le_left_add_right_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (F : ℕ → ℂ)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b resonance lam, F n‖ ≤
      ‖∑ n ∈ Finset.Ico a c, F n‖ +
        ‖∑ n ∈ Finset.Ico d b, F n‖ := by
  have hcomplement_eq :
      Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b resonance lam =
        Finset.Ico a c ∪ Finset.Ico d b :=
    Complex.realPhase_integerIncrementResonanceWindowComplement_eq_left_union_right_of_eq_Ico
      φ hac hcd hdb hwindow
  have hdisjoint :
      Disjoint (Finset.Ico a c) (Finset.Ico d b) :=
    Finset.Ico_left_right_disjoint_of_le hcd
  have hsum_union :
      (∑ n ∈ Finset.Ico a c ∪ Finset.Ico d b, F n) =
        (∑ n ∈ Finset.Ico a c, F n) +
          ∑ n ∈ Finset.Ico d b, F n :=
    Finset.sum_union hdisjoint
  have hsum_complement :
      (∑ n ∈ Complex.realPhase_integerIncrementResonanceWindowComplement
          φ a b resonance lam, F n) =
        (∑ n ∈ Finset.Ico a c, F n) +
          ∑ n ∈ Finset.Ico d b, F n :=
    Eq.trans
      (congrArg
        (fun S : Finset ℕ => ∑ n ∈ S, F n)
        hcomplement_eq)
      hsum_union
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ n ∈ Finset.Ico a c, F n‖ +
            ‖∑ n ∈ Finset.Ico d b, F n‖)
      hsum_complement.symm
      (norm_add_le
        (∑ n ∈ Finset.Ico a c, F n)
        (∑ n ∈ Finset.Ico d b, F n))

/-- Norm split for a half-open block into a resonant window plus the two
outside intervals after the window has been identified as `[c,d)`. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_Ico_sum_norm_le_window_add_left_add_right_of_eq_Ico
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (F : ℕ → ℂ)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d) :
    ‖∑ n ∈ Finset.Ico a b, F n‖ ≤
      ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam, F n‖ +
        (‖∑ n ∈ Finset.Ico a c, F n‖ +
          ‖∑ n ∈ Finset.Ico d b, F n‖) := by
  have hsplit :
      ‖∑ n ∈ Finset.Ico a b, F n‖ ≤
        ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b resonance lam, F n‖ +
          ‖∑ n ∈
            Complex.realPhase_integerIncrementResonanceWindowComplement
              φ a b resonance lam, F n‖ :=
    Complex.realPhase_integerIncrementResonanceWindow_sum_norm_le
      φ a b resonance lam F
  have hcomplement :
      ‖∑ n ∈
          Complex.realPhase_integerIncrementResonanceWindowComplement
            φ a b resonance lam, F n‖ ≤
        ‖∑ n ∈ Finset.Ico a c, F n‖ +
          ‖∑ n ∈ Finset.Ico d b, F n‖ :=
    Complex.realPhase_integerIncrementResonanceWindowComplement_sum_norm_le_left_add_right_of_eq_Ico
      φ F hac hcd hdb hwindow
  exact
    le_trans hsplit
      (add_le_add_left hcomplement
        ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam, F n‖)

/-- If a canonical resonant window is identified as a half-open interval whose
endpoint length is controlled, then the resonant-window exponential sum has
the same real cardinality bound. -/
theorem Complex.realPhase_integerIncrementResonanceWindow_sum_norm_le_of_Ico_length
    (φ ψ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam M : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam =
        Finset.Ico c d)
    (hlength : ((d - c : ℕ) : ℝ) ≤ M) :
    ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam,
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ M := by
  have hunit :
      ∀ n : ℕ,
        n ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b resonance lam →
          ‖Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ 1 := by
    intro n _hn
    exact le_of_eq (Complex.realPhase_exp_I_norm ψ n)
  have hcard_bound :
      ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
            φ a b resonance lam,
          Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
        ((Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam).card : ℝ) :=
    Complex.finite_sum_norm_le_card_of_norm_le_one
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b resonance lam)
      (fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ)))
      hunit
  have hcard_real :
      ((Complex.realPhase_integerIncrementResonanceWindow
          φ a b resonance lam).card : ℝ) =
        ((d - c : ℕ) : ℝ) :=
    Complex.realPhase_integerIncrementResonanceWindow_card_real_eq_of_eq_Ico
      φ hwindow
  exact
    le_trans hcard_bound
      (Eq.subst
        (motive := fun r : ℝ => r ≤ M)
        hcard_real.symm
        hlength)

/-- Shifted-logarithmic specialization of the resonant-window cardinality
bound for the exponential correlation phase. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_sum_norm_le_of_Ico_length
    (t : ℝ)
    {a b h c d : ℕ}
    {resonance lam M : ℝ}
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) resonance lam =
        Finset.Ico c d)
    (hlength : ((d - c : ℕ) : ℝ) ≤ M) :
    ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) resonance lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤ M := by
  exact
    Complex.realPhase_integerIncrementResonanceWindow_sum_norm_le_of_Ico_length
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hwindow
      hlength

/-- Shifted-logarithmic specialization of the three-part half-open split
around an identified resonant window. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_window_add_left_add_right_of_eq_Ico
    (t : ℝ)
    {a b h c d : ℕ}
    {resonance lam : ℝ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) resonance lam =
        Finset.Ico c d) :
    ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
      ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) resonance lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ +
        (‖∑ n ∈ Finset.Ico a c,
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ +
          ‖∑ n ∈ Finset.Ico d (b - h),
            Complex.exp
              (Complex.I *
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h n : ℂ))‖) := by
  exact
    Complex.realPhase_integerIncrementResonanceWindow_Ico_sum_norm_le_window_add_left_add_right_of_eq_Ico
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (fun n : ℕ =>
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ)))
      hac hcd hdb hwindow

/-- A finite resonant-index set for a shifted logarithmic difference is a
half-open resonant window, once the shifted adjacent increments are known to
be monotone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
    (t : ℝ)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h)) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  exact
    Complex.realPhase_integerIncrement_resonanceWindow_exists
      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
      habh S hS hinc_mono

/-- A finite resonant-index set for a shifted logarithmic difference is a
half-open resonant window when the fixed-width parent gap is monotone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_parentGap_monotone
    (t : ℝ)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam)
    (hgap :
      MonotoneOn
        (fun n : ℕ =>
          Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (n + h) -
            Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              n)
        (Finset.Ico a (b - h) : Set ℕ)) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_parentGap_monotone
      t hgap
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
      t habh S hS hinc_mono

/-- A finite resonant-index set for a shifted logarithmic difference is a
half-open resonant window when the fixed-width parent gap is antitone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_parentGap_antitone
    (t : ℝ)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam)
    (hgap :
      AntitoneOn
        (fun n : ℕ =>
          Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (n + h) -
            Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              n)
        (Finset.Ico a (b - h) : Set ℕ)) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_parentGap_antitone
      t hgap
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
      t habh S hS hinc_mono

/-- In the nonnegative-frequency branch, every finite resonant-index set for a
shifted logarithmic difference is a half-open resonant window. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
      t ht_nonneg ha
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
      t habh S hS hinc_mono

/-- In the nonnegative-frequency branch, the canonical resonant-index set for
a shifted logarithmic difference is a half-open resonant window. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_canonical_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧
        Complex.realPhase_integerIncrementResonanceWindow
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
          a (b - h) resonance lam = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
      t ht_nonneg ha
  exact
    Complex.realPhase_integerIncrement_resonanceWindow_exists_canonical
      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
      habh hinc_mono

/-- A family of finite resonant-index sets for a shifted logarithmic
difference consists pointwise of half-open resonant windows in the
nonnegative-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_family_exists_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (S : ℤ → Finset ℕ)
    (hS :
      ∀ k : ℤ,
        ∀ n : ℕ,
          n ∈ S k ↔
            n ∈ Finset.Ico a (b - h) ∧
              ‖Complex.realPhase_integerIncrement
                  (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
                (2 * Real.pi * (k : ℝ))‖ < lam) :
    ∀ k : ℤ,
      ∃ c d : ℕ,
        a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S k = Finset.Ico c d := by
  intro k
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_nonneg
      t ht_nonneg ha habh (S k) (hS k)

/-- A family of finite resonant-index sets for the concrete VdC shifted
logarithmic phase consists pointwise of half-open resonant windows in the
nonnegative-frequency branch. -/
theorem Complex.realPhase_secondDerivative_vdc_logarithmic_resonanceWindow_family_exists_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (S : ℤ → Finset ℕ)
    (hS :
      ∀ k : ℤ,
        ∀ n : ℕ,
          n ∈ S k ↔
            n ∈ Finset.Ico a (b - h) ∧
              ‖Complex.realPhase_integerIncrement
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  n -
                (2 * Real.pi * (k : ℝ))‖ < lam) :
    ∀ k : ℤ,
      ∃ c d : ℕ,
        a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S k = Finset.Ico c d := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_family_exists_of_nonneg
      t ht_nonneg ha habh S hS

/-- In the nonnegative-frequency branch, the canonical resonant-index set for
the concrete logarithmic VdC shifted phase is a half-open resonant window. -/
theorem Complex.realPhase_secondDerivative_vdc_logarithmic_resonanceWindow_exists_canonical_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧
        Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) resonance lam = Finset.Ico c d := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_canonical_of_nonneg
      t ht_nonneg ha habh

/-- Along the canonical Weyl shift range, every integer-centered resonant
family for the concrete logarithmic VdC shifts is pointwise a half-open
window in the nonnegative-frequency branch. -/
theorem Complex.realPhase_secondDerivative_vdc_logarithmic_shiftRange_resonanceWindow_family_exists_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    {lam : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (S : ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ n : ℕ,
              n ∈ S h k ↔
                n ∈ Finset.Ico a (b - h) ∧
                  ‖Complex.realPhase_integerIncrement
                      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                        h)
                      n -
                    (2 * Real.pi * (k : ℝ))‖ < lam h) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ k : ℤ,
          ∃ c d : ℕ,
            a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S h k = Finset.Ico c d := by
  intro h hmem k
  exact
    Complex.realPhase_secondDerivative_vdc_logarithmic_resonanceWindow_family_exists_of_nonneg
      t ht_nonneg ha (habh h hmem) (S h) (hS h hmem) k

/-- Along the canonical Weyl shift range, every constructed integer-centered
resonant window for the concrete logarithmic VdC shifts is a half-open window
in the nonnegative-frequency branch. -/
theorem Complex.realPhase_secondDerivative_vdc_logarithmic_shiftRange_resonanceWindow_exists_canonical_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    {lam : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ k : ℤ,
          ∃ c d : ℕ,
            a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧
              Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h) =
                  Finset.Ico c d := by
  intro h hmem k
  exact
    Complex.realPhase_secondDerivative_vdc_logarithmic_resonanceWindow_exists_canonical_of_nonneg
      t ht_nonneg ha (habh h hmem)

/-- Outside an extensionally specified resonant-index set, the adjacent
increment is separated from that resonance. -/
theorem Complex.realPhase_integerIncrement_separated_from_resonance_of_not_mem_window
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hn_block : n ∈ Finset.Ico a b)
    (hn_not_mem : n ∉ S) :
    lam ≤ ‖Complex.realPhase_integerIncrement φ n - resonance‖ := by
  have hn_not_lt :
      ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam := by
    intro hn_lt
    have hn_mem : n ∈ S :=
      (hS n).mpr (And.intro hn_block hn_lt)
    exact hn_not_mem hn_mem
  exact le_of_not_gt hn_not_lt

/-- A subblock avoiding an extensionally specified resonant window is pointwise
separated from the corresponding resonance center. -/
theorem Complex.realPhase_integerIncrement_separated_from_resonance_on_subblock
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid : ∀ n : ℕ, n ∈ Finset.Ico c d → n ∉ S) :
    ∀ n : ℕ,
      n ∈ Finset.Ico c d →
        lam ≤ ‖Complex.realPhase_integerIncrement φ n - resonance‖ := by
  intro n hn
  exact
    Complex.realPhase_integerIncrement_separated_from_resonance_of_not_mem_window
      φ S hS (hsub hn) (havoid n hn)

/-- A subblock avoiding the resonant window supplies the standard separated
increment hypothesis on that subblock. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hresonance_eq :
      resonance = 2 * Real.pi * (0 : ℝ))
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid : ∀ n : ℕ, n ∈ Finset.Ico c d → n ∉ S)
    (honly_zero :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          ∀ k : ℤ,
            ‖Complex.realPhase_integerIncrement φ n -
                (2 * Real.pi * (0 : ℝ))‖ ≤
              ‖Complex.realPhase_integerIncrement φ n -
                (2 * Real.pi * (k : ℝ))‖) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  have hzero_sep :
      lam ≤
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (0 : ℝ))‖ := by
    have hres_sep :
        lam ≤ ‖Complex.realPhase_integerIncrement φ n - resonance‖ :=
      Complex.realPhase_integerIncrement_separated_from_resonance_on_subblock
        φ S hS hsub havoid n hn
    exact
      Eq.subst
        (motive := fun r : ℝ =>
          lam ≤ ‖Complex.realPhase_integerIncrement φ n - r‖)
        hresonance_eq
        hres_sep
  exact le_trans hzero_sep (honly_zero n hn k)

/-- A subblock avoiding the resonant window supplies separated increments when
principal-interval control makes the zero lattice center the closest center. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance_principal
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hresonance_eq :
      resonance = 2 * Real.pi * (0 : ℝ))
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid : ∀ n : ℕ, n ∈ Finset.Ico c d → n ∉ S)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement φ n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance
      φ S hresonance_eq hS hsub havoid
      (fun n hn k =>
        Complex.realPhase_integerIncrement_zero_lattice_closest_of_mem_principal
          φ (hprincipal n hn) k)

/-- A subblock avoiding the `2πk`-centered window becomes separated after
subtracting the integer lattice slope, provided the shifted increments stay in
the principal branch. -/
theorem Complex.realPhase_integerLatticeShiftSeparatedOn_of_integerResonanceWindow_avoidance_principal
    (φ : ℝ → ℝ)
    (k : ℤ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.realPhase_integerLatticeShift φ k) c d lam := by
  have hshift_window :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_integerLatticeShift φ k)
          a b (2 * Real.pi * (0 : ℝ)) lam =
        Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
    Complex.realPhase_integerIncrementResonanceWindow_integerLatticeShift_zero_eq
      φ k a b lam
  have havoid_shift :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_integerLatticeShift φ k)
            a b (2 * Real.pi * (0 : ℝ)) lam := by
    intro n hn hn_shift
    have hn_original :
        n ∈ Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n ∈ S)
        hshift_window
        hn_shift
    exact havoid n hn hn_original
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance_principal
      (Complex.realPhase_integerLatticeShift φ k)
      (Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_integerLatticeShift φ k)
        a b (2 * Real.pi * (0 : ℝ)) lam)
      rfl
      (fun m =>
        Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          (Complex.realPhase_integerLatticeShift φ k))
      hsub
      havoid_shift
      hprincipal

/-- On a gap assigned to the integer center `k`, avoiding the corresponding
resonance window and staying in the shifted principal branch supplies all
finite-difference inputs for the shifted phase. -/
theorem Complex.realPhase_integerLatticeShift_gap_finiteDifference_inputs
    (φ : ℝ → ℝ)
    (k : ℤ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d ∧
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d ∧
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_integerLatticeShift φ k) c d lam := by
  have hmono_shift_ambient :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) a b :=
    Complex.realPhase_integerIncrementMonotoneOn_integerLatticeShift
      φ k hmono
  have hmono_shift_gap :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d :=
    Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
      (Complex.realPhase_integerLatticeShift φ k)
      hmono_shift_ambient
      hsub
  have hred_shift_gap :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d :=
    Complex.realPhase_reducedIntegerIncrementMonotoneOn_integerLatticeShift_of_principal
      φ k
      (Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
        φ hmono hsub)
      hprincipal
  have hsep_shift_gap :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_integerLatticeShift φ k) c d lam :=
    Complex.realPhase_integerLatticeShiftSeparatedOn_of_integerResonanceWindow_avoidance_principal
      φ k hsub havoid hprincipal
  exact And.intro hmono_shift_gap
    (And.intro hred_shift_gap hsep_shift_gap)

/-- A gap interval contained in the finite-family complement has the
finite-difference inputs for the corresponding integer-lattice shifted phase,
for any chosen center in the finite family. -/
theorem Complex.realPhase_integerLatticeShift_gap_finiteDifference_inputs_of_family_complement
    (φ : ℝ → ℝ)
    (k : ℤ)
    {a b c d : ℕ}
    {lam : ℝ}
    {K : Finset ℤ}
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hk : k ∈ K)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (hgap_subset :
      Finset.Ico c d ⊆
        Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam K)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d ∧
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d ∧
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_integerLatticeShift φ k) c d lam := by
  have havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (k : ℝ)) lam := by
    intro n hn hn_window
    have hn_complement :
        n ∈ Complex.realPhase_integerIncrementResonanceFamilyComplement
          φ a b lam K :=
      hgap_subset hn
    have hn_data :
        n ∈ Finset.Ico a b ∧
          n ∉ Complex.realPhase_integerIncrementResonanceFamilyUnion
            φ a b lam K :=
      (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
        φ).mp hn_complement
    have hn_union :
        n ∈ Complex.realPhase_integerIncrementResonanceFamilyUnion
          φ a b lam K :=
      (Complex.mem_realPhase_integerIncrementResonanceFamilyUnion_iff
        φ).mpr
        (Exists.intro k (And.intro hk hn_window))
    exact hn_data.2 hn_union
  exact
    Complex.realPhase_integerLatticeShift_gap_finiteDifference_inputs
      φ k hmono hsub havoid hprincipal

/-- The left side of a canonical zero-centered resonance window is separated
when the increments on that side lie in the principal branch. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_left_of_canonical_zero_resonanceWindow_eq_Ico_principal
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (0 : ℝ)) lam =
        Finset.Ico c d)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a c →
          Complex.realPhase_integerIncrement φ n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_integerIncrementSeparatedOn φ a c lam := by
  have hsub : Finset.Ico a c ⊆ Finset.Ico a b :=
    Finset.Ico_left_subset_ambient_of_le (le_trans hcd hdb)
  have havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico a c →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (0 : ℝ)) lam :=
    Complex.realPhase_integerIncrementResonanceWindow_left_avoid_of_eq_Ico
      φ hwindow
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance_principal
      φ
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (0 : ℝ)) lam)
      rfl
      (fun m =>
        Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          φ)
      hsub
      havoid
      hprincipal

/-- The right side of a canonical zero-centered resonance window is separated
when the increments on that side lie in the principal branch. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_right_of_canonical_zero_resonanceWindow_eq_Ico_principal
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (0 : ℝ)) lam =
        Finset.Ico c d)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico d b →
          Complex.realPhase_integerIncrement φ n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_integerIncrementSeparatedOn φ d b lam := by
  have hsub : Finset.Ico d b ⊆ Finset.Ico a b :=
    Finset.Ico_right_subset_ambient_of_le (le_trans hac hcd)
  have havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico d b →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            φ a b (2 * Real.pi * (0 : ℝ)) lam :=
    Complex.realPhase_integerIncrementResonanceWindow_right_avoid_of_eq_Ico
      φ hwindow
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance_principal
      φ
      (Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (0 : ℝ)) lam)
      rfl
      (fun m =>
        Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          φ)
      hsub
      havoid
      hprincipal

/-- Avoidance of the resonance window around every integer lattice center
supplies the standard separated-increment hypothesis without any principal
interval or no-winding assumption. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_family_avoidance
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (S : ℤ → Finset ℕ)
    (hS :
      ∀ k : ℤ,
        ∀ m : ℕ,
          m ∈ S k ↔
            m ∈ Finset.Ico a b ∧
              ‖Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ))‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid :
      ∀ k : ℤ,
        ∀ n : ℕ,
          n ∈ Finset.Ico c d →
            n ∉ S k) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  exact
    Complex.realPhase_integerIncrement_separated_from_resonance_of_not_mem_window
      φ (S k) (hS k) (hsub hn) (havoid k n hn)

/-- Avoidance of the canonical resonant window around every integer lattice
center supplies the standard separated-increment hypothesis. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_canonical_resonanceWindow_family_avoidance
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid :
      ∀ k : ℤ,
        ∀ n : ℕ,
          n ∈ Finset.Ico c d →
            n ∉ Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_family_avoidance
      φ
      (fun k : ℤ =>
        Complex.realPhase_integerIncrementResonanceWindow
          φ a b (2 * Real.pi * (k : ℝ)) lam)
      (fun k m =>
        Complex.mem_realPhase_integerIncrementResonanceWindow_iff
          φ)
      hsub havoid

end

end LFunctions
end Boundary
