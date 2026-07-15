import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualAllLatticeSeparation

/-!
# Monotonicity of dual shifted increments

Each unit-cell increment is a shifted derivative value at an interior
mean-value point.  Mean-value points belonging to strictly ordered cells are
ordered, and the shifted derivative is strictly increasing.  Hence the raw
dual shifted increments are strictly increasing with the natural index.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Nat.cellInterior_ordered
    {n m : ℕ} {x y : ℝ}
    (hnm : n < m)
    (hx : x ∈ Set.Ioo (n : ℝ) ((n + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Ioo (m : ℝ) ((m + 1 : ℕ) : ℝ)) :
    x < y := by
  have hsuccLe : n + 1 ≤ m := Nat.succ_le_of_lt hnm
  have hcast : ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hsuccLe
  exact lt_of_lt_of_le hx.2 (le_trans hcast (le_of_lt hy.1))

theorem Complex.logarithmicPhaseDualShiftedIncrement_strictMono
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℕ} (hh : 0 < h) :
    StrictMonoOn
      (Complex.logarithmicPhaseDualShiftedIncrement t h)
      {n : ℕ | 0 < n} := by
  intro n hn m hm hnm
  rcases Complex.exists_dualShiftDerivative_eq_increment t ht hh hn with
    ⟨x, hx, hxEq⟩
  rcases Complex.exists_dualShiftDerivative_eq_increment t ht hh hm with
    ⟨y, hy, hyEq⟩
  have hxy := Nat.cellInterior_ordered hnm hx hy
  have hxPos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) (le_of_lt hx.1)
  have hyPos := lt_of_lt_of_le (Nat.cast_pos.mpr hm) (le_of_lt hy.1)
  have hderivative :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_strictMonoOn
      t ht (Nat.cast_pos.mpr hh) hxPos hyPos hxy
  exact Eq.subst
    (motive := fun left : ℝ =>
      left < Complex.logarithmicPhaseDualShiftedIncrement t h m)
    hxEq
    (Eq.subst
      (motive := fun right : ℝ =>
        Complex.logarithmicPhaseDualShiftedDifferenceDerivative
          t (h : ℝ) x < right)
      hxEq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          Complex.logarithmicPhaseDualShiftedDifferenceDerivative
            t (h : ℝ) x < right)
        hyEq.symm hderivative))

theorem Complex.logarithmicPhaseDualShiftedIncrement_monotoneOn_positive
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℕ} (hh : 0 < h) :
    MonotoneOn
      (Complex.logarithmicPhaseDualShiftedIncrement t h)
      {n : ℕ | 0 < n} := by
  exact
    (Complex.logarithmicPhaseDualShiftedIncrement_strictMono t ht hh).monotoneOn

theorem Complex.logarithmicPhaseDualShiftedIncrement_monotone_on_Icc
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h a b : ℕ} (hh : 0 < h) (ha : 0 < a) :
    ∀ n ∈ Finset.Icc a b,
      ∀ m ∈ Finset.Icc a b,
        n ≤ m →
          Complex.logarithmicPhaseDualShiftedIncrement t h n ≤
            Complex.logarithmicPhaseDualShiftedIncrement t h m := by
  intro n hn m hm hnm
  have hnPos := lt_of_lt_of_le ha (Finset.mem_Icc.mp hn).1
  have hmPos := lt_of_lt_of_le ha (Finset.mem_Icc.mp hm).1
  exact
    Complex.logarithmicPhaseDualShiftedIncrement_monotoneOn_positive
      t ht hh hnPos hmPos hnm

theorem Complex.logarithmicPhaseDualShiftedIncrement_monotone_on_Ico
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h a b : ℕ} (hh : 0 < h) (ha : 0 < a) :
    ∀ n ∈ Finset.Ico a b,
      ∀ m ∈ Finset.Ico a b,
        n ≤ m →
          Complex.logarithmicPhaseDualShiftedIncrement t h n ≤
            Complex.logarithmicPhaseDualShiftedIncrement t h m := by
  intro n hn m hm hnm
  have hnPos := lt_of_lt_of_le ha (Finset.mem_Ico.mp hn).1
  have hmPos := lt_of_lt_of_le ha (Finset.mem_Ico.mp hm).1
  exact
    Complex.logarithmicPhaseDualShiftedIncrement_monotoneOn_positive
      t ht hh hnPos hmPos hnm

theorem Complex.logarithmicPhaseDualShiftedIncrement_strictMono_on_Ico
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h a b : ℕ} (hh : 0 < h) (ha : 0 < a) :
    ∀ n ∈ Finset.Ico a b,
      ∀ m ∈ Finset.Ico a b,
        n < m →
          Complex.logarithmicPhaseDualShiftedIncrement t h n <
            Complex.logarithmicPhaseDualShiftedIncrement t h m := by
  intro n hn m hm hnm
  have hnPos := lt_of_lt_of_le ha (Finset.mem_Ico.mp hn).1
  have hmPos := lt_of_lt_of_le ha (Finset.mem_Ico.mp hm).1
  exact
    Complex.logarithmicPhaseDualShiftedIncrement_strictMono
      t ht hh hnPos hmPos hnm

theorem Complex.logarithmicPhaseDualShiftedIncrement_neg_on_positive
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℕ} (hh : 0 < h) :
    ∀ n : ℕ, 0 < n →
      Complex.logarithmicPhaseDualShiftedIncrement t h n < 0 := by
  intro n hn
  exact Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hn

theorem Complex.logarithmicPhaseDualShiftedIncrement_abs_antitone_on_positive
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℕ} (hh : 0 < h) :
    AntitoneOn
      (fun n : ℕ =>
        |Complex.logarithmicPhaseDualShiftedIncrement t h n|)
      {n : ℕ | 0 < n} := by
  intro n hn m hm hnm
  have hmono :=
    Complex.logarithmicPhaseDualShiftedIncrement_monotoneOn_positive
      t ht hh hn hm hnm
  have hnNeg :=
    Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hn
  have hmNeg :=
    Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hm
  have hnAbs := abs_of_neg hnNeg
  have hmAbs := abs_of_neg hmNeg
  exact Eq.subst (motive := fun right : ℝ => right ≤ _)
    hmAbs.symm
    (Eq.subst (motive := fun left : ℝ => _ ≤ left)
      hnAbs.symm (neg_le_neg hmono))

end

end LFunctions
end Boundary
