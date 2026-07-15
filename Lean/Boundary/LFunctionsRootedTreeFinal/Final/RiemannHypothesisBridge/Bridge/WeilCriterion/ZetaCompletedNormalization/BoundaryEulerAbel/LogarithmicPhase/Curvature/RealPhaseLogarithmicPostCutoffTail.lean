import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicPostCutoffIncrement

/-!
# Post-cutoff first-derivative tail

The principal-strip increment is separated from zero by the block endpoint
scale and from every nonzero `2π` lattice point by one.  Since a nonempty
post-cutoff block has endpoint scale below one, this gives the complete
Kusmin--Landau separation hypothesis and hence the concrete tail estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.postCutoff_endpointScale_lt_one
    (t : ℝ) {b : ℕ}
    (hstart : Real.logarithmicPhaseFrequencyTailStart t ≤ b) :
    ‖t‖ / ((b + 1 : ℕ) : ℝ) < 1 := by
  have hnormStart := Real.norm_lt_frequencyTailStart_cast t
  have hstartCast :
      ((Real.logarithmicPhaseFrequencyTailStart t : ℕ) : ℝ) ≤ (b : ℝ) :=
    Nat.cast_le.mpr hstart
  have hnormB : ‖t‖ < (b : ℝ) := lt_of_lt_of_le hnormStart hstartCast
  have hbSucc : (b : ℝ) < ((b + 1 : ℕ) : ℝ) := by
    exact Nat.cast_lt.mpr (Nat.lt_succ_self b)
  have hnormSucc := lt_trans hnormB hbSucc
  have hsuccPos : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  exact (div_lt_one hsuccPos).mpr hnormSucc

theorem Real.postCutoff_endpointScale_le_one
    (t : ℝ) {b : ℕ}
    (hstart : Real.logarithmicPhaseFrequencyTailStart t ≤ b) :
    ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ 1 :=
  le_of_lt (Real.postCutoff_endpointScale_lt_one t hstart)

theorem Real.one_le_two_pi_mul_posNat
    (q : ℕ) :
    (1 : ℝ) ≤ 2 * Real.pi * ((q + 1 : ℕ) : ℝ) := by
  have honeTwoPi := Real.logarithmicPhase_one_le_two_pi
  have hq : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le q))
  have htwoPiNonneg : 0 ≤ 2 * Real.pi :=
    mul_nonneg (OfNat.zero_le 2) Real.pi_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hq htwoPiNonneg
  exact le_trans honeTwoPi
    (Eq.subst (motive := fun value : ℝ => 2 * Real.pi ≤ value)
      (mul_one (2 * Real.pi)).symm hscaled)

theorem Real.two_le_two_pi_mul_posNat
    (q : ℕ) :
    (2 : ℝ) ≤ 2 * Real.pi * ((q + 1 : ℕ) : ℝ) := by
  have htwoPi : (2 : ℝ) ≤ 2 * Real.pi :=
    mul_le_mul_of_nonneg_left
      (le_of_lt (lt_trans (Nat.one_lt_ofNat : (1 : ℝ) < 3)
        Real.pi_gt_three))
      (OfNat.zero_le 2)
  have hq : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le q))
  have hscaled := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (OfNat.zero_le 2) Real.pi_pos.le)
  exact le_trans htwoPi
    (Eq.subst (motive := fun value : ℝ => 2 * Real.pi ≤ value)
      (mul_one (2 * Real.pi)).symm hscaled)

theorem Real.principalNegative_distance_positiveLattice_ge_one
    {θ : ℝ}
    (hθ : θ ≤ 0)
    (q : ℕ) :
    (1 : ℝ) ≤ ‖θ - 2 * Real.pi * ((q + 1 : ℕ) : ℝ)‖ := by
  let A := 2 * Real.pi * ((q + 1 : ℕ) : ℝ)
  have hA := Real.one_le_two_pi_mul_posNat q
  have hsub : θ - A ≤ -1 := by
    have hzero := sub_le_sub_right hθ A
    have hneg := neg_le_neg hA
    exact le_trans hzero
      (Eq.subst (motive := fun value : ℝ => value ≤ -1)
        (zero_sub A).symm hneg)
  have habs : (1 : ℝ) ≤ |θ - A| := le_abs'.mpr (Or.inl hsub)
  exact Eq.subst (motive := fun value : ℝ => 1 ≤ value)
    (Real.norm_eq_abs (θ - A)).symm habs

theorem Real.principalNegative_distance_negativeLattice_ge_one
    {θ : ℝ}
    (hθ : -(1 : ℝ) < θ)
    (q : ℕ) :
    (1 : ℝ) ≤ ‖θ - 2 * Real.pi * (-((q + 1 : ℕ) : ℝ))‖ := by
  let A := 2 * Real.pi * ((q + 1 : ℕ) : ℝ)
  have hA := Real.two_le_two_pi_mul_posNat q
  have hsum : (1 : ℝ) < θ + A := by
    have hadd := add_lt_add_of_lt_of_le hθ hA
    exact Eq.subst (motive := fun value : ℝ => value < θ + A)
      (show (-(1 : ℝ) + 2) = 1 from rfl) hadd
  have hmulNeg :
      2 * Real.pi * (-((q + 1 : ℕ) : ℝ)) = -A :=
    mul_neg (2 * Real.pi) ((q + 1 : ℕ) : ℝ)
  have hsub :
      θ - 2 * Real.pi * (-((q + 1 : ℕ) : ℝ)) = θ + A := by
    exact Eq.trans (congrArg (fun value : ℝ => θ - value) hmulNeg)
      (sub_neg_eq_add θ A)
  have habs : (1 : ℝ) ≤
      |θ - 2 * Real.pi * (-((q + 1 : ℕ) : ℝ))| := by
    exact le_abs'.mpr (Or.inr
      (Eq.subst (motive := fun value : ℝ => 1 ≤ value)
        hsub.symm (le_of_lt hsum)))
  exact Eq.subst (motive := fun value : ℝ => 1 ≤ value)
    (Real.norm_eq_abs _).symm habs

theorem Complex.logarithmicPhase_postCutoff_incrementSeparatedOn
    (t : ℝ) (ht : 0 ≤ t) {b : ℕ}
    (hstart : Real.logarithmicPhaseFrequencyTailStart t ≤ b) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.logarithmicPhaseFrequencyTailStart t) b
      (‖t‖ / ((b + 1 : ℕ) : ℝ)) := by
  intro n hn k
  have hnData := Finset.mem_Ico.mp hn
  let θ := Complex.realPhase_integerIncrement
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n
  have hθLower :=
    Complex.logarithmicPhase_postCutoff_increment_neg_one_lt t ht hnData.1
  have hnPos : 0 < n := lt_of_lt_of_le
    (Real.logarithmicPhaseFrequencyTailStart_pos t) hnData.1
  have hθUpper :=
    Complex.logarithmicPhase_postCutoff_increment_nonpos t ht hnPos
  have hlamOne := Real.postCutoff_endpointScale_le_one t hstart
  cases k with
  | ofNat q =>
      cases q with
      | zero =>
          have hzero :=
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_norm_ge_blockScale
              t
              (Nat.succ_le_of_lt
                (Real.logarithmicPhaseFrequencyTailStart_pos t)) hn
          exact Eq.subst
            (motive := fun value : ℝ => _ ≤ ‖θ - value‖)
            (show (2 * Real.pi * ((0 : ℕ) : ℝ)) = 0 from by rfl).symm
            (Eq.subst (motive := fun value : ℝ => _ ≤ ‖value‖)
              (sub_zero θ).symm hzero)
      | succ q =>
          exact le_trans hlamOne
            (Real.principalNegative_distance_positiveLattice_ge_one hθUpper q)
  | negSucc q =>
      exact le_trans hlamOne
        (Real.principalNegative_distance_negativeLattice_ge_one hθLower q)

theorem Complex.logarithmicPhaseRealPhase_postCutoffTail_le_twentyTarget
    (t : ℝ) (htNorm : 1 ≤ ‖t‖) (ht : 0 ≤ t)
    {b : ℕ}
    (hstart : Real.logarithmicPhaseFrequencyTailStart t ≤ b) :
    ‖∑ n ∈ Finset.Icc (Real.logarithmicPhaseFrequencyTailStart t) b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)) := by
  have hfirst : 1 ≤ Real.logarithmicPhaseFrequencyTailStart t :=
    Nat.succ_le_of_lt (Real.logarithmicPhaseFrequencyTailStart_pos t)
  have hreduced :=
    Complex.logarithmicPhase_postCutoff_reducedIncrementMonotoneOn
      t ht hstart
  have hsep := Complex.logarithmicPhase_postCutoff_incrementSeparatedOn
    t ht hstart
  exact
    Complex.logarithmicPhaseRealPhase_firstDerivative_subblock_le_twentyTarget_of_reduced_sep
      t htNorm ht hfirst hstart (Nat.le_refl b) hreduced hsep

end

end LFunctions
end Boundary
