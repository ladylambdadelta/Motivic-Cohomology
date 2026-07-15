import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBasePrincipalRuns

/-!
# Kusmin--Landau bounds on base dual principal runs

Every nonempty principal run has antitone raw increments, antitone centered
increments, and uniform separation from `2*pi*Z`.  The generic separated
increment theorem therefore bounds the unweighted dual oscillation uniformly
on the run and on each of its prefixes.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Finset.Ico_eq_Icc_pred_of_lt
    {a b : ℕ} (hab : a < b) :
    Finset.Ico a b = Finset.Icc a (b - 1) := by
  exact Finset.ext (fun n =>
    Iff.intro
      (fun hn =>
        have hdata := Finset.mem_Ico.mp hn
        Finset.mem_Icc.mpr
          (And.intro hdata.1 (Nat.le_sub_one_of_lt hdata.2)))
      (fun hn =>
        have hdata := Finset.mem_Icc.mp hn
        have hbPos : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
        have hpredSucc : b - 1 + 1 = b := Nat.sub_add_cancel
          (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le a) hab))
        have hnLt : n < b := Eq.subst
          (motive := fun z : ℕ => n < z) hpredSucc
          (Nat.lt_succ_of_le hdata.2)
        Finset.mem_Ico.mpr (And.intro hdata.1 hnLt))

theorem Complex.logarithmicPhaseDualBasePrincipalRun_rawMonotone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} {K M : ℕ}
    (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.logarithmicPhaseDualBaseAction t) p.1 p.2 := by
  exact Or.inr
    (Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseIncrement_antitone
      t ht hK hp)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_Ico_norm_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} (heta : 0 < eta)
    {K M : ℕ} (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M)
    (hpNonempty : p.1 < p.2) :
    ‖∑ n ∈ Finset.Ico p.1 p.2,
        Complex.logarithmicPhaseDualOscillationNat t n‖ ≤
      4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
  have hpBounds := Complex.logarithmicPhaseDualBasePrincipalRun_bounded
    t eta K M hp
  have hstart : 1 ≤ p.1 := le_trans hK hpBounds.1
  have hend : p.1 ≤ p.2 - 1 := Nat.le_sub_one_of_lt hpNonempty
  have hincSub : Finset.Ico p.1 (p.2 - 1) ⊆ Finset.Ico p.1 p.2 := by
    intro n hn
    have hdata := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr
      (And.intro hdata.1
        (lt_of_lt_of_le hdata.2 (Nat.sub_le p.2 1)))
  have hraw :=
    (Complex.logarithmicPhaseDualBasePrincipalRun_rawMonotone
      t ht hK hp).mono_Ico hincSub
  have hreduced :=
    (Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseReducedMonotone
      t ht hK hp).mono_Ico hincSub
  have hseparated : Complex.realPhase_integerIncrementSeparatedOn
      (Complex.logarithmicPhaseDualBaseAction t) p.1 (p.2 - 1) eta := by
    intro n hn k
    exact Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseSeparated
      t hp n (hincSub hn) k
  have hbound := Complex.realPhase_separatedIncrement_integer_block_bound
    (Complex.logarithmicPhaseDualBaseAction t)
    hstart hend heta hraw hreduced hseparated
  have hinterval := Finset.Ico_eq_Icc_pred_of_lt hpNonempty
  have hsum :
      (∑ n ∈ Finset.Ico p.1 p.2,
          Complex.logarithmicPhaseDualOscillationNat t n) =
        ∑ n ∈ Finset.Icc p.1 (p.2 - 1),
          Complex.exp
            (Complex.I *
              (Complex.logarithmicPhaseDualBaseAction t n : ℂ)) := by
    exact Eq.trans
      (congrArg
        (fun S : Finset ℕ =>
          ∑ n ∈ S, Complex.logarithmicPhaseDualOscillationNat t n)
        hinterval)
      (Finset.sum_congr rfl
        (fun n hn =>
          Complex.logarithmicPhaseDualOscillationNat_eq_baseAction_exp t n))
  exact Eq.subst (motive := fun z : ℂ => ‖z‖ ≤ _)
    hsum.symm hbound

theorem Complex.logarithmicPhaseDualBasePrincipalRun_prefix_norm_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} (heta : 0 < eta)
    {K M : ℕ} (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    ∀ r : ℕ, p.1 < r → r ≤ p.2 →
      ‖∑ n ∈ Finset.Ico p.1 r,
          Complex.logarithmicPhaseDualOscillationNat t n‖ ≤
        4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
  intro r hstart hrEnd
  have hsub : Finset.Ico p.1 r ⊆ Finset.Ico p.1 p.2 := by
    intro n hn
    have hdata := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr
      (And.intro hdata.1 (lt_of_lt_of_le hdata.2 hrEnd))
  have hraw :=
    (Complex.logarithmicPhaseDualBasePrincipalRun_rawMonotone
      t ht hK hp).mono_Ico hsub
  have hreduced :=
    (Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseReducedMonotone
      t ht hK hp).mono_Ico hsub
  have hseparated : Complex.realPhase_integerIncrementSeparatedOn
      (Complex.logarithmicPhaseDualBaseAction t) p.1 r eta := by
    intro n hn k
    exact Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseSeparated
      t hp n (hsub hn) k
  have hpBounds := Complex.logarithmicPhaseDualBasePrincipalRun_bounded
    t eta K M hp
  have hone : 1 ≤ p.1 := le_trans hK hpBounds.1
  have hend : p.1 ≤ r - 1 := Nat.le_sub_one_of_lt hstart
  have hbound := Complex.realPhase_separatedIncrement_integer_block_bound
    (Complex.logarithmicPhaseDualBaseAction t)
    hone hend heta hraw hreduced hseparated
  have hinterval := Finset.Ico_eq_Icc_pred_of_lt hstart
  exact Eq.subst (motive := fun z : ℂ => ‖z‖ ≤ _)
    (Eq.trans
      (congrArg
        (fun S : Finset ℕ =>
          ∑ n ∈ S, Complex.logarithmicPhaseDualOscillationNat t n)
        hinterval)
      (Finset.sum_congr rfl
        (fun n hn =>
          Complex.logarithmicPhaseDualOscillationNat_eq_baseAction_exp t n))).symm
    hbound

end

end LFunctions
end Boundary
