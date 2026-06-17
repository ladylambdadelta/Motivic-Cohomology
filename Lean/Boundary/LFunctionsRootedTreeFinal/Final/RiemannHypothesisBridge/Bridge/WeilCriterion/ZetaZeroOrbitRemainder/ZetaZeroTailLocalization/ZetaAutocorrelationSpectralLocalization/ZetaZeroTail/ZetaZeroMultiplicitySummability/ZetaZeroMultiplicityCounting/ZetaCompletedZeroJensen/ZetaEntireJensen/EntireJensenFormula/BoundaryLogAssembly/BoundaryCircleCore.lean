import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.ProductLogCore

/-!
# Boundary-circle core for Jensen formula

This split owns the elementary boundary-circle parametrization and quotient
boundary-zero parameter set used by both boundary-log assembly and origin Taylor
transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A nonnegative real radius has the same norm after embedding in `ℂ`. -/
theorem complex_norm_ofReal_of_nonnegative
    {r : ℝ}
    (hr : 0 ≤ r) :
    ‖(r : ℂ)‖ = r := by
  have hnorm_real : ‖(r : ℂ)‖ = ‖r‖ :=
    Complex.norm_real r
  have hreal_norm_abs : ‖r‖ = |r| :=
    Real.norm_eq_abs r
  have habs : |r| = r :=
    abs_of_nonneg hr
  exact hnorm_real.trans (hreal_norm_abs.trans habs)

/-- The Jensen circle parametrization has the requested radius. -/
theorem entireFunctionJensenBoundaryCircle_norm
    {R θ : ℝ}
    (hR : 0 ≤ R) :
    ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
  have hR_norm : ‖(R : ℂ)‖ = R :=
    complex_norm_ofReal_of_nonnegative hR
  have hExp_norm : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  calc
    ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ =
        ‖(R : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
      exact norm_mul (R : ℂ) (Complex.exp (θ * Complex.I))
    _ = R * 1 := by
      exact congrArg₂ HMul.hMul hR_norm hExp_norm
    _ = R := mul_one R

/-- Boundary parameters where a quotient factor vanishes on the Jensen circle. -/
def entireFunctionJensenQuotientBoundaryZeroParameters
    (G : ℂ → ℂ)
    (R : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
    G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0}

/-- Outside the quotient boundary-zero parameter set, the quotient sample is
nonzero. -/
theorem entireFunctionJensenQuotientBoundary_sample_ne_of_not_mem_zeroParameters
    (G : ℂ → ℂ)
    {R θ : ℝ}
    (hθ :
      θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R)
    (hθI : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  intro hzero
  exact hθ ⟨hθI, hzero⟩

/-- If the boundary parametrization is injective on the fundamental arc and
the circle zero set is finite, then the quotient boundary-zero parameters are
finite. -/
theorem entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
    (G : ℂ → ℂ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hInj :
      Set.InjOn
        (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)))
    (hCircle : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite := by
  let f : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} → ℂ :=
    fun θ => (R : ℂ) * Complex.exp (θ * Complex.I)
  have hInjSubtype : Function.Injective f := by
    intro a b hEq
    exact Subtype.ext (hInj a.2 b.2 hEq)
  have hpre : (f ⁻¹' {z : ℂ | ‖z‖ = R ∧ G z = 0}).Finite :=
    hCircle.preimage fun _ _ _ _ hEq => hInjSubtype hEq
  have hIocFinite :
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0}.Finite := by
    have himage :
        (Subtype.val '' (f ⁻¹' {z : ℂ | ‖z‖ = R ∧ G z = 0})).Finite :=
      hpre.image Subtype.val
    exact
      himage.subset
        (fun θ hθ =>
          ⟨⟨θ, hθ.1⟩,
            ⟨entireFunctionJensenBoundaryCircle_norm hR, hθ.2⟩,
            rfl⟩)
  have hsubset_zero :
      {θ : ℝ |
        θ ∈ entireFunctionJensenQuotientBoundaryZeroParameters G R ∧ θ = 0} ⊆
        ({0} : Set ℝ) := by
    intro θ hθ
    exact hθ.2
  have hfinite_zero :
      {θ : ℝ |
        θ ∈ entireFunctionJensenQuotientBoundaryZeroParameters G R ∧ θ = 0}.Finite :=
    (Set.finite_singleton (0 : ℝ)).subset hsubset_zero
  have hsubset_ioc :
      {θ : ℝ |
        θ ∈ entireFunctionJensenQuotientBoundaryZeroParameters G R ∧ θ ≠ 0} ⊆
        {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
          G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0} := by
    intro θ hθ
    exact ⟨⟨lt_of_le_of_ne hθ.1.1.1 hθ.2.symm, hθ.1.1.2⟩, hθ.1.2⟩
  have hfinite_ioc :
      {θ : ℝ |
        θ ∈ entireFunctionJensenQuotientBoundaryZeroParameters G R ∧ θ ≠ 0}.Finite :=
    hIocFinite.subset hsubset_ioc
  have hsplit :
      entireFunctionJensenQuotientBoundaryZeroParameters G R =
        {θ : ℝ |
          θ ∈ entireFunctionJensenQuotientBoundaryZeroParameters G R ∧ θ = 0} ∪
        {θ : ℝ |
          θ ∈ entireFunctionJensenQuotientBoundaryZeroParameters G R ∧ θ ≠ 0} :=
    Set.ext
      (fun θ =>
        Iff.intro
          (fun hθ =>
            match eq_or_ne θ 0 with
            | Or.inl hθ0 => Or.inl ⟨hθ, hθ0⟩
            | Or.inr hθ0 => Or.inr ⟨hθ, hθ0⟩)
          (fun hθ =>
            match hθ with
            | Or.inl hθzero => hθzero.1
            | Or.inr hθioc => hθioc.1))
  exact
    Eq.subst
      (motive := fun S : Set ℝ => S.Finite)
      hsplit.symm
      (hfinite_zero.union hfinite_ioc)

end
end LFunctions
end Boundary
