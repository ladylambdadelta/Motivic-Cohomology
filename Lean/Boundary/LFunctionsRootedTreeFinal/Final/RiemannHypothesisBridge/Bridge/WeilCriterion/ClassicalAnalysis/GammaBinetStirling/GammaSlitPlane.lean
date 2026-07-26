import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.CoherenceComponents
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.BranchIntegral.Owner

/-!
# Gamma slit-plane control on the open right half-plane

This file peels the branch-cut part of the Binet coherence input into the
exact geometric obstruction: after the standard open-right-half-plane
nonvanishing theorem, membership in the principal slit-plane is reduced to
exclusion of the nonpositive real ray.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Gamma has no zeros on the open right half-plane. -/
theorem Complex.Gamma_openRightHalfPlane_nonzero_owner :
    ∀ z : ℂ, 0 < z.re → Complex.Gamma z ≠ 0 :=
  fun z hz =>
    Complex.Gamma_ne_zero_of_re_pos hz

/-- Gamma is positive, hence in the principal slit-plane, on the positive real
axis. -/
theorem Complex.Gamma_positiveReal_mem_slitPlane_owner :
    ∀ x : ℝ, (0 : ℝ) < x → Complex.Gamma (x : ℂ) ∈ Complex.slitPlane :=
  fun x hx =>
    let hGamma_pos : 0 < Real.Gamma x :=
      _root_.Real.Gamma_pos_of_pos hx
    let hGamma_re :
        0 < (Real.Gamma x : ℂ).re :=
      Eq.subst
        (motive := fun y : ℝ => 0 < y)
        (Complex.ofReal_re (Real.Gamma x)).symm
        hGamma_pos
    let hGamma_slit :
        (Real.Gamma x : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hGamma_re)
    Eq.subst
      (motive := fun y : ℂ => y ∈ Complex.slitPlane)
      (Complex.Gamma_ofReal x).symm
      hGamma_slit

/-- Gamma avoids the nonpositive real ray at positive real arguments. -/
theorem Complex.Gamma_positiveReal_nonpositiveRealExclusion_owner :
    ∀ x : ℝ, (0 : ℝ) < x → Complex.Gamma (x : ℂ) ∈ Complex.slitPlane :=
  fun x hx =>
    Complex.Gamma_positiveReal_mem_slitPlane_owner x hx

/- The Gamma image has a principal-log neighborhood at every positive real
argument.  This is the local branch statement actually needed by a scheduled
carrier; it does not assert a false global slit-plane theorem on the whole
right half-plane. -/
theorem Complex.Gamma_positiveReal_local_slitPlane_owner
    (x : ℝ) (hx : 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, z ∈ Metric.ball (x : ℂ) ε →
        Complex.Gamma z ∈ Complex.slitPlane := by
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma (x : ℂ) (fun m hm => by
      have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hneg : -(m : ℝ) ≤ 0 := neg_nonpos.mpr hm_nonneg
      intro h
      have hre : x = -(m : ℝ) := by
        have h' := congrArg Complex.re h
        exact h'
      have : x ≤ 0 := hre ▸ hneg
      exact (not_le_of_gt hx) this)
  have hGamma_cont : ContinuousAt Complex.Gamma (x : ℂ) :=
    hGamma_diff.continuousAt
  have hGamma_mem : Complex.Gamma (x : ℂ) ∈ Complex.slitPlane :=
    Complex.Gamma_positiveReal_mem_slitPlane_owner x hx
  have hpreimage :
      Complex.Gamma ⁻¹' Complex.slitPlane ∈ 𝓝 (x : ℂ) :=
    (Complex.isOpen_slitPlane.mem_nhds hGamma_mem).preimage hGamma_cont
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hε, hball⟩
  exact ⟨ε, hε, fun z hz => hball hz⟩

/- A closed carrier ball can be chosen inside the local principal-log
neighborhood at every positive real center.  This is the form consumed by
compact-carrier estimates. -/
theorem Complex.Gamma_positiveReal_closedBall_mem_slitPlane_owner
    (x : ℝ) (hx : 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, z ∈ Metric.closedBall (x : ℂ) ε →
        Complex.Gamma z ∈ Complex.slitPlane := by
  rcases Complex.Gamma_positiveReal_local_slitPlane_owner x hx with
    ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  have hdist : dist z (x : ℂ) ≤ ε / 2 :=
    Metric.mem_closedBall.mp hz
  have hhalf : ε / 2 < ε := by
    exact half_lt_self hε
  have hlt : dist z (x : ℂ) < ε :=
    hdist.trans_lt hhalf
  exact hball hlt

/- The carrier package consumed by inverse-Gamma estimates: the same closed
ball carries both the principal slit condition and Gamma nonvanishing. -/
theorem Complex.Gamma_positiveReal_closedBall_slitPlane_and_nonzero_owner
    (x : ℝ) (hx : 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, z ∈ Metric.closedBall (x : ℂ) ε →
        Complex.Gamma z ∈ Complex.slitPlane ∧ Complex.Gamma z ≠ 0 := by
  rcases Complex.Gamma_positiveReal_closedBall_mem_slitPlane_owner x hx with
    ⟨ε, hε, hslit⟩
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hslit_z : Complex.Gamma z ∈ Complex.slitPlane := hslit z hz
  exact ⟨hslit_z, Complex.slitPlane_ne_zero hslit_z⟩

/- The scheduled real-centre probes use this restricted carrier package.  It
   records precisely the slit-plane information proved from positivity and
   continuity; it does not promote that information to a statement about the
   entire open right half-plane. -/
def Complex.GammaPositiveRealProbeSlitPlaneControl : Prop :=
  ∀ x : ℝ, 0 < x →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, z ∈ Metric.closedBall (x : ℂ) ε →
        Complex.Gamma z ∈ Complex.slitPlane

theorem Complex.GammaPositiveRealProbeSlitPlaneControl_owner :
    Complex.GammaPositiveRealProbeSlitPlaneControl :=
  fun x hx => Complex.Gamma_positiveReal_closedBall_mem_slitPlane_owner x hx

def Complex.GammaPositiveRealProbeSlitPlaneAndNonzeroControl : Prop :=
  ∀ x : ℝ, 0 < x →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, z ∈ Metric.closedBall (x : ℂ) ε →
        Complex.Gamma z ∈ Complex.slitPlane ∧ Complex.Gamma z ≠ 0

theorem Complex.GammaPositiveRealProbeSlitPlaneAndNonzeroControl_owner :
    Complex.GammaPositiveRealProbeSlitPlaneAndNonzeroControl :=
  fun x hx =>
    Complex.Gamma_positiveReal_closedBall_slitPlane_and_nonzero_owner x hx

/- Continuity transports any already-established Gamma slit-plane value to a
closed carrier ball. -/
theorem Complex.Gamma_closedBall_mem_slitPlane_of_mem_owner
    (z : ℂ) (hz : Complex.Gamma z ∈ Complex.slitPlane) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z ε →
        Complex.Gamma w ∈ Complex.slitPlane := by
  have hgamma_ne : Complex.Gamma z ≠ 0 :=
    Complex.slitPlane_ne_zero hz
  have hnot_pole : ∀ m : ℕ, z ≠ -m := by
    intro m hzm
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff z).mpr ⟨m, hzm⟩)
  have hcont : ContinuousAt Complex.Gamma z :=
    (Complex.differentiableAt_Gamma z hnot_pole).continuousAt
  have hpreimage :
      Complex.Gamma ⁻¹' Complex.slitPlane ∈ 𝓝 z :=
    (Complex.isOpen_slitPlane.mem_nhds hz).preimage hcont
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro w hw
  have hdist : dist w z ≤ ε / 2 :=
    Metric.mem_closedBall.mp hw
  have hhalf : ε / 2 < ε := half_lt_self hε
  have hlt : dist w z < ε := hdist.trans_lt hhalf
  exact hball hlt

/-- A complex exponential whose imaginary coordinate lies in the principal
open strip avoids the principal branch cut. -/
/- The canonical replacement for the false global right-half-plane image
statement: principal-log control is local at every already-admissible Gamma
value, exactly the form needed by a compact scheduled carrier. -/
theorem Complex.exp_mem_slitPlane_of_im_mem_principalOpenStrip
    (w : ℂ)
    (hlo : -Real.pi < w.im)
    (hhi : w.im < Real.pi) :
    Complex.exp w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff_arg.mpr
    (And.intro
      (fun harg_pi =>
        let hmodel :
            Complex.exp w =
              (Real.exp w.re : ℂ) *
                (Complex.cos (w.im : ℂ) +
                  Complex.sin (w.im : ℂ) * Complex.I) :=
          let hexp :
              Complex.exp (w.re : ℂ) = (Real.exp w.re : ℂ) :=
            (Complex.ofReal_exp w.re).symm
          calc
            Complex.exp w =
                Complex.exp (w.re : ℂ) *
                  (Complex.cos (w.im : ℂ) +
                    Complex.sin (w.im : ℂ) * Complex.I) :=
              Complex.exp_eq_exp_re_mul_sin_add_cos (x := w)
            _ =
                (Real.exp w.re : ℂ) *
                  (Complex.cos (w.im : ℂ) +
                    Complex.sin (w.im : ℂ) * Complex.I) := by
              exact congrArg
                (fun a : ℂ =>
                  a *
                    (Complex.cos (w.im : ℂ) +
                      Complex.sin (w.im : ℂ) * Complex.I))
                hexp
        let harg_model :
            Complex.arg
                ((Real.exp w.re : ℂ) *
                  (Complex.cos (w.im : ℂ) +
                    Complex.sin (w.im : ℂ) * Complex.I)) =
              w.im :=
          Complex.arg_mul_cos_add_sin_mul_I
            (Real.exp_pos w.re)
            (And.intro hlo hhi.le)
        let harg_exp :
            Complex.arg (Complex.exp w) = w.im :=
          Eq.trans
            (congrArg Complex.arg hmodel)
            harg_model
        let hpi_eq : Real.pi = w.im :=
          Eq.trans harg_pi.symm harg_exp
        lt_irrefl Real.pi
          (Eq.subst
            (motive := fun y : ℝ => y < Real.pi)
            hpi_eq.symm
            hhi))
      (Complex.exp_ne_zero w))

/-- The Binet logarithm branch stays in the principal open strip on the open
right half-plane. -/
def Complex.BinetLogGammaBranchPrincipalOpenStrip : Prop :=
  ∀ z : ℂ,
    0 < z.re →
      -Real.pi < (Complex.binetLogGammaBranch z).im ∧
        (Complex.binetLogGammaBranch z).im < Real.pi

/-- The Binet principal-log coherence package contains the Gamma slit-plane
control as its first component. -/
theorem Complex.GammaLocalSlitPlaneControl_of_gammaBinetPrincipalLogCoherence_owner
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Complex.GammaLocalSlitPlaneControl :=
  hcoh.1

/-- On the positive real axis, the Binet logarithm branch lies in the
principal open strip. -/
theorem Complex.binetLogGammaBranch_positiveReal_mem_principalOpenStrip_owner :
    ∀ x : ℝ,
      (0 : ℝ) < x →
        -Real.pi < (Complex.binetLogGammaBranch (x : ℂ)).im ∧
          (Complex.binetLogGammaBranch (x : ℂ)).im < Real.pi :=
  fun x hx =>
    let him :
        (Complex.binetLogGammaBranch (x : ℂ)).im = 0 :=
      Complex.binetLogGammaBranch_posReal_im_eq_zero_owner hx
    And.intro
      (Eq.subst
        (motive := fun y : ℝ => -Real.pi < y)
        him.symm
        (neg_lt_zero.mpr Real.pi_pos))
      (Eq.subst
        (motive := fun y : ℝ => y < Real.pi)
        him.symm
        Real.pi_pos)

/-- Principal-strip control of the Abel-Plana logarithm branch gives the Gamma
slit-plane control on the open right half-plane. -/
theorem Complex.GammaRightHalfPlaneSlitPlaneControl_of_binetLogGammaBranchPrincipalOpenStrip_owner
    (hstrip : Complex.BinetLogGammaBranchPrincipalOpenStrip) :
    Complex.GammaRightHalfPlaneSlitPlaneControl :=
  fun z hz =>
    let hstrip_z :
        -Real.pi < (Complex.binetLogGammaBranch z).im ∧
          (Complex.binetLogGammaBranch z).im < Real.pi :=
      hstrip z hz
    let hbranch_slit :
        Complex.exp (Complex.binetLogGammaBranch z) ∈ Complex.slitPlane :=
      Complex.exp_mem_slitPlane_of_im_mem_principalOpenStrip
        (Complex.binetLogGammaBranch z)
        hstrip_z.1
        hstrip_z.2
    let hfinite :
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z :=
      Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner z hz
    let hbranch_exp :
        Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z :=
      Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana
        z
        hz
        hfinite
    Eq.subst
      (motive := fun y : ℂ => y ∈ Complex.slitPlane)
      hbranch_exp
      hbranch_slit

end

end LFunctions
end Boundary
