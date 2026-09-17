import RankTwoPoisson.Symplectic

/-!
# Canonical Poisson calculus

Mixed partials commute; the canonical bracket satisfies Jacobi, and its
Hamiltonian derivations respect the commutator bracket.
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace Calculus
noncomputable section

variable {K σ : Type*} [CommRing K] [DecidableEq σ]

/-- Formal mixed partial derivatives commute. -/
theorem pderiv_comm (i j : σ) (f : MvPolynomial σ K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
    MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  have h : ⁅MvPolynomial.pderiv (R:=K) i, MvPolynomial.pderiv (R:=K) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, hi, hj]
  have hf := congrArg (fun D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) => D f) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using hf

section Field
variable (K : Type*) [Field K]

/-- Hamiltonian commutators for the canonical bracket. -/
theorem hamiltonian_identity (f g h : MvPolynomial Var K) :
    bracketK K f (bracketK K g h) - bracketK K g (bracketK K f h) =
    bracketK K (bracketK K f g) h := by
  simp [bracketK, polyDerivK, pderiv_comm]
  ring

/-- The canonical bracket satisfies the cyclic Jacobi identity. -/
theorem jacobi (f g h : MvPolynomial Var K) :
    bracketK K f (bracketK K g h) + bracketK K g (bracketK K h f) +
      bracketK K h (bracketK K f g) = 0 := by
  have hi := hamiltonian_identity K f g h
  rw [Symplectic.bracket_skewK K h f, Symplectic.bracket_skewK K h (bracketK K f g)]
  have hn : bracketK K g (- bracketK K f h) = - bracketK K g (bracketK K f h) := by
    simp [bracketK, polyDerivK]
    ring
  rw [hn]
  linear_combination hi

/-- Hamiltonian vector field as an actual polynomial derivation. -/
def hamiltonian (f : MvPolynomial Var K) :
    Derivation K (MvPolynomial Var K) (MvPolynomial Var K) :=
    (MvPolynomial.pderiv 2 f) • MvPolynomial.pderiv 0 -
    (MvPolynomial.pderiv 0 f) • MvPolynomial.pderiv 2 +
    (MvPolynomial.pderiv 3 f) • MvPolynomial.pderiv 1 -
    (MvPolynomial.pderiv 1 f) • MvPolynomial.pderiv 3

theorem hamiltonian_apply (f g : MvPolynomial Var K) :
    hamiltonian K f g = bracketK K f g := rfl

theorem hamiltonian_commutator (f g : MvPolynomial Var K) :
    ⁅hamiltonian K f, hamiltonian K g⁆ = hamiltonian K (bracketK K f g) := by
  apply Derivation.ext
  intro h
  simpa only [Derivation.commutator_apply, hamiltonian_apply] using
    hamiltonian_identity K f g h

end Field
end
end Calculus
end RankTwoPoisson
