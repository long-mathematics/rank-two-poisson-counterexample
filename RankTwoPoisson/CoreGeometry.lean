import RankTwoPoisson.Core

/-!
# Matrix interpretation of the core certificates

The core Jacobian has rows (r,t,s) and columns (x,y,β). Its determinant is
identified with Matrix.det and transported to every characteristic-zero field.
The residual two-form is represented by its complete alternating coefficient
matrix in the same source-coordinate order.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RankTwoPoisson
namespace Core
noncomputable section

/-- The ordered three-variable output tuple (r,t,s). -/
abbrev coreOutput : CoreVar → CoreP := ![r,t,s]

/-- The actual formal Jacobian of the rational core. -/
def jacobianMatrix : Matrix CoreVar CoreVar CoreP :=
  fun i j => MvPolynomial.pderiv j (coreOutput i)

/-- The existing determinant certificate, expressed with Matrix.det. -/
theorem core_det_rational : jacobianMatrix.det = 1 := by
  have h : jacobianMatrix.det = jac3 r t s := by
    rw [Matrix.det_fin_three]
    simp [jacobianMatrix, coreOutput, jac3, cpartial, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [h, core_jacobian]

/-- Extend the rational core coefficients to K. -/
def coreOutputK (K : Type*) [Field K] [CharZero K] (i : CoreVar) :
    MvPolynomial CoreVar K := MvPolynomial.map (algebraMap ℚ K) (coreOutput i)

/-- The normalized core has determinant one over every characteristic-zero field. -/
theorem core_det_charZero (K : Type*) [Field K] [CharZero K] :
    Matrix.det (fun i j : CoreVar => MvPolynomial.pderiv j (coreOutputK K i)) = 1 := by
  calc
    Matrix.det (fun i j : CoreVar => MvPolynomial.pderiv j (coreOutputK K i))
        = (jacobianMatrix.map (MvPolynomial.map (algebraMap ℚ K))).det := by
            congr 1
            ext i j
            simp only [coreOutputK, Matrix.map_apply, jacobianMatrix,
              MvPolynomial.pderiv_map]
    _ = (MvPolynomial.map (algebraMap ℚ K)) jacobianMatrix.det :=
          (RingHom.map_det _ _).symm
    _ = 1 := by rw [core_det_rational, map_one]

/-- All coefficients of the residual two-form Θ in basis (dx,dy,dβ). -/
def residualForm : Matrix CoreVar CoreVar CoreP :=
  !![0,A1,A2; -A1,0,A3; -A2,-A3,0]

/-- Swapping coordinate indices changes the wedge coefficient sign. -/
theorem wedge_skew (f g : CoreP) (i j : CoreVar) :
    wedgeCoeff f g i j = -wedgeCoeff f g j i := by
  dsimp [wedgeCoeff]
  ring

@[simp] theorem wedge_self (f g : CoreP) (i : CoreVar) : wedgeCoeff f g i i = 0 := by
  simp [wedgeCoeff]

/-- All coefficients of dr∧dh+dt∧ds equal the coefficients of Θ. -/
theorem coefficient_identity_matrix (i j : CoreVar) :
    wedgeCoeff r h i j + wedgeCoeff t s i j = residualForm i j := by
  obtain ⟨h01,h02,h12⟩ := coefficient_identity
  have h10 : wedgeCoeff r h 1 0 + wedgeCoeff t s 1 0 = -A1 := by
    rw [wedge_skew r h 1 0, wedge_skew t s 1 0, ← neg_add, h01]
  have h20 : wedgeCoeff r h 2 0 + wedgeCoeff t s 2 0 = -A2 := by
    rw [wedge_skew r h 2 0, wedge_skew t s 2 0, ← neg_add, h02]
  have h21 : wedgeCoeff r h 2 1 + wedgeCoeff t s 2 1 = -A3 := by
    rw [wedge_skew r h 2 1, wedge_skew t s 2 1, ← neg_add, h12]
  fin_cases i <;> fin_cases j <;> simp [residualForm, h01,h02,h12,h10,h20,h21]

end
end Core
end RankTwoPoisson
