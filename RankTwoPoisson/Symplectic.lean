import RankTwoPoisson.ExactFiber

/-!
# The four - dimensional symplectic criterion and Jacobian

Source columns are ordered (x,q,p,z), output rows (R,T,D,S). The matrix omega
represents dx∧dp+dq∧dz, while its inverse -omega represents the bracket.
All coefficient equalities are identities of multivariate polynomials.
The determinant formula is proved directly over any commutative coefficient
ring; it yields +1, without passing through a determinant-squared equation.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson
namespace Symplectic
open Matrix
variable {A : Type*} [CommRing A]

/-- The alternating matrix for dx∧dp+dq∧dz in order (x,q,p,z). -/
def omega : Matrix (Fin 4) (Fin 4) A :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0,-1, 0, 0]

/-- Contraction of two row vectors with the canonical bracket matrix -omega. -/
def pair (u v : Fin 4 → A) : A := u 2 * v 0 - u 0 * v 2 + u 3 * v 1 - u 1 * v 3

/-- The inverse of the symplectic matrix is its negative. -/
theorem omega_mul_neg : (omega : Matrix (Fin 4) (Fin 4) A) * (-omega) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [omega, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The inverse identity in the opposite order. -/
theorem neg_mul_omega : -(omega : Matrix (Fin 4) (Fin 4) A) * omega = 1 := by
  rw [neg_mul, ← Matrix.mul_neg, omega_mul_neg]

/-- For square matrices over a commutative ring, preservation of a dual form implies preservation of the form. -/
theorem conjugate_imp (J U V : Matrix (Fin 4) (Fin 4) A)
    (huv : U * V = 1) (hvu : V * U = 1) (h : J * V * J.transpose = V) :
    J.transpose * U * J = U := by
  have hr : J * (V * J.transpose * U) = 1 := by
    calc
      J * (V * J.transpose * U) = (J * V * J.transpose) * U := by simp [Matrix.mul_assoc]
      _ = V * U := by rw [h]
      _ = 1 := hvu
  have hl : (V * J.transpose * U) * J = 1 := mul_eq_one_comm.mp hr
  calc
    J.transpose * U * J = U * ((V * J.transpose * U) * J) := by simp [← Matrix.mul_assoc, huv]
    _ = U := by rw [hl, Matrix.mul_one]

/-- Equivalent primal and dual matrix equations, with both inverse identities explicit. -/
theorem conjugate_iff (J U V : Matrix (Fin 4) (Fin 4) A)
    (huv : U * V = 1) (hvu : V * U = 1) :
    J * V * J.transpose = V ↔ J.transpose * U * J = U := by
  constructor
  · exact conjugate_imp J U V huv hvu
  · intro h
    simpa only [transpose_transpose] using conjugate_imp J.transpose V U hvu huv h

/-- Entries of J(-omega)Jᵀ are the generator bracket contractions. -/
theorem bracket_matrix (J : Matrix (Fin 4) (Fin 4) A) (i j : Fin 4) :
    (J * (-omega) * J.transpose : Matrix (Fin 4) (Fin 4) A) i j = pair (J i) (J j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, omega, pair]
  ring

/-- The 4×4 determinant expressed through the six alternating row contractions. -/
theorem det_pair (J : Matrix (Fin 4) (Fin 4) A) :
    J.det = pair (J 2) (J 0) * pair (J 3) (J 1) -
      pair (J 0) (J 1) * pair (J 2) (J 3) +
      pair (J 0) (J 3) * pair (J 2) (J 1) := by
  have h1 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have h2 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have h3 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := rfl
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, pair, h1, h2, h3]
  ring


/-- Entries of Jᵀ omega J are the coefficients of the pulled-back two-form. -/
theorem form_entry (J : Matrix (Fin 4) (Fin 4) A) (i j : Fin 4) :
    (J.transpose * omega * J : Matrix (Fin 4) (Fin 4) A) i j =
    J 0 i * J 2 j - J 2 i * J 0 j + J 1 i * J 3 j - J 3 i * J 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, omega]
  ring

section Polynomials
variable (K : Type*) [Field K] [CharZero K]

/-- Rows are outputs; columns are source coordinates (x,q,p,z). -/
noncomputable def jacobian (F : Var → MvPolynomial Var K) : Matrix Var Var (MvPolynomial Var K) :=
  fun i j => MvPolynomial.pderiv j (F i)

omit [CharZero K] in
/-- The row contraction is exactly the established polynomial bracket convention. -/
theorem jacobian_pair (F : Var → MvPolynomial Var K) (i j : Var) :
    pair (jacobian K F i) (jacobian K F j) = bracketK K (F i) (F j) := rfl


/-- Generator preservation extends to all polynomials by two polynomial inductions. -/
theorem preserves_of_generators (φ : MvPolynomial Var K →ₐ[K] MvPolynomial Var K)
    (h : ∀ i j : Var, bracketK K (φ (MvPolynomial.X i)) (φ (MvPolynomial.X j)) =
      φ (bracketK K (MvPolynomial.X i) (MvPolynomial.X j))) : IsPoissonK K φ := by
  have hright (i : Var) (f : MvPolynomial Var K) :
      bracketK K (φ f) (φ (MvPolynomial.X i)) = φ (bracketK K f (MvPolynomial.X i)) := by
    refine MvPolynomial.induction_on
      (motive := fun f : MvPolynomial Var K =>
        bracketK K (φ f) (φ (MvPolynomial.X i)) = φ (bracketK K f (MvPolynomial.X i)))
      f ?_ ?_ ?_
    · intro c
      simp
    · intro f g hf hg
      simp only [map_add, bracketK_add_left]
      exact congrArg₂ (· + ·) hf hg
    · intro f j hf
      simp only [map_mul, map_add, bracketK_mul_left]
      rw [h, hf]
  intro f g
  refine MvPolynomial.induction_on
    (motive := fun g : MvPolynomial Var K =>
      bracketK K (φ f) (φ g) = φ (bracketK K f g))
    g ?_ ?_ ?_
  · intro c
    simp
  · intro g h hg hh
    simp only [map_add, bracketK_add_right]
    exact congrArg₂ (· + ·) hg hh
  · intro g j hg
    simp only [map_mul, map_add, bracketK_mul_right]
    rw [hright, hg]

/-- For arbitrary outputs, preservation on all polynomials is equivalent to the canonical generator matrix. -/
theorem poisson_iff_canonical (F : Var → MvPolynomial Var K) :
    IsPoissonK K (MvPolynomial.aeval F) ↔
    ∀ i j : Var, bracketK K (F i) (F j) = MvPolynomial.C (canonicalMatrixK K i j) := by
  constructor
  · intro h i j
    have hi := h (MvPolynomial.X i) (MvPolynomial.X j)
    simpa [bracketK_X_X] using hi
  · intro h
    apply preserves_of_generators
    intro i j
    simpa [bracketK_X_X] using h i j

/-- The generator relations are exactly the dual symplectic matrix identity. -/
theorem canonical_iff_matrix (F : Var → MvPolynomial Var K) :
    (∀ i j : Var, bracketK K (F i) (F j) = MvPolynomial.C (canonicalMatrixK K i j)) ↔
    jacobian K F * (-omega) * (jacobian K F).transpose = -omega := by
  have heq (i j : Var) :
      MvPolynomial.C (canonicalMatrixK K i j) =
        (-omega : Matrix Var Var (MvPolynomial Var K)) i j := by
    fin_cases i <;> fin_cases j <;> norm_num [omega, canonicalMatrixK, canonicalMatrix]
  constructor
  · intro h
    ext i j
    rw [bracket_matrix, jacobian_pair, h, heq]
  · intro h i j
    rw [heq]
    have hi := congrFun (congrFun h i) j
    rwa [bracket_matrix, jacobian_pair] at hi

/-- The general symplectic criterion over a characteristic-zero field. -/
theorem poisson_iff_symplectic (F : Var → MvPolynomial Var K) :
    IsPoissonK K (MvPolynomial.aeval F) ↔
    (jacobian K F).transpose * omega * jacobian K F = omega := by
  rw [poisson_iff_canonical, canonical_iff_matrix]
  exact conjugate_iff _ _ _ omega_mul_neg neg_mul_omega


/-- Every bracket-preserving four-variable polynomial substitution has determinant one. -/
theorem det_of_poisson (F : Var → MvPolynomial Var K)
    (h : IsPoissonK K (MvPolynomial.aeval F)) : (jacobian K F).det = 1 := by
  rw [det_pair]
  simp only [jacobian_pair, (poisson_iff_canonical K F).mp h]
  norm_num [canonicalMatrixK, canonicalMatrix, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

omit [CharZero K] in
/-- Skew symmetry of the canonical bracket. -/
theorem bracket_skewK (f g : MvPolynomial Var K) :
    bracketK K f g = -bracketK K g f := by
  dsimp [bracketK]
  ring

omit [CharZero K] in
@[simp] theorem bracket_selfK (f : MvPolynomial Var K) : bracketK K f f = 0 := by
  dsimp [bracketK]
  ring

/-- The full generator matrix is equivalent to the six displayed manuscript relations. -/
theorem canonical_iff_six (F : Var → MvPolynomial Var K) :
    (∀ i j : Var, bracketK K (F i) (F j) = MvPolynomial.C (canonicalMatrixK K i j)) ↔
    bracketK K (F 2) (F 0) = 1 ∧ bracketK K (F 3) (F 1) = 1 ∧
    bracketK K (F 0) (F 3) = 0 ∧ bracketK K (F 0) (F 1) = 0 ∧
    bracketK K (F 2) (F 3) = 0 ∧ bracketK K (F 2) (F 1) = 0 := by
  constructor
  · intro h
    simp only [h]
    norm_num [canonicalMatrixK, canonicalMatrix, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  · rintro ⟨h20, h31, h03, h01, h23, h21⟩
    have h02 : bracketK K (F 0) (F 2) = -1 := by rw [bracket_skewK, h20]
    have h13 : bracketK K (F 1) (F 3) = -1 := by rw [bracket_skewK, h31]
    have h30 : bracketK K (F 3) (F 0) = 0 := by rw [bracket_skewK, h03, neg_zero]
    have h10 : bracketK K (F 1) (F 0) = 0 := by rw [bracket_skewK, h01, neg_zero]
    have h32 : bracketK K (F 3) (F 2) = 0 := by rw [bracket_skewK, h23, neg_zero]
    have h12 : bracketK K (F 1) (F 2) = 0 := by rw [bracket_skewK, h21, neg_zero]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalMatrixK, canonicalMatrix, h20, h31, h03, h01, h23, h21,
        h02, h13, h30, h10, h32, h12]

/-- The six relations are equivalent to global bracket preservation, not an assumption on the constructed map. -/
theorem poisson_iff_six (F : Var → MvPolynomial Var K) :
    IsPoissonK K (MvPolynomial.aeval F) ↔
    bracketK K (F 2) (F 0) = 1 ∧ bracketK K (F 3) (F 1) = 1 ∧
    bracketK K (F 0) (F 3) = 0 ∧ bracketK K (F 0) (F 1) = 0 ∧
    bracketK K (F 2) (F 3) = 0 ∧ bracketK K (F 2) (F 1) = 0 := by
  rw [poisson_iff_canonical, canonical_iff_six]

/-- The actual output tuple satisfies the dual symplectic equation. -/
theorem output_bracket_matrix :
    jacobian K (outputK K) * (-omega) * (jacobian K (outputK K)).transpose = -omega := by
  ext i j
  rw [bracket_matrix, jacobian_pair, bracketK_outputK_outputK]
  fin_cases i <;> fin_cases j <;> norm_num [omega, canonicalMatrixK, canonicalMatrix]

/-- The actual four-dimensional output Jacobian has determinant one over K. -/
theorem output_det : (jacobian K (outputK K)).det = 1 := by
  rw [det_pair]
  simp only [jacobian_pair, bracketK_outputK_outputK]
  norm_num [canonicalMatrixK, canonicalMatrix, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The actual output tuple preserves the canonical symplectic form. -/
theorem output_symplectic :
    (jacobian K (outputK K)).transpose * omega * jacobian K (outputK K) = omega := by
  exact (conjugate_iff _ _ _ omega_mul_neg neg_mul_omega).mp (output_bracket_matrix K)

/-- Every coefficient of dR∧dD+dT∧dS equals that of dx∧dp+dq∧dz. -/
theorem output_form_coefficients (i j : Var) :
    MvPolynomial.pderiv i (outputK K 0) * MvPolynomial.pderiv j (outputK K 2) -
      MvPolynomial.pderiv i (outputK K 2) * MvPolynomial.pderiv j (outputK K 0) +
      MvPolynomial.pderiv i (outputK K 1) * MvPolynomial.pderiv j (outputK K 3) -
      MvPolynomial.pderiv i (outputK K 3) * MvPolynomial.pderiv j (outputK K 1) =
      (omega : Matrix Var Var (MvPolynomial Var K)) i j := by
  have h := congrFun (congrFun (output_symplectic K) i) j
  rwa [form_entry] at h



/-- The symplectic criterion for arbitrary complex polynomial outputs. -/
theorem criterion_complex (F : Var → PC) :
    IsPoissonC (MvPolynomial.aeval F) ↔
    (jacobian ℂ F).transpose * omega * jacobian ℂ F = omega :=
  poisson_iff_symplectic ℂ F

/-- The six-relation formulation for the manuscript complex polynomial algebra. -/
theorem six_criterion_complex (F : Var → PC) :
    IsPoissonC (MvPolynomial.aeval F) ↔
    bracketC (F 2) (F 0) = 1 ∧ bracketC (F 3) (F 1) = 1 ∧
    bracketC (F 0) (F 3) = 0 ∧ bracketC (F 0) (F 1) = 0 ∧
    bracketC (F 2) (F 3) = 0 ∧ bracketC (F 2) (F 1) = 0 :=
  poisson_iff_six ℂ F

/-- The determinant consequence of the complex symplectic criterion. -/
theorem det_of_poisson_complex (F : Var → PC)
    (h : IsPoissonC (MvPolynomial.aeval F)) : (jacobian ℂ F).det = 1 :=
  det_of_poisson ℂ F h

/-- The four-dimensional determinant assertion for the manuscript complex map. -/
theorem output_det_complex : (jacobian ℂ outputC).det = 1 := output_det ℂ

/-- The symplectic matrix equation for the manuscript complex map. -/
theorem output_symplectic_complex :
    (jacobian ℂ outputC).transpose * omega * jacobian ℂ outputC = omega :=
  output_symplectic ℂ

/-- The determinant assertion for the original rational output polynomials. -/
theorem output_det_rational : (jacobian ℚ output).det = 1 := by
  rw [det_pair]
  change bracket (output 2) (output 0) * bracket (output 3) (output 1) -
    bracket (output 0) (output 1) * bracket (output 2) (output 3) +
    bracket (output 0) (output 3) * bracket (output 2) (output 1) = 1
  simp [output]

/-- All conclusions of the manuscript's main theorem, for its explicit map. -/
theorem main_complex :
    IsPoissonC PhiC ∧ ¬IsAlgAutomorphismC PhiC ∧
    (jacobian ℂ outputC).det = 1 ∧
    (∀ v : Var → ℂ, pointMapC PhiC v = targetC ↔
      v = point0C ∨ v = point1C ∨ v = complexPoint point2) ∧
    point0C ≠ point1C ∧ point0C ≠ complexPoint point2 ∧
    point1C ≠ complexPoint point2 := by
  exact ⟨PhiC_isPoisson, PhiC_not_automorphism, output_det_complex,
    Fiber.exact_fiber_complex, Fiber.fiber_points_distinct⟩

end Polynomials

end Symplectic
end RankTwoPoisson
