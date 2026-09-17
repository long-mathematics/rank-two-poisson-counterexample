import RankTwoPoisson.SourceEquivalence

/-!
# The induced Jacobian Poisson bracket

The bracket on all polynomials in the independent core coordinates equals
the negative Jacobian determinant. Core substitution identifies it with the
ambient bracket over every characteristic-zero field, and R is a Casimir.
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace Induced
open MvPolynomial
noncomputable section

theorem generators_rational :
    bracket x y = x^3 ∧ bracket x beta = -3*x^2 ∧
      bracket y beta = -2 + 6*x*y + 3*x^2*beta := by
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [bracket, polyDeriv, y, beta, B, a, rat, x, q, p, z]
    ring
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [bracket, polyDeriv, beta, B, a, rat, x, q, p, z]
  · apply MvPolynomial.funext
    intro v
    simp [bracket, polyDeriv, y, beta, B, a, rat, x, q, p, z]
    ring

private theorem pderiv_two {σ R : Type*} [CommRing R] [DecidableEq σ] (i : σ) :
    pderiv i (2 : MvPolynomial σ R) = 0 := (pderiv i).map_natCast 2

private theorem pderiv_three {σ R : Type*} [CommRing R] [DecidableEq σ] (i : σ) :
    pderiv i (3 : MvPolynomial σ R) = 0 := (pderiv i).map_natCast 3

variable (K : Type*) [Field K]
abbrev CP := MvPolynomial (Fin 3) K

def wedge (f g : CP K) (i j : Fin 3) := pderiv i f * pderiv j g - pderiv j f * pderiv i g

def bracket3 (f g : CP K) : CP K :=
    (X 0)^3 * wedge K f g 0 1 - 3*(X 0)^2 * wedge K f g 0 2 +
    (-2 + 6*X 0*X 1 + 3*(X 0)^2*X 2) * wedge K f g 1 2

theorem add_left (f g h : CP K) : bracket3 K (f+g) h = bracket3 K f h + bracket3 K g h := by
  simp [bracket3, wedge]; ring

theorem add_right (f g h : CP K) : bracket3 K f (g+h) = bracket3 K f g + bracket3 K f h := by
  simp [bracket3, wedge]; ring

theorem mul_left (f g h : CP K) : bracket3 K (f*g) h = f*bracket3 K g h + g*bracket3 K f h := by
  simp [bracket3, wedge]; ring

theorem mul_right (f g h : CP K) : bracket3 K f (g*h) = g*bracket3 K f h + h*bracket3 K f g := by
  simp [bracket3, wedge]; ring

@[simp] theorem C_left (c : K) (f : CP K) : bracket3 K (C c) f = 0 := by simp [bracket3, wedge]
@[simp] theorem C_right (f : CP K) (c : K) : bracket3 K f (C c) = 0 := by simp [bracket3, wedge]

def r3 : CP K := C 2*X 0 - C 3*(X 0)^2*X 1 - (X 0)^3*X 2

/-- The induced bracket is the negative Jacobian determinant in order (x,y,β). -/
theorem determinant_formula (f g : CP K) :
    bracket3 K f g = - Matrix.det (fun i j : Fin 3 => pderiv j (![r3 K,f,g] i)) := by
  rw [Matrix.det_fin_three]
  simp [bracket3, wedge, r3, map_ofNat, pderiv_two, pderiv_three]
  ring

theorem casimir (f : CP K) : bracket3 K (r3 K) f = 0 := by
  simp [bracket3, wedge, r3, map_ofNat, pderiv_two, pderiv_three]
  ring

variable [CharZero K]
open SourceCoordinates

theorem source_generators (i j : Fin 3) :
    bracketK K (coreSubstK K (X i)) (coreSubstK K (X j)) =
      coreSubstK K (bracket3 K (X i) (X j)) := by
  have hxy : bracketK K (mapK K x) (mapK K y) = (mapK K x)^3 := by
    rw [bracket_mapK, generators_rational.1, map_pow]
  have hxb : bracketK K (mapK K x) (mapK K beta) = -3*(mapK K x)^2 := by
    rw [bracket_mapK, generators_rational.2.1]
    simp only [map_mul, map_neg, map_ofNat, map_pow]
  have hyb : bracketK K (mapK K y) (mapK K beta) =
      -2 + 6*(mapK K x)*(mapK K y) + 3*(mapK K x)^2*(mapK K beta) := by
    rw [bracket_mapK, generators_rational.2.2]
    simp only [map_add, map_mul, map_neg, map_ofNat, map_pow]
  have hyx := Symplectic.bracket_skewK K (mapK K y) (mapK K x)
  have hbx := Symplectic.bracket_skewK K (mapK K beta) (mapK K x)
  have hby := Symplectic.bracket_skewK K (mapK K beta) (mapK K y)
  fin_cases i <;> fin_cases j <;>
    simp [coreSubstK, bracket3, wedge, hxy, hxb, hyb, hyx, hbx, hby,
      Symplectic.bracket_selfK, map_ofNat]

/-- Restriction of the ambient bracket to the full source-coordinate subalgebra. -/
theorem source_bracket (f g : CP K) :
    bracketK K (coreSubstK K f) (coreSubstK K g) = coreSubstK K (bracket3 K f g) := by
  have hg (i : Fin 3) (f : CP K) :
      bracketK K (coreSubstK K f) (coreSubstK K (X i)) = coreSubstK K (bracket3 K f (X i)) := by
    induction f using MvPolynomial.induction_on with
    | C c => simp [coreSubstK]
    | add f g hf hg => simp only [map_add, bracketK_add_left, add_left]; rw [hf,hg]
    | mul_X f j hf =>
      simp only [map_mul, map_add, bracketK_mul_left, mul_left]
      rw [source_generators, hf]
  induction g using MvPolynomial.induction_on with
  | C c => simp [coreSubstK]
  | add g h hg hh => simp only [map_add, bracketK_add_right, add_right]; rw [hg,hh]
  | mul_X g j h =>
    simp only [map_mul, map_add, bracketK_mul_right, mul_right]
    rw [hg, h]

/-- Full statement of the induced negative-Jacobian formula for arbitrary core polynomials. -/
theorem source_bracket_determinant (f g : CP K) :
    bracketK K (coreSubstK K f) (coreSubstK K g) =
      -coreSubstK K (Matrix.det (fun i j : Fin 3 => pderiv j (![r3 K,f,g] i))) := by
  rw [source_bracket, determinant_formula, map_neg]

/-- The independently defined core R is the coefficient extension of Core.r. -/
theorem r3_map : r3 K = MvPolynomial.map (algebraMap ℚ K) Core.r := by
  simp [r3, Core.r, Core.crat, Core.Xc, Core.Yc, Core.Wc, map_ofNat]

theorem source_casimir (f : CP K) : bracketK K (mapK K R) (coreSubstK K f) = 0 := by
  have hr : coreSubstK K (r3 K) = mapK K R := by
    rw [r3_map]; exact (core_substitution_charZero K).1
  rw [← hr, source_bracket, casimir, map_zero]

theorem D0_R_rational : bracket D0 R = 1 := by
  rw [R_factorization]
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D0, rat, x, q, p, z, pderiv_two, pderiv_three]
  ring

theorem H_R_charZero : bracketK K (mapK K H) (mapK K R) = 0 := by
  rw [Symplectic.bracket_skewK]
  have h := source_casimir K (MvPolynomial.map (algebraMap ℚ K) Core.h)
  rw [(core_substitution_charZero K).2.2.2] at h
  rw [h, neg_zero]

theorem D0_R_charZero : bracketK K (mapK K D0) (mapK K R) = 1 := by
  rw [bracket_mapK, D0_R_rational, map_one]

/-- The first-coordinate simplification after coefficient extension. -/
theorem R_factorization_charZero :
    mapK K R = mapK K x * (2-3*mapK K x*mapK K q) := by
  rw [R_factorization]
  simp only [map_mul, map_sub, map_ofNat]

/-- Ambient derivatives and bracket used to derive the induced generators. -/
theorem ambient_support :
    pderiv 2 beta = 3*x^2 ∧ pderiv 3 beta = 2*(1-3*x*q) ∧
      bracket q beta = -2+6*x*q := by
  refine ⟨?_,?_,?_⟩ <;> apply MvPolynomial.funext <;> intro v <;>
    simp [bracket,polyDeriv,beta,B,a,rat,x,q,p,z]
  ring

end
end Induced
end RankTwoPoisson
