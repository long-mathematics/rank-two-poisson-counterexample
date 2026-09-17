import RankTwoPoisson.Symplectic

/-!
# Source-coordinate algebra equivalences

The polynomial maps Ψ₀=(x,y,β,D₀) and Ψ=(x,y,β,D) are represented
contravariantly by their substitution algebra equivalences. Their inverses,
core substitution, algebraic independence, and full Jacobian determinants are
proved over every characteristic-zero field.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RankTwoPoisson
namespace SourceCoordinates
open MvPolynomial
noncomputable section

def sourceTuple : Var → P := ![x,y,beta,D0]
def inverseTuple : Var → P := ![x,Qs,pInv,zInv]
def sourceHom : P →ₐ[ℚ] P := aeval sourceTuple
def inverseHom : P →ₐ[ℚ] P := aeval inverseTuple

theorem inverse_source : inverseHom.comp sourceHom = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, sourceHom, inverseHom, aeval_X, AlgHom.id_apply]
  fin_cases i
  · simp [sourceTuple, inverseTuple, x]
  · change aeval inverseTuple y = q
    convert yBack_eq using 1
    simp [yBack, betaBack, y, beta, B, a, rat, x, q, p, z, inverseTuple]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]
  · change aeval inverseTuple beta = p
    convert betaBack_eq using 1
    simp [betaBack, beta, B, a, rat, x, q, p, z, inverseTuple]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]
  · change aeval inverseTuple D0 = z
    convert D0Back_eq using 1
    simp [D0Back, D0, rat, x, q, p, z, inverseTuple]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]

theorem source_inverse : sourceHom.comp inverseHom = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, sourceHom, inverseHom, aeval_X, AlgHom.id_apply]
  fin_cases i
  · simp [sourceTuple, inverseTuple, x]
  · change aeval sourceTuple Qs = q
    convert Qorig_eq using 1
    simp [Qorig, Qs, sourceTuple, rat, x, q, p]
  · change aeval sourceTuple pInv = p
    convert pRecovered_eq using 1
    simp [pInv, pRecovered, Morig, Qorig, Qs, As, Ms, sourceTuple, rat, x, q, p, z]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]
  · change aeval sourceTuple zInv = z
    convert zRecovered_eq using 1
    simp [zInv, zRecovered, Morig, Qorig, Qs, Cs, Ms, sourceTuple, rat, x, q, p, z]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]

def sourceEquiv : P ≃ₐ[ℚ] P :=
  AlgEquiv.ofAlgHom sourceHom inverseHom source_inverse inverse_source

/-- Embed independent core coordinates as the first three polynomial variables. -/
def coreLift : Core.CoreP →ₐ[ℚ] P := aeval ![x,q,p]
/-- Substitute the actual source coordinates into the independent core. -/
def coreSubst : Core.CoreP →ₐ[ℚ] P := aeval ![x,y,beta]

theorem core_substitution :
    coreSubst Core.r = R ∧ coreSubst Core.t = T ∧
    coreSubst Core.s = S ∧ coreSubst Core.h = H := by
  simp [coreSubst, Core.r, Core.t, Core.s, Core.h, Core.U, Core.crat,
    Core.Xc, Core.Yc, Core.Wc, R, T, S, H, u, rat]

theorem source_coreLift (f : Core.CoreP) : sourceHom (coreLift f) = coreSubst f := by
  rw [coreLift, MvPolynomial.comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coreSubst, sourceHom, sourceTuple, x, q, p]

def shear (c : ℚ) : P →ₐ[ℚ] P := aeval ![x,q,p,z + rat c * coreLift Core.h]

theorem shear_coreLift (c : ℚ) (f : Core.CoreP) : shear c (coreLift f) = coreLift f := by
  rw [coreLift, MvPolynomial.comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shear, x, q, p]

theorem shear_X (c : ℚ) (i : Var) :
    shear c (X i) = ![x,q,p,z + rat c * coreLift Core.h] i := by simp [shear]

theorem shear_comp (c d : ℚ) : (shear c).comp (shear d) = shear (c+d) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, shear_X]
  fin_cases i <;>
    simp [x, q, p, z, rat, map_add, map_mul, shear_X, shear_coreLift, add_mul]
  ring

theorem shear_zero : shear 0 = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shear, x, q, p, z, rat]

def shearEquiv : P ≃ₐ[ℚ] P := AlgEquiv.ofAlgHom (shear 1) (shear (-1))
  (by rw [shear_comp]; norm_num; exact shear_zero)
  (by rw [shear_comp]; norm_num; exact shear_zero)

def correctedEquiv : P ≃ₐ[ℚ] P := shearEquiv.trans sourceEquiv

theorem source_X (i : Var) : sourceHom (X i) = sourceTuple i := by simp [sourceHom]

theorem correctedEquiv_X (i : Var) : correctedEquiv (X i) = ![x,y,beta,D] i := by
  change sourceHom (shear 1 (X i)) = _
  rw [shear_X]
  fin_cases i <;>
    simp [x, q, p, z, rat, source_X, sourceTuple, source_coreLift,
      core_substitution.2.2.2, D]

variable (K : Type*) [Field K] [CharZero K]

theorem substitution_map (F : Var → P) (f : P) :
    aeval (fun i => mapK K (F i)) (mapK K f) = mapK K (aeval F f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mapK]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, hf]; simp [mapK]

def extendHom (f : P →ₐ[ℚ] P) : MvPolynomial Var K →ₐ[K] MvPolynomial Var K :=
  aeval (fun i => mapK K (f (X i)))

theorem extendHom_map (f : P →ₐ[ℚ] P) (g : P) :
    extendHom K f (mapK K g) = mapK K (f g) := by
  rw [extendHom, substitution_map]
  congr 1
  have h : aeval (fun i => f (X i)) = f := by ext i; simp
  rw [h]

theorem extendHom_comp (f g : P →ₐ[ℚ] P) :
    (extendHom K f).comp (extendHom K g) = extendHom K (f.comp g) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, extendHom, aeval_X]
  exact extendHom_map K f (g (X i))

theorem extendHom_id : extendHom K (AlgHom.id ℚ P) = AlgHom.id K _ := by
  ext i
  simp [extendHom, mapK]

def extendEquiv (e : P ≃ₐ[ℚ] P) : MvPolynomial Var K ≃ₐ[K] MvPolynomial Var K :=
  AlgEquiv.ofAlgHom (extendHom K e.toAlgHom) (extendHom K e.symm.toAlgHom)
    (by rw [extendHom_comp, e.comp_symm]; exact extendHom_id K)
    (by rw [extendHom_comp, e.symm_comp]; exact extendHom_id K)

/-- Independent core substitution after coefficient extension. -/
def coreSubstK : MvPolynomial Core.CoreVar K →ₐ[K] MvPolynomial Var K :=
  aeval (fun i => mapK K (![x,y,beta] i))

theorem coreSubstK_map (f : Core.CoreP) :
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) f) = mapK K (coreSubst f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [coreSubstK, coreSubst, mapK]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, hf]; simp [coreSubstK, coreSubst]

theorem core_substitution_charZero :
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.r) = mapK K R ∧
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.t) = mapK K T ∧
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.s) = mapK K S ∧
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.h) = mapK K H := by
  simp only [coreSubstK_map, core_substitution.1, core_substitution.2.1,
    core_substitution.2.2.1, core_substitution.2.2.2, and_self]

/-- Source-coordinate automorphism over every characteristic-zero field. -/
def sourceEquivK := extendEquiv K sourceEquiv
/-- Corrected source-coordinate automorphism over every characteristic-zero field. -/
def correctedEquivK := extendEquiv K correctedEquiv

theorem sourceEquivK_X (i : Var) : sourceEquivK K (X i) = mapK K (sourceTuple i) := by
  simp [sourceEquivK, extendEquiv, extendHom, sourceEquiv, source_X]

theorem sourceEquivK_symm_X (i : Var) :
    (sourceEquivK K).symm (X i) = mapK K (inverseTuple i) := by
  simp [sourceEquivK, extendEquiv, extendHom, sourceEquiv, inverseHom]

theorem correctedEquivK_X (i : Var) :
    correctedEquivK K (X i) = mapK K (![x,y,beta,D] i) := by
  simp [correctedEquivK, extendEquiv, extendHom, correctedEquiv_X]

/-- The first three source coordinates are algebraically independent. -/
theorem source_algebraicIndependent :
    AlgebraicIndependent K (fun i : Fin 3 => mapK K (![x,y,beta] i)) := by
  have h := (MvPolynomial.algebraicIndependent_X Var K).map'
    (f := (sourceEquivK K).toAlgHom) (sourceEquivK K).injective
  have h' := h.comp (fun i : Fin 3 => i.castSucc) (Fin.castSucc_injective 3)
  convert h' using 1
  funext i
  fin_cases i <;> simp [Function.comp_def, sourceEquivK_X, sourceTuple]

/-- The full source Jacobian, in order (x,q,p,z), has determinant minus one. -/
theorem source_det_rational :
    Matrix.det (fun i j : Var => pderiv j (sourceTuple i)) = -1 := by
  rw [Symplectic.det_pair]
  apply MvPolynomial.funext
  intro v
  simp [Symplectic.pair, sourceTuple, y, beta, B, a, D0, rat, x, q, p, z]
  ring

/-- Explicit corrected inverse: replace the fourth independent coordinate by D-H. -/
theorem correctedEquivK_symm_X (i : Var) :
    (correctedEquivK K).symm (X i) = mapK K
      (aeval ![x,q,p,z - coreLift Core.h] (inverseTuple i)) := by
  simp [correctedEquivK, extendEquiv, extendHom, correctedEquiv,
    shearEquiv, sourceEquiv, inverseHom, shear, rat, sub_eq_add_neg]

/-- The correction shear does not change the source determinant. -/
theorem corrected_det_rational :
    Matrix.det (fun i j : Var => pderiv j (![x,y,beta,D] i)) = -1 := by
  rw [Symplectic.det_pair]
  apply MvPolynomial.funext
  intro v
  simp [Symplectic.pair, D, H, u, y, beta, B, a, D0, rat, x, q, p, z]
  ring

/-- Coefficient extension commutes with the full formal Jacobian determinant. -/
theorem jacobian_det_map (F : Var → P) :
    Matrix.det (fun i j => pderiv j (mapK K (F i))) =
      mapK K (Matrix.det (fun i j => pderiv j (F i))) := by
  calc
    _ = Matrix.det (Matrix.map (fun i j : Var => pderiv j (F i)) (mapK K)) := by
      congr 1
      funext i j
      simp only [Matrix.map_apply, mapK, MvPolynomial.pderiv_map]
    _ = _ := (RingHom.map_det _ _).symm

theorem source_det_charZero :
    Matrix.det (fun i j => pderiv j (mapK K (sourceTuple i))) = -1 := by
  rw [jacobian_det_map, source_det_rational, map_neg, map_one]

theorem corrected_det_charZero :
    Matrix.det (fun i j => pderiv j (mapK K (![x,y,beta,D] i))) = -1 := by
  rw [jacobian_det_map, corrected_det_rational, map_neg, map_one]

end
end SourceCoordinates
end RankTwoPoisson
