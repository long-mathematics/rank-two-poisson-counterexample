import RankTwoPoisson
import Lean.Util.CollectAxioms

/-!
Audit all constants originating in mathematical project modules, including
private/generated declarations and declarations outside the public namespace.
The allowed foundations do not certify correspondence with the manuscript.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut modules : Nat := 0
  for moduleName in env.header.moduleNames do
    if (`RankTwoPoisson).isPrefixOf moduleName then
      modules := modules + 1
  unless modules > 1 do
    throwError "No mathematical project modules imported"
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => (`RankTwoPoisson).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if owned then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      match info with
      | .axiomInfo _ => throwError "Project-added axiom: {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  unless declarations > 0 ∧ theorems > 0 do
    throwError "Empty declaration audit"
  logInfo m!"Axiom audit passed: {modules} modules, {declarations} declarations, {theorems} theorem constants."
  logInfo "All transitive dependencies lie in {propext, Classical.choice, Quot.sound}."

#print axioms RankTwoPoisson.explicit_counterexample
#print axioms RankTwoPoisson.explicit_counterexample_complex
#print axioms RankTwoPoisson.explicit_counterexample_charZero
#print axioms RankTwoPoisson.SourceCoordinates.two_sided_inverse_certificate
#print axioms RankTwoPoisson.Core.coefficient_identity
#print axioms RankTwoPoisson.Core.core_jacobian

#print axioms RankTwoPoisson.Fiber.exact_fiber_charZero
#print axioms RankTwoPoisson.Fiber.exact_fiber_complex
#print axioms RankTwoPoisson.Fiber.exact_fiber_rational

#print axioms RankTwoPoisson.Symplectic.criterion_complex
#print axioms RankTwoPoisson.Symplectic.output_det
#print axioms RankTwoPoisson.Symplectic.output_symplectic
#print axioms RankTwoPoisson.Symplectic.main_complex

#print axioms RankTwoPoisson.Core.core_det_charZero
#print axioms RankTwoPoisson.Core.coefficient_identity_matrix

#print axioms RankTwoPoisson.SourceCoordinates.sourceEquivK
#print axioms RankTwoPoisson.SourceCoordinates.correctedEquivK
#print axioms RankTwoPoisson.SourceCoordinates.source_algebraicIndependent
#print axioms RankTwoPoisson.SourceCoordinates.source_det_charZero
#print axioms RankTwoPoisson.SourceCoordinates.corrected_det_charZero
#print axioms RankTwoPoisson.Calculus.jacobi
#print axioms RankTwoPoisson.Calculus.hamiltonian_commutator
