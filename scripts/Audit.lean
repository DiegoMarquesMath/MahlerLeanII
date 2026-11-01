import MahlerLeanII
import Lean.Util.CollectAxioms

/- Audit every declaration in the project namespace, not just the final wrappers. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let required : Array Lean.Name := #[
    `MahlerLeanII.rational_scaleApproximable,
    `MahlerLeanII.liouville_of_scaleApproximable_of_irrational,
    `MahlerLeanII.scaleApproximable_rationalOrLiouville,
    `MahlerLeanII.not_approximationAt_iff,
    `MahlerLeanII.not_scaleApproximable_iff,
    `MahlerLeanII.Reconstruction.kernel_trivial,
    `MahlerLeanII.Reconstruction.polynomial_map_injective,
    `MahlerLeanII.Reconstruction.relation_natDegree_le,
    `MahlerLeanII.Reconstruction.relation_eq_zero_of_samples,
    `MahlerLeanII.Reconstruction.kernel_trivial_of_samples,
    `MahlerLeanII.Reconstruction.evaluation_matrix_factorization,
    `MahlerLeanII.Reconstruction.evaluation_det_factorization,
    `MahlerLeanII.Reconstruction.evaluation_det_ne_zero,
    `MahlerLeanII.Reconstruction.divided_evaluation_det_factorization,
    `MahlerLeanII.Reconstruction.bounded_polynomial_map_apply,
    `MahlerLeanII.Reconstruction.bounded_polynomial_map_injective,
    `MahlerLeanII.Reconstruction.bounded_polynomial_map_basis,
    `MahlerLeanII.Reconstruction.reconstruction_family_natDegree_lt,
    `MahlerLeanII.Reconstruction.reconstruction_coefficient_det_ne_zero,
    `MahlerLeanII.Reconstruction.normalized_matrix_eq_divided_evaluation,
    `MahlerLeanII.Reconstruction.normalized_det_factorization,
    `MahlerLeanII.Reconstruction.normalized_det_ne_zero,
    `MahlerLeanII.Reconstruction.reconstruction_determinant_constant,
    `MahlerLeanII.Reconstruction.normalized_system_exact,
    `MahlerLeanII.Reconstruction.determinant_box_bounds,
    `MahlerLeanII.Reconstruction.cramer_of_solution,
    `MahlerLeanII.Reconstruction.common_denominator_of_row_clearing,
    `MahlerLeanII.Reconstruction.normalized_rational_height,
    `MahlerLeanII.Reconstruction.nodeSeparation_pos,
    `MahlerLeanII.Reconstruction.normalized_stability_on_compact,
    `MahlerLeanII.Reconstruction.nodeSeparation_eq,
    `MahlerLeanII.Reconstruction.rational_reconstruction_bounds]
  for name in required do
    unless env.contains name do
      throwError "Required declaration missing: {name}"
  for (name, _) in env.constants.toList do
    if (`MahlerLeanII).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected axioms in {name}: {unexpected}"
      if required.contains name then
        Lean.logInfo m!"AUDITED {name}: {axioms}"
  Lean.logInfo "All project declarations use only the permitted standard axioms."
