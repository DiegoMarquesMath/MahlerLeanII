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
    `MahlerLeanII.Reconstruction.rational_reconstruction_bounds,
    `MahlerLeanII.simultaneous_list,
    `MahlerLeanII.simultaneous_approximation,
    `MahlerLeanII.Counting.twice_pairCount,
    `MahlerLeanII.Counting.farey_vandermonde_lower,
    `MahlerLeanII.Counting.obstructed_scales_exclude_large_blocks,
    `MahlerLeanII.Counting.small_denominator_count,
    `MahlerLeanII.Counting.two_height_count,
    `MahlerLeanII.Escape.point_escape_of_sparse_count,
    `MahlerLeanII.Evaluation.rational_evaluation_control,
    `MahlerLeanII.Evaluation.jointFast_cons,
    `MahlerLeanII.Evaluation.scale_quotient,
    `MahlerLeanII.Evaluation.rationalOrLiouville_of_jointFast,
    `MahlerLeanII.coefficientSubfield,
    `MahlerLeanII.mem_coefficientSubfield,
    `MahlerLeanII.coefficientEmbedding,
    `MahlerLeanII.definedOver_iff_normalized_coefficients,
    `MahlerLeanII.evaluation_of_coefficients,
    `MahlerLeanII.escape_of_bad_coefficients,
    `MahlerLeanII.rational_classification,
    `MahlerLeanII.monomial_rationalOrLiouville,
    `MahlerLeanII.monomial_preserves_of_fiber_free,
    `MahlerLeanII.monomial_preserves_of_nonzero_fibers]
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
