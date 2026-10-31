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
    `MahlerLeanII.not_scaleApproximable_iff]
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
        logInfo m!"AUDITED {name}: {axioms}"
  logInfo "All project declarations use only the permitted standard axioms."
