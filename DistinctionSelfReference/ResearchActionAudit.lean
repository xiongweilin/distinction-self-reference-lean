import DistinctionSelfReference

/-!
# Action-first research axiom audit (outside v1.0 freeze)

These names are additive research claims. Elaborating and listing axioms
does not certify model completeness, deployment safety or the v1.0 release.
The frozen `FreezeAudit.lean` remains byte-for-byte unchanged.
-/

#print axioms DistinctionSelfReference.RobustAction.safe_for_actual
#print axioms DistinctionSelfReference.RobustAction.survives_information_refinement
#print axioms DistinctionSelfReference.RobustAction.commonSafe_union_iff
#print axioms DistinctionSelfReference.RobustAction.common_action_without_world_identification
#print axioms DistinctionSelfReference.RobustAction.incompatible_boolean_worlds_no_common_action
#print axioms DistinctionSelfReference.RobustAction.omitted_actual_state_can_invalidate_safety
