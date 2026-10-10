import DistinctionSelfReference.LocalSufficiency

namespace DistinctionSelfReference
namespace RobustAction

universe u v

/--
A *declared* uncertainty set supports one action if the action meets its
safety predicate in every remaining possible world. No self-reference or
unique world-identification premise is used.
-/
def CommonSafe
    {World : Type u} {Action : Type v}
    (possible : Set World) (safe : World → Action → Prop)
    (action : Action) : Prop :=
  ∀ world, world ∈ possible → safe world action

/-- A common safe action is safe for the actual world if it is represented. -/
theorem safe_for_actual
    {World : Type u} {Action : Type v}
    {possible : Set World} {safe : World → Action → Prop}
    {action : Action} {actual : World}
    (h : CommonSafe possible safe action)
    (hactual : actual ∈ possible) :
    safe actual action :=
  h actual hactual

/-- Additional genuine information cannot destroy an already-common action. -/
theorem survives_information_refinement
    {World : Type u} {Action : Type v}
    {before after : Set World} {safe : World → Action → Prop}
    {action : Action}
    (hsub : after ⊆ before)
    (h : CommonSafe before safe action) :
    CommonSafe after safe action := by
  intro world hw
  exact h world (hsub hw)

/-- Common safety on a union requires safety on *both* possibility sets. -/
theorem commonSafe_union_iff
    {World : Type u} {Action : Type v}
    {left right : Set World} {safe : World → Action → Prop}
    {action : Action} :
    CommonSafe (left ∪ right) safe action ↔
      CommonSafe left safe action ∧ CommonSafe right safe action := by
  constructor
  · intro h
    constructor
    · intro w hw
      exact h w (Or.inl hw)
    · intro w hw
      exact h w (Or.inr hw)
  · intro h w hw
    rcases hw with hl | hr
    · exact h.1 w hl
    · exact h.2 w hr

/--
Different possible worlds can share a safe decision without any observation
that distinguishes them. Thus universal world-identification is not necessary
for this limited form of decision sufficiency.
-/
theorem common_action_without_world_identification :
    CommonSafe (Set.univ : Set Bool)
      (fun (_ : Bool) (a : Bool) => a = false) false := by
  intro world _
  rfl

/--
Not every information state supports a safe common action. Two possible
worlds with disjoint admissible actions provide a concrete obstruction.
-/
theorem incompatible_boolean_worlds_no_common_action :
    ¬ ∃ a : Bool, CommonSafe (Set.univ : Set Bool)
      (fun w choice : Bool => w = choice) a := by
  rintro ⟨a, ha⟩
  have hf : false = a := ha false (Set.mem_univ false)
  have ht : true = a := ha true (Set.mem_univ true)
  exact Bool.false_ne_true (hf.trans ht.symm)

end RobustAction
end DistinctionSelfReference
