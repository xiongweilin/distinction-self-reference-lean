import DistinctionSelfReference.InformationOrder

namespace DistinctionSelfReference
namespace LocalSufficiency

open InformationOrder

universe u v w z

/--
A current observation is sufficient for a commitment requirement when the
required commitment can be computed solely from that observation.
-/
def Sufficient
    {World : Type u} {Obs : Type v} {Choice : Type w}
    (observe : World → Obs)
    (required : World → Choice) : Prop :=
  Refines observe required

/--
An ambiguity witness: two reality states look identical now but require
different commitments.
-/
def Ambiguous
    {World : Type u} {Obs : Type v} {Choice : Type w}
    (observe : World → Obs)
    (required : World → Choice) : Prop :=
  ∃ x y, observe x = observe y ∧ required x ≠ required y

/-- Sufficiency rules out every commitment-relevant ambiguity. -/
theorem sufficient_not_ambiguous
    {World : Type u} {Obs : Type v} {Choice : Type w}
    {observe : World → Obs} {required : World → Choice}
    (h : Sufficient observe required) :
    ¬ Ambiguous observe required := by
  rintro ⟨x, y, hobs, hchoice⟩
  exact hchoice (equality_preserved_by_postprocessing h hobs)

/-- Any ambiguity witness certifies current insufficiency. -/
theorem ambiguous_not_sufficient
    {World : Type u} {Obs : Type v} {Choice : Type w}
    {observe : World → Obs} {required : World → Choice}
    (h : Ambiguous observe required) :
    ¬ Sufficient observe required := by
  intro hs
  exact sufficient_not_ambiguous hs h

/--
More informative observations preserve sufficiency: if coarse is obtained by
post-processing fine and coarse already determines the required commitment,
then fine determines it as well.
-/
theorem finer_preserves_sufficiency
    {World : Type u} {Fine : Type v} {Coarse : Type w} {Choice : Type z}
    {fine : World → Fine} {coarse : World → Coarse}
    {required : World → Choice}
    (hfc : Refines fine coarse)
    (hcr : Sufficient coarse required) :
    Sufficient fine required := by
  exact refines_trans hfc hcr

/-- A fully distinguishing representation is sufficient for its own choice map. -/
theorem identity_sufficient
    {World : Type u}
    (required : World → World) :
    Sufficient (fun x : World => x) required := by
  exact ⟨required, rfl⟩

/-- The minimal ambiguity example: constant observation, different required choices. -/
def constantObservation : Bool → Unit := fun _ => Unit.unit

def requiredBoolChoice : Bool → Bool := fun b => b

theorem constantObservation_ambiguous :
    Ambiguous constantObservation requiredBoolChoice := by
  refine ⟨false, true, rfl, ?_⟩
  change false ≠ true
  exact Bool.false_ne_true

theorem constantObservation_insufficient :
    ¬ Sufficient constantObservation requiredBoolChoice :=
  ambiguous_not_sufficient constantObservation_ambiguous

/--
Restoring the lost distinction makes the same commitment requirement
sufficient without changing the requirement itself.
-/
theorem identityObservation_sufficient :
    Sufficient (fun b : Bool => b) requiredBoolChoice := by
  exact refines_refl requiredBoolChoice

/--
Thus a strict information loss can change a sufficient commitment boundary
into an insufficient one.
-/
theorem information_loss_can_destroy_sufficiency :
    Refines (fun b : Bool => b) constantObservation ∧
      Sufficient (fun b : Bool => b) requiredBoolChoice ∧
      ¬ Sufficient constantObservation requiredBoolChoice := by
  exact ⟨identity_refines_constant Unit.unit,
    identityObservation_sufficient, constantObservation_insufficient⟩

end LocalSufficiency
end DistinctionSelfReference
