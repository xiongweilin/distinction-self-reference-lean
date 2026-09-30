import Mathlib.Logic.Relation
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Card
import DistinctionSelfReference.CapabilityOrder

namespace DistinctionSelfReference
namespace ChangingEvaluator

universe u

/-- A time-local evaluator is only a binary improvement relation. -/
structure Evaluator (State : Type u) where
  better : State → State → Prop

def LocalImprovement
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (trajectory : Nat → State) : Prop :=
  ∀ n, (evaluators n).better (trajectory n) (trajectory (n + 1))

/--
Every local evaluator is coherent with one global relation when all local
improvement edges are also global improvement edges.
-/
def CoherentWithGlobal
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (global : Evaluator State) : Prop :=
  ∀ n a b, (evaluators n).better a b → global.better a b

/--
A common transitive global evaluator composes all local improvements into
endpoint improvement over every finite nonempty prefix.
-/
theorem local_to_global
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (trajectory : Nat → State)
    (global : Evaluator State)
    (hlocal : LocalImprovement evaluators trajectory)
    (hcoherent : CoherentWithGlobal evaluators global)
    (htrans : ∀ ⦃a b c⦄, global.better a b → global.better b c → global.better a c) :
    ∀ n, global.better (trajectory 0) (trajectory (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hcoherent 0 _ _ (hlocal 0)
  | succ n ih =>
      exact htrans ih
        (hcoherent (n + 1) _ _ (hlocal (n + 1)))

/--
A common potential is a stronger numerical coherence witness.
-/
def CommonPotential
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (potential : State → Nat) : Prop :=
  ∀ n a b,
    (evaluators n).better a b →
    potential a < potential b

theorem potential_increases_each_step
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (trajectory : Nat → State)
    (potential : State → Nat)
    (hlocal : LocalImprovement evaluators trajectory)
    (hpotential : CommonPotential evaluators potential) :
    ∀ n, potential (trajectory n) < potential (trajectory (n + 1)) := by
  intro n
  exact hpotential n _ _ (hlocal n)

/--
Any trajectory whatsoever can be made locally improving if the evaluator is
allowed to change adversarially with the trajectory itself.
-/
def pathEvaluator
    {State : Type u}
    (trajectory : Nat → State)
    (n : Nat) :
    Evaluator State where
  better a b :=
    a = trajectory n ∧ b = trajectory (n + 1)

theorem every_path_locally_improves
    {State : Type u}
    (trajectory : Nat → State) :
    LocalImprovement (pathEvaluator trajectory) trajectory := by
  intro n
  exact ⟨rfl, rfl⟩

/-- A concrete recurrent path. -/
def toggle : Nat → Bool
  | 0 => false
  | n + 1 => !(toggle n)

theorem toggle_two_step (n : Nat) :
    toggle (n + 2) = toggle n := by
  simp [toggle]

theorem toggle_locally_improves :
    LocalImprovement (pathEvaluator toggle) toggle :=
  every_path_locally_improves toggle

theorem toggle_recurrence :
    toggle 2 = toggle 0 := by
  exact toggle_two_step 0

/--
Local improvement under changing evaluators can coexist with recurrence.
Hence local improvement alone does not imply any strict global order.
-/
theorem no_irreflexive_transitive_global_extension :
    ¬ ∃ global : Evaluator Bool,
        (∀ a, ¬ global.better a a) ∧
        (∀ ⦃a b c⦄, global.better a b → global.better b c → global.better a c) ∧
        CoherentWithGlobal (pathEvaluator toggle) global := by
  rintro ⟨global, hirr, htrans, hcoherent⟩
  have h01 :
      global.better (toggle 0) (toggle 1) :=
    hcoherent 0 _ _ (toggle_locally_improves 0)
  have h12 :
      global.better (toggle 1) (toggle 2) :=
    hcoherent 1 _ _ (toggle_locally_improves 1)
  have h02 := htrans h01 h12
  rw [toggle_recurrence] at h02
  exact hirr (toggle 0) h02

/-- The union of every time-local improvement edge. -/
def LocalEdge
    {State : Type u}
    (evaluators : Nat → Evaluator State) :
    State → State → Prop :=
  fun a b => ∃ n, (evaluators n).better a b

/--
Exact acyclicity condition for admitting one strict transitive global
improvement relation.
-/
def AcyclicLocalUnion
    {State : Type u}
    (evaluators : Nat → Evaluator State) : Prop :=
  ∀ x, ¬ Relation.TransGen (LocalEdge evaluators) x x

/--
Necessary and sufficient boundary:
the changing evaluators admit an irreflexive transitive global extension
exactly when the transitive closure of their union has no cycle.
-/
theorem strict_global_extension_iff_acyclic_local_union
    {State : Type u}
    (evaluators : Nat → Evaluator State) :
    (∃ global : Evaluator State,
        (∀ a, ¬ global.better a a) ∧
        (∀ ⦃a b c⦄,
          global.better a b →
          global.better b c →
          global.better a c) ∧
        CoherentWithGlobal evaluators global) ↔
      AcyclicLocalUnion evaluators := by
  constructor
  · rintro ⟨global, hirr, htrans, hcoherent⟩
    intro x hcycle
    have hlift :
        ∀ {a b},
          Relation.TransGen (LocalEdge evaluators) a b →
          global.better a b := by
      intro a b hab
      induction hab with
      | single hab =>
          rcases hab with ⟨n, hn⟩
          exact hcoherent n _ _ hn
      | tail _ hbc ih =>
          rcases hbc with ⟨n, hn⟩
          exact htrans ih (hcoherent n _ _ hn)
    exact hirr x (hlift hcycle)
  · intro hacyclic
    let global : Evaluator State :=
      ⟨Relation.TransGen (LocalEdge evaluators)⟩
    refine ⟨global, ?_, ?_, ?_⟩
    · intro a
      exact hacyclic a
    · intro a b c hab hbc
      exact hab.trans hbc
    · intro n a b hab
      exact Relation.TransGen.single ⟨n, hab⟩

/--
A common Nat-valued potential is strictly stronger than bare local coherence:
it rules out every cycle in the union of local improvement edges.
-/
theorem commonPotential_implies_acyclic_local_union
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (potential : State → Nat)
    (hpotential : CommonPotential evaluators potential) :
    AcyclicLocalUnion evaluators := by
  intro x hcycle
  have hpath :
      ∀ {a b},
        Relation.TransGen (LocalEdge evaluators) a b →
        potential a < potential b := by
    intro a b hab
    induction hab with
    | single hab =>
        rcases hab with ⟨n, hn⟩
        exact hpotential n _ _ hn
    | tail _ hbc ih =>
        rcases hbc with ⟨n, hn⟩
        exact lt_trans ih (hpotential n _ _ hn)
  exact (lt_irrefl (potential x)) (hpath hcycle)

/-- The strict transitive future generated by all local evaluator edges. -/
def StrictFuture
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (a : State) : Set State :=
  {b | Relation.TransGen (LocalEdge evaluators) a b}

/--
Under acyclicity, traversing one local edge strictly shrinks the remaining
strict future.
-/
theorem strictFuture_ssubset_of_localEdge
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (hacyclic : AcyclicLocalUnion evaluators)
    {a b : State}
    (hab : LocalEdge evaluators a b) :
    StrictFuture evaluators b ⊂ StrictFuture evaluators a := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro x hbx
    exact Relation.TransGen.head hab hbx
  · intro heq
    have hba : b ∈ StrictFuture evaluators a :=
      Relation.TransGen.single hab
    have hbb : b ∉ StrictFuture evaluators b :=
      hacyclic b
    apply hbb
    rw [heq]
    exact hba

/--
On a finite state space, count the strict future in reverse: fewer remaining
reachable states means larger potential.
-/
noncomputable def finiteAcyclicPotential
    {State : Type u}
    [Finite State]
    (evaluators : Nat → Evaluator State)
    (a : State) : Nat :=
  Nat.card State - (StrictFuture evaluators a).ncard

theorem finiteAcyclicPotential_is_common
    {State : Type u}
    [Finite State]
    (evaluators : Nat → Evaluator State)
    (hacyclic : AcyclicLocalUnion evaluators) :
    CommonPotential evaluators (finiteAcyclicPotential evaluators) := by
  intro n a b hab
  have hedge : LocalEdge evaluators a b := ⟨n, hab⟩
  have hstrict :
      StrictFuture evaluators b ⊂ StrictFuture evaluators a :=
    strictFuture_ssubset_of_localEdge evaluators hacyclic hedge
  have hcard :
      (StrictFuture evaluators b).ncard <
        (StrictFuture evaluators a).ncard :=
    Set.ncard_lt_ncard hstrict
  have hle :
      (StrictFuture evaluators a).ncard ≤ Nat.card State :=
    Set.ncard_le_card _
  exact (tsub_lt_tsub_iff_left_of_le hle).2 hcard

/--
Exact finite-state boundary: acyclicity of the local-edge union is equivalent
to existence of a Nat-valued common potential.
-/
theorem finite_acyclic_iff_exists_nat_commonPotential
    {State : Type u}
    [Finite State]
    (evaluators : Nat → Evaluator State) :
    AcyclicLocalUnion evaluators ↔
      ∃ potential : State → Nat,
        CommonPotential evaluators potential := by
  constructor
  · intro hacyclic
    exact ⟨finiteAcyclicPotential evaluators,
      finiteAcyclicPotential_is_common evaluators hacyclic⟩
  · rintro ⟨potential, hpotential⟩
    exact commonPotential_implies_acyclic_local_union
      evaluators potential hpotential

/--
Therefore a common numerical potential always yields a strict transitive global
extension.
-/
theorem commonPotential_gives_strict_global_extension
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (potential : State → Nat)
    (hpotential : CommonPotential evaluators potential) :
    ∃ global : Evaluator State,
      (∀ a, ¬ global.better a a) ∧
      (∀ ⦃a b c⦄,
        global.better a b →
        global.better b c →
        global.better a c) ∧
      CoherentWithGlobal evaluators global := by
  exact
    (strict_global_extension_iff_acyclic_local_union evaluators).2
      (commonPotential_implies_acyclic_local_union
        evaluators potential hpotential)

namespace PotentialStrictnessExample

/--
Every local evaluator uses the same predecessor edge: a version may improve
from n+1 to n. The union is acyclic, but orienting every such edge upward in
Nat would require an impossible infinite strictly decreasing potential.
-/
def predecessorEvaluators (_ : Nat) : Evaluator Nat where
  better a b := a = b + 1

theorem predecessor_localEdge_iff {a b : Nat} :
    LocalEdge predecessorEvaluators a b ↔ a = b + 1 := by
  constructor
  · rintro ⟨n, hn⟩
    simpa [predecessorEvaluators] using hn
  · intro hab
    exact ⟨0, by simpa [predecessorEvaluators] using hab⟩

theorem predecessor_acyclic :
    AcyclicLocalUnion predecessorEvaluators := by
  intro x hcycle
  have hdecreases :
      ∀ {a b},
        Relation.TransGen (LocalEdge predecessorEvaluators) a b →
        b < a := by
    intro a b hab
    induction hab with
    | single hab =>
        have hedge := predecessor_localEdge_iff.mp hab
        omega
    | tail _ hbc ih =>
        have hedge := predecessor_localEdge_iff.mp hbc
        omega
  exact (lt_irrefl x) (hdecreases hcycle)

theorem predecessor_has_no_nat_commonPotential :
    ¬ ∃ potential : Nat → Nat,
        CommonPotential predecessorEvaluators potential := by
  rintro ⟨potential, hpotential⟩
  have hstep : ∀ n, potential (n + 1) < potential n := by
    intro n
    exact hpotential 0 (n + 1) n (by
      simp [predecessorEvaluators])
  have hanti : StrictAnti potential :=
    strictAnti_nat_of_succ_lt hstep
  exact (not_strictAnti_of_wellFoundedLT potential) hanti

/--
The hierarchy is strict on infinite state spaces:
acyclicity (hence existence of a strict global relation) need not admit a
Nat-valued common potential.
-/
theorem acyclicity_strictly_weaker_than_nat_commonPotential :
    AcyclicLocalUnion predecessorEvaluators ∧
    ¬ ∃ potential : Nat → Nat,
        CommonPotential predecessorEvaluators potential :=
  ⟨predecessor_acyclic, predecessor_has_no_nat_commonPotential⟩

end PotentialStrictnessExample

end ChangingEvaluator
end DistinctionSelfReference
