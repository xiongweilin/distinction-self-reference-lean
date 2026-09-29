import Mathlib.Order.WellQuasiOrder

namespace DistinctionSelfReference
namespace ArchiveRSI

universe u

abbrev Archive (Version : Type u) := Set Version

def MonotoneArchive
    {Version : Type u}
    (archive : Nat → Archive Version) : Prop :=
  ∀ n, archive n ⊆ archive (n + 1)

def StrictArchiveGrowth
    {Version : Type u}
    (before after : Archive Version) : Prop :=
  before ⊆ after ∧ ¬ after ⊆ before

/-- Retaining the old archive and inserting a candidate is always monotone. -/
def retainAndInsert
    {Version : Type u}
    (old : Archive Version)
    (candidate : Version) :
    Archive Version :=
  insert candidate old

theorem retainAndInsert_mono
    {Version : Type u}
    (old : Archive Version)
    (candidate : Version) :
    old ⊆ retainAndInsert old candidate := by
  intro x hx
  exact Or.inr hx

namespace BranchingExample

abbrev Version := Sum Bool Nat

/-- One selected branch oscillates forever between two versions. -/
def branchBit : Nat → Bool
  | 0 => false
  | n + 1 => !(branchBit n)

def branch (n : Nat) : Version :=
  Sum.inl (branchBit n)

theorem branchBit_two_step (n : Nat) :
    branchBit (n + 2) = branchBit n := by
  simp [branchBit]

theorem branch_recurrence (n : Nat) :
    branch (n + 2) = branch n := by
  simp [branch, branchBit_two_step]

/--
The archive retains both branch states and also accumulates one fresh off-branch
version at every step.
-/
def archive (n : Nat) : Archive Version :=
  {v |
    match v with
    | Sum.inl _ => True
    | Sum.inr k => k < n}

theorem branch_always_archived (n : Nat) :
    branch n ∈ archive n := by
  simp [archive, branch]

theorem archive_monotone :
    MonotoneArchive archive := by
  intro n v hv
  cases v with
  | inl b =>
      trivial
  | inr k =>
      change k < n at hv
      change k < n + 1
      omega

theorem archive_strict_each_step (n : Nat) :
    StrictArchiveGrowth (archive n) (archive (n + 1)) := by
  constructor
  · exact archive_monotone n
  · intro hback
    have hnew : (Sum.inr n : Version) ∈ archive (n + 1) := by
      change n < n + 1
      omega
    have hold := hback hnew
    change n < n at hold
    omega

/--
A branch may recur forever while the retained archive strictly grows at every
step. Linear recurrence and archive recurrence are therefore distinct notions.
-/
theorem recurrent_branch_with_strict_archive_growth :
    (∀ n, branch (n + 2) = branch n) ∧
    (∀ n, StrictArchiveGrowth (archive n) (archive (n + 1))) :=
  ⟨branch_recurrence, archive_strict_each_step⟩

/-- A branch-level evaluator may see a permanent plateau while the archive grows. -/
def branchScore : Version → Nat
  | Sum.inl _ => 0
  | Sum.inr k => k + 1

theorem branch_score_plateau (n : Nat) :
    branchScore (branch n) = branchScore (branch (n + 1)) := by
  rfl

end BranchingExample

/--
WQO immediately gives the finite-antichain fact needed for Pareto-frontier
archives: every antichain frontier is finite.
-/
theorem antichain_frontier_finite
    {Version : Type u}
    [Preorder Version]
    [WellQuasiOrderedLE Version]
    (frontier : Set Version)
    (hfrontier : IsAntichain (· ≤ ·) frontier) :
    frontier.Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain hfrontier

/--
But WQO does not mean every version sequence stabilizes: it guarantees only a
later comparable pair.
-/
theorem wqo_has_comparable_pair
    {Version : Type u}
    [Preorder Version]
    [WellQuasiOrderedLE Version]
    (versions : Nat → Version) :
    ∃ i j, i < j ∧ versions i ≤ versions j :=
  wellQuasiOrdered_le versions

end ArchiveRSI
end DistinctionSelfReference
