import Mathlib.Order.WellQuasiOrder
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Preorder.Finite

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

/-- Every archive stage is a Pareto-style antichain. -/
def AntichainArchive
    {Version : Type u}
    [Preorder Version]
    (archive : Nat → Archive Version) : Prop :=
  ∀ n, IsAntichain (· ≤ ·) (archive n)

/--
A WQO forbids an antichain archive from being both monotone and strictly
growing at every single step forever.
-/
theorem wqo_forbids_strict_antichain_growth_every_step
    {Version : Type u}
    [Preorder Version]
    [WellQuasiOrderedLE Version]
    (archive : Nat → Archive Version)
    (hmono : MonotoneArchive archive)
    (hanti : AntichainArchive archive) :
    ¬ ∀ n, StrictArchiveGrowth (archive n) (archive (n + 1)) := by
  intro hstrict
  have hmonotone : Monotone archive :=
    monotone_nat_of_le_succ fun n => (hstrict n).1
  have hex :
      ∀ n, ∃ x,
        x ∈ archive (n + 1) ∧
        x ∉ archive n := by
    intro n
    exact Set.not_subset.mp (hstrict n).2
  choose fresh hnew hnotOld using hex
  rcases wellQuasiOrdered_le fresh with ⟨i, j, hij, hijle⟩
  have hi_j : fresh i ∈ archive j :=
    hmonotone (Nat.succ_le_of_lt hij) (hnew i)
  have hi_succj : fresh i ∈ archive (j + 1) :=
    hmonotone (Nat.le_succ j) hi_j
  have hne : fresh i ≠ fresh j := by
    intro heq
    apply hnotOld j
    rw [← heq]
    exact hi_j
  have heq :=
    (hanti (j + 1)).eq hi_succj (hnew j) hijle
  exact hne heq

/--
Full stabilization theorem for retained Pareto frontiers:
under a WQO, a monotone sequence of antichain archives is eventually constant.
-/
theorem wqo_monotone_antichain_archive_eventually_stabilizes
    {Version : Type u}
    [Preorder Version]
    [WellQuasiOrderedLE Version]
    (archive : Nat → Archive Version)
    (hmono : MonotoneArchive archive)
    (hanti : AntichainArchive archive) :
    ∃ N, ∀ n, N ≤ n → archive n = archive N := by
  have hmonotone : Monotone archive :=
    monotone_nat_of_le_succ hmono
  let total : Set Version := ⋃ n, archive n
  have htotalAnti : IsAntichain (· ≤ ·) total := by
    intro a ha b hb hne hab
    rcases Set.mem_iUnion.mp ha with ⟨i, hai⟩
    rcases Set.mem_iUnion.mp hb with ⟨j, hbj⟩
    let k := max i j
    have haiK : a ∈ archive k :=
      hmonotone (le_max_left i j) hai
    have hbjK : b ∈ archive k :=
      hmonotone (le_max_right i j) hbj
    exact hne ((hanti k).eq haiK hbjK hab)
  have htotalFinite : total.Finite :=
    antichain_frontier_finite total htotalAnti
  have hcover : total ⊆ ⋃ n, archive n := by
    simpa [total]
  rcases Set.finite_subset_iUnion htotalFinite hcover with
    ⟨indices, hindicesFinite, hfiniteCover⟩
  rcases hindicesFinite.exists_le with ⟨N, hN⟩
  have htotalToN : total ⊆ archive N := by
    intro x hx
    have hxCover := hfiniteCover hx
    rcases Set.mem_iUnion.mp hxCover with ⟨i, hxI⟩
    rcases Set.mem_iUnion.mp hxI with ⟨hi, hxi⟩
    exact hmonotone (hN i hi) hxi
  refine ⟨N, ?_⟩
  intro n hn
  apply Set.Subset.antisymm
  · intro x hx
    apply htotalToN
    exact Set.mem_iUnion.mpr ⟨n, hx⟩
  · exact hmonotone hn

/-- The undominated maximal elements of an archive. -/
def ParetoFrontier
    {Version : Type u}
    [Preorder Version]
    (archive : Archive Version) :
    Archive Version :=
  {x | x ∈ archive ∧ ∀ y, y ∈ archive → ¬ x < y}

theorem paretoFrontier_subset
    {Version : Type u}
    [Preorder Version]
    (archive : Archive Version) :
    ParetoFrontier archive ⊆ archive := by
  intro x hx
  exact hx.1

/--
A frontier is dominance-complete for an archive when it lies inside the archive
and every archived point is weakly dominated by some frontier point.
-/
def DominanceComplete
    {Version : Type u}
    [Preorder Version]
    (frontier archive : Archive Version) : Prop :=
  frontier ⊆ archive ∧
  ∀ x, x ∈ archive → ∃ y, y ∈ frontier ∧ x ≤ y

/--
For every finite archive, the undominated Pareto frontier is a complete
dominance summary of the whole archive.
-/
theorem finite_paretoFrontier_dominanceComplete
    {Version : Type u}
    [Preorder Version]
    (archive : Archive Version)
    (hfinite : archive.Finite) :
    DominanceComplete (ParetoFrontier archive) archive := by
  constructor
  · exact paretoFrontier_subset archive
  · intro x hx
    rcases hfinite.exists_le_maximal hx with ⟨y, hxy, hymax⟩
    refine ⟨y, ?_, hxy⟩
    constructor
    · exact hymax.1
    · intro z hz hyz
      exact hyz.not_le (hymax.2 hz hyz.le)

/--
One frontier strictly dominates another when every old frontier point is
strictly improved by some new frontier point.
-/
def StrictFrontierProgress
    {Version : Type u}
    [Preorder Version]
    (old new : Archive Version) : Prop :=
  ∀ x, x ∈ old → ∃ y, y ∈ new ∧ x < y

namespace FrontierReplacementExample

/--
The retained archive contains every natural-number version seen so far.
This archive is monotone and strictly grows forever.
-/
def retained (n : Nat) : Archive Nat :=
  {k | k ≤ n}

theorem retained_monotone :
    MonotoneArchive retained := by
  intro n k hk
  change k ≤ n at hk
  change k ≤ n + 1
  omega

theorem retained_strict_each_step (n : Nat) :
    StrictArchiveGrowth (retained n) (retained (n + 1)) := by
  constructor
  · exact retained_monotone n
  · intro hback
    have hnew : n + 1 ∈ retained (n + 1) := by
      simp [retained]
    have hold := hback hnew
    change n + 1 ≤ n at hold
    omega

def frontier (n : Nat) : Archive Nat :=
  ParetoFrontier (retained n)

/--
At every finite stage the unique Pareto-maximal retained version is the newest
one.
-/
theorem frontier_eq_singleton (n : Nat) :
    frontier n = {n} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxn, hmax⟩
    have hnot : ¬ x < n := hmax n (by simp [retained])
    have hxeq : x = n := by
      omega
    simpa [hxeq]
  · intro hx
    have hxeq : x = n := by
      simpa using hx
    subst x
    constructor
    · simp [retained]
    · intro y hy
      change y ≤ n at hy
      omega

/-- Every recomputed frontier is a singleton antichain. -/
theorem frontier_antichain :
    AntichainArchive frontier := by
  intro n
  rw [frontier_eq_singleton]
  exact IsAntichain.singleton

/--
Each changing singleton frontier still summarizes the complete retained archive
by dominance.
-/
theorem frontier_dominance_complete (n : Nat) :
    DominanceComplete (frontier n) (retained n) := by
  rw [frontier_eq_singleton]
  constructor
  · intro x hx
    have hxeq : x = n := by simpa using hx
    subst x
    simp [retained]
  · intro x hx
    refine ⟨n, by simp, ?_⟩
    exact hx

/--
The frontier is genuinely non-monotone: the old maximal point is removed when
the next strictly better point appears.
-/
theorem frontier_not_subset_next (n : Nat) :
    ¬ frontier n ⊆ frontier (n + 1) := by
  rw [frontier_eq_singleton, frontier_eq_singleton]
  intro h
  have hn : n ∈ ({n} : Set Nat) := by simp
  have hmem := h hn
  simp at hmem

theorem frontier_changes_each_step (n : Nat) :
    frontier n ≠ frontier (n + 1) := by
  intro heq
  exact frontier_not_subset_next n (heq.subset)

/--
Although the frontier set never stabilizes, each new frontier strictly
dominates the preceding one.
-/
theorem frontier_strict_progress_each_step (n : Nat) :
    StrictFrontierProgress (frontier n) (frontier (n + 1)) := by
  intro x hx
  rw [frontier_eq_singleton] at hx
  have hxeq : x = n := by
    simpa using hx
  subst x
  refine ⟨n + 1, ?_, by omega⟩
  rw [frontier_eq_singleton]
  simp

/--
WQO does not force stabilization of a recomputed Pareto frontier.
Even over Nat, the retained archive grows monotonically, every frontier is a
finite antichain, and the frontier can be replaced by a strictly dominating
singleton forever.
-/
theorem wqo_allows_perpetual_frontier_replacement :
    MonotoneArchive retained ∧
    AntichainArchive frontier ∧
    (∀ n, DominanceComplete (frontier n) (retained n)) ∧
    (∀ n, frontier n ≠ frontier (n + 1)) ∧
    (∀ n, StrictFrontierProgress (frontier n) (frontier (n + 1))) := by
  exact ⟨
    retained_monotone,
    frontier_antichain,
    frontier_dominance_complete,
    frontier_changes_each_step,
    frontier_strict_progress_each_step⟩

end FrontierReplacementExample

end ArchiveRSI
end DistinctionSelfReference
