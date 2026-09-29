import Mathlib.Order.OrderIsoNat
import DistinctionSelfReference.InfiniteCapabilityOrder

namespace DistinctionSelfReference
namespace RankedCapability

open CapabilityOrder
open CapabilityDynamics
open InfiniteCapabilityOrder

universe u v

/--
A rank certificate maps every capability profile into an ordered rank and
strictly increases that rank whenever capability strictly grows.
-/
structure RankCertificate
    (Capability : Type u)
    (Rank : Type v)
    [Preorder Rank] where
  rank : Profile Capability → Rank
  strict :
    ∀ {before after},
      StrictGrowth before after →
      rank before < rank after

/--
If the rank order has well-founded greater-than, no capability chain can
strictly improve forever.
-/
theorem noInfiniteStrictGrowth_of_wellFoundedRank
    {Capability : Type u}
    {Rank : Type v}
    [Preorder Rank]
    [WellFoundedGT Rank]
    (R : RankCertificate Capability Rank) :
    NoInfiniteStrictGrowth Capability := by
  rintro ⟨chain, hstrict⟩
  have hrank : StrictMono (fun n => R.rank (chain n)) :=
    strictMono_nat_of_lt_succ (fun n => R.strict (hstrict n))
  exact (not_strictMono_of_wellFoundedGT
    (fun n => R.rank (chain n))) hrank

/--
Conversely, an explicit open-ended strict capability chain rules out every
rank certificate into a WellFoundedGT order.
-/
theorem no_wellFounded_rank_of_infinite_growth
    {Capability : Type u}
    {Rank : Type v}
    [Preorder Rank]
    [WellFoundedGT Rank]
    (hopen :
      ∃ chain : Nat → Profile Capability,
        ∀ n, StrictGrowth (chain n) (chain (n + 1))) :
    ¬ Nonempty (RankCertificate Capability Rank) := by
  rintro ⟨R⟩
  exact (noInfiniteStrictGrowth_of_wellFoundedRank R) hopen

/--
The canonical Nat-capability chain therefore cannot admit a globally
strict-growth-reflecting rank into any WellFoundedGT order.
-/
theorem nat_open_growth_forbids_wellFounded_rank
    {Rank : Type v}
    [Preorder Rank]
    [WellFoundedGT Rank] :
    ¬ Nonempty (RankCertificate Nat Rank) :=
  no_wellFounded_rank_of_infinite_growth nat_has_infinite_strictGrowth

end RankedCapability
end DistinctionSelfReference
