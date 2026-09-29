import DistinctionSelfReference.FutureDistinction
import DistinctionSelfReference.InformationOrder

namespace DistinctionSelfReference
namespace InformationFutureBridge

open FutureDistinction
open InformationOrder

universe u v

/--
Any summary obtained by post-processing the canonical residual language
identifies every pair of future-indistinguishable histories.
-/
theorem futureEq_implies_equal_summary
    {Alpha : Type u} {Summary : Type v}
    (L : Language Alpha)
    (summary : List Alpha → Summary)
    (hrefine : Refines L.leftQuotient summary)
    {x y : List Alpha}
    (hxy : FutureEq L x y) :
    summary x = summary y := by
  exact equality_preserved_by_postprocessing hrefine hxy

/--
If a post-processed summary still distinguishes two histories, then the
canonical future-state representation distinguished them already.
-/
theorem summary_distinction_implies_not_futureEq
    {Alpha : Type u} {Summary : Type v}
    (L : Language Alpha)
    (summary : List Alpha → Summary)
    (hrefine : Refines L.leftQuotient summary)
    {x y : List Alpha}
    (hxy : summary x ≠ summary y) :
    ¬ FutureEq L x y := by
  exact distinction_reflects_to_finer hrefine hxy

end InformationFutureBridge
end DistinctionSelfReference
