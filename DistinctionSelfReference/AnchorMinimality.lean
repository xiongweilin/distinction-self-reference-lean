import Mathlib.Data.Set.Card
import DistinctionSelfReference.LocalSufficiency

namespace DistinctionSelfReference
namespace AnchorMinimality

open InformationOrder
open LocalSufficiency

universe u v w z

/--
Two observations carry the same deterministic information when each can be
obtained by post-processing the other.
-/
def InfoEquivalent
    {World : Type u}
    {A : Type v}
    {B : Type w}
    (a : World → A)
    (b : World → B) : Prop :=
  Refines a b ∧ Refines b a

theorem infoEquivalent_refl
    {World : Type u}
    {A : Type v}
    (a : World → A) :
    InfoEquivalent a a :=
  ⟨refines_refl a, refines_refl a⟩

theorem infoEquivalent_symm
    {World : Type u}
    {A : Type v}
    {B : Type w}
    {a : World → A}
    {b : World → B}
    (h : InfoEquivalent a b) :
    InfoEquivalent b a :=
  ⟨h.2, h.1⟩

/--
A least sufficient anchor is sufficient for the target commitment and is no
more informative than any other sufficient anchor: every other sufficient
anchor can be post-processed to it.
-/
def LeastSufficient
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    (anchor : World → Anchor)
    (required : World → Choice) : Prop :=
  Sufficient anchor required ∧
  Refines required anchor

/--
The target commitment itself is a canonical least sufficient anchor.
-/
theorem required_is_least_sufficient
    {World : Type u}
    {Choice : Type w}
    (required : World → Choice) :
    LeastSufficient required required :=
  ⟨refines_refl required, refines_refl required⟩

/--
Every sufficient anchor refines every least sufficient anchor.
-/
theorem sufficient_refines_least
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {Other : Type z}
    {anchor : World → Anchor}
    {required : World → Choice}
    {other : World → Other}
    (hleast : LeastSufficient anchor required)
    (hs : Sufficient other required) :
    Refines other anchor :=
  refines_trans hs hleast.2

/--
Every sufficient anchor must retain every distinction that the required
goal-relevant commitment makes.
-/
theorem sufficient_refines_required
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {anchor : World → Anchor}
    {required : World → Choice}
    (hs : Sufficient anchor required) :
    Refines anchor required :=
  hs

/--
Any least sufficient anchor is information-equivalent to the required
commitment itself.
-/
theorem leastSufficient_iff_equivalent_required
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {anchor : World → Anchor}
    {required : World → Choice} :
    LeastSufficient anchor required ↔
      InfoEquivalent anchor required := by
  constructor
  · exact fun hleast => ⟨hleast.1, hleast.2⟩
  · exact fun h => ⟨h.1, h.2⟩

/--
Least sufficient anchors are unique up to deterministic information
equivalence, even when their concrete observation types differ.
-/
theorem leastSufficient_unique_up_to_info
    {World : Type u}
    {A : Type v}
    {B : Type w}
    {Choice : Type z}
    {a : World → A}
    {b : World → B}
    {required : World → Choice}
    (ha : LeastSufficient a required)
    (hb : LeastSufficient b required) :
    InfoEquivalent a b := by
  constructor
  · exact refines_trans ha.1 hb.2
  · exact refines_trans hb.1 ha.2

/--
A sufficient anchor cannot identify two worlds that the target commitment
distinguishes.
-/
theorem sufficient_anchor_separates_required_distinctions
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {anchor : World → Anchor}
    {required : World → Choice}
    (hs : Sufficient anchor required)
    {x y : World}
    (hreq : required x ≠ required y) :
    anchor x ≠ anchor y :=
  distinction_reflects_to_finer hs hreq

/--
For a finite observation alphabet, the required commitment gives the exact
minimal information partition: every sufficient anchor has fibers contained
inside required-commitment fibers, while a least anchor has exactly the same
fibers.
-/
theorem least_anchor_same_fibers_as_required
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {anchor : World → Anchor}
    {required : World → Choice}
    (hleast : LeastSufficient anchor required)
    {x y : World} :
    anchor x = anchor y ↔ required x = required y := by
  rcases (leastSufficient_iff_equivalent_required).1 hleast with ⟨har, hra⟩
  constructor
  · exact equality_preserved_by_postprocessing har
  · exact equality_preserved_by_postprocessing hra

/--
For any sufficient anchor with finitely many actually reachable observations,
the number of reachable goal judgments cannot exceed the number of reachable
anchor observations.
-/
theorem sufficient_anchor_range_card_lower_bound
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {anchor : World → Anchor}
    {required : World → Choice}
    (hs : Sufficient anchor required)
    (hfinite : (Set.range anchor).Finite) :
    (Set.range required).ncard ≤ (Set.range anchor).ncard := by
  rcases hs with ⟨post, hfactor⟩
  rw [hfactor, Set.range_comp]
  exact Set.ncard_image_le hfinite

/--
A least sufficient anchor attains the lower bound exactly: its reachable
observation classes are equinumerous with the reachable goal-judgment classes.
-/
theorem least_anchor_range_card_eq_required
    {World : Type u}
    {Anchor : Type v}
    {Choice : Type w}
    {anchor : World → Anchor}
    {required : World → Choice}
    (hleast : LeastSufficient anchor required)
    (hfinite : (Set.range anchor).Finite) :
    (Set.range anchor).ncard = (Set.range required).ncard := by
  have hreqFinite : (Set.range required).Finite := by
    rcases hleast.1 with ⟨post, hfactor⟩
    rw [hfactor, Set.range_comp]
    exact hfinite.image post
  apply Nat.le_antisymm
  · exact sufficient_anchor_range_card_lower_bound hleast.2 hreqFinite
  · exact sufficient_anchor_range_card_lower_bound hleast.1 hfinite

end AnchorMinimality
end DistinctionSelfReference
