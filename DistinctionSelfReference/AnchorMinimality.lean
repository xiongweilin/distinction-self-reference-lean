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
  ∀ {Other : Type z} (other : World → Other),
    Sufficient other required →
    Refines other anchor

/--
The target commitment itself is a canonical least sufficient anchor.
-/
theorem required_is_least_sufficient
    {World : Type u}
    {Choice : Type w}
    (required : World → Choice) :
    LeastSufficient required required := by
  constructor
  · exact refines_refl required
  · intro Other other hs
    exact hs

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
  · intro hleast
    constructor
    · exact hleast.1
    · exact hleast.2 required (refines_refl required)
  · rintro ⟨har, hra⟩
    constructor
    · exact har
    · intro Other other hs
      exact refines_trans hs hra

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
  · exact hb.2 a ha.1
  · exact ha.2 b hb.1

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

end AnchorMinimality
end DistinctionSelfReference
