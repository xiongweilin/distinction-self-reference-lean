import DistinctionSelfReference.LocalSufficiency
import DistinctionSelfReference.OverlapGluing

namespace DistinctionSelfReference
namespace CompositionalSufficiency

open LocalSufficiency
open OverlapGluing

universe u v w x y

/--
A family of local commitment requirements over shared variables. Each local
component sees one observation and constrains only its own scope.
-/
structure LocalRequirement
    (Index : Type u) (World : Type v) (Obs : Type w)
    (Var : Type x) (Value : Type y) where
  scope : Index → Set Var
  observe : Index → World → Obs
  required : Index → World → Var → Value

namespace LocalRequirement

variable
  {Index : Type u} {World : Type v} {Obs : Type w}
  {Var : Type x} {Value : Type y}

/-- The local commitment restricted to the variables actually owned by i. -/
def localRequired
    (R : LocalRequirement Index World Obs Var Value)
    (i : Index) : World → ({x // x ∈ R.scope i} → Value) :=
  fun world x => R.required i world x.1

/-- Every variable is governed by at least one local requirement. -/
def Covers (R : LocalRequirement Index World Obs Var Value) : Prop :=
  ∀ x, ∃ i, x ∈ R.scope i

/-- Local requirements agree on every shared variable, in every world. -/
def Compatible (R : LocalRequirement Index World Obs Var Value) : Prop :=
  ∀ world i j x, x ∈ R.scope i → x ∈ R.scope j →
    R.required i world x = R.required j world x

/-- Each local observation is sufficient for its own scoped commitment. -/
def LocallySufficient
    (R : LocalRequirement Index World Obs Var Value) : Prop :=
  ∀ i, Sufficient (R.observe i) (R.localRequired i)

/-- Collect all local observations into one compositional observation. -/
def combinedObservation
    (R : LocalRequirement Index World Obs Var Value) :
    World → (Index → Obs) :=
  fun world i => R.observe i world

/-- View one world's local requirements as an overlap-gluing patch family. -/
def patchesAt
    (R : LocalRequirement Index World Obs Var Value)
    (world : World) : PatchFamily Index Var Value where
  scope := R.scope
  assign i x := R.required i world x

theorem patchesAt_covers
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers)
    (world : World) :
    (R.patchesAt world).Covers := hcover

theorem patchesAt_compatible
    (R : LocalRequirement Index World Obs Var Value)
    (hcompat : R.Compatible)
    (world : World) :
    (R.patchesAt world).Compatible := by
  intro i j z hzi hzj
  exact hcompat world i j z hzi hzj

/--
Local compatibility is sufficient to glue each world's local commitments into
a global assignment.
-/
theorem each_world_glues
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers)
    (hcompat : R.Compatible)
    (world : World) :
    (R.patchesAt world).asConstraints.GloballySatisfiable := by
  exact (R.patchesAt world).globallySatisfiable_of_covers_of_compatible
    (R.patchesAt_covers hcover world)
    (R.patchesAt_compatible hcompat world)

/-- A fixed covering patch is chosen for each global variable. -/
noncomputable def pickIndex
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers) (z : Var) : Index :=
  Classical.choose (hcover z)

theorem pickIndex_mem
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers) (z : Var) :
    z ∈ R.scope (R.pickIndex hcover z) :=
  Classical.choose_spec (hcover z)

/-- Canonical global commitment assembled using one covering patch per variable. -/
noncomputable def globalRequired
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers) : World → Var → Value :=
  fun world z => R.required (R.pickIndex hcover z) world z

/-- Overlap compatibility makes the canonical global commitment extend every patch. -/
theorem globalRequired_extends
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers)
    (hcompat : R.Compatible)
    (world : World) (i : Index) (z : Var)
    (hz : z ∈ R.scope i) :
    R.globalRequired hcover world z = R.required i world z := by
  unfold globalRequired
  exact hcompat world (R.pickIndex hcover z) i z
    (R.pickIndex_mem hcover z) hz

/--
Local observation sufficiency + cover + overlap agreement compose into one
global commitment that is computable from the vector of local observations
and simultaneously extends every local requirement.
-/
theorem local_sufficiency_glues_to_global
    (R : LocalRequirement Index World Obs Var Value)
    (hcover : R.Covers)
    (hcompat : R.Compatible)
    (hlocal : R.LocallySufficient) :
    Sufficient R.combinedObservation (R.globalRequired hcover) ∧
      ∀ world i z, z ∈ R.scope i →
        R.globalRequired hcover world z = R.required i world z := by
  classical
  constructor
  · let decode : ∀ i, Obs → ({z // z ∈ R.scope i} → Value) :=
      fun i => Classical.choose (hlocal i)
    let post : (Index → Obs) → Var → Value := fun observations z =>
      let i := R.pickIndex hcover z
      decode i (observations i) ⟨z, R.pickIndex_mem hcover z⟩
    refine ⟨post, ?_⟩
    funext world z
    let i := R.pickIndex hcover z
    have hdecode := Classical.choose_spec (hlocal i)
    have hworld := congrFun hdecode world
    have hpoint := congrFun hworld ⟨z, R.pickIndex_mem hcover z⟩
    change R.required i world z =
      decode i (R.observe i world) ⟨z, R.pickIndex_mem hcover z⟩ at hpoint
    exact hpoint
  · intro world i z hz
    exact R.globalRequired_extends hcover hcompat world i z hz

end LocalRequirement
end CompositionalSufficiency
end DistinctionSelfReference
