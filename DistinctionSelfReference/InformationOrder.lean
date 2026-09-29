namespace DistinctionSelfReference
namespace InformationOrder

universe u v w z

/--
A representation fine refines coarse when coarse can be obtained solely by
post-processing fine.
-/
def Refines {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fine : State → Fine) (coarse : State → Coarse) : Prop :=
  ∃ post : Fine → Coarse, coarse = post ∘ fine

theorem refines_refl
    {State : Type u} {Obs : Type v}
    (r : State → Obs) :
    Refines r r := by
  exact ⟨id, rfl⟩

theorem refines_trans
    {State : Type u} {A : Type v} {B : Type w} {C : Type z}
    {a : State → A} {b : State → B} {c : State → C}
    (hab : Refines a b)
    (hbc : Refines b c) :
    Refines a c := by
  rcases hab with ⟨f, rfl⟩
  rcases hbc with ⟨g, rfl⟩
  exact ⟨g ∘ f, rfl⟩

/-- Post-processing cannot create a distinction between states identified by fine. -/
theorem equality_preserved_by_postprocessing
    {State : Type u} {Fine : Type v} {Coarse : Type w}
    {fine : State → Fine} {coarse : State → Coarse}
    (h : Refines fine coarse)
    {x y : State}
    (hxy : fine x = fine y) :
    coarse x = coarse y := by
  rcases h with ⟨post, rfl⟩
  exact congrArg post hxy

/-- Every distinction visible after post-processing was already visible before it. -/
theorem distinction_reflects_to_finer
    {State : Type u} {Fine : Type v} {Coarse : Type w}
    {fine : State → Fine} {coarse : State → Coarse}
    (h : Refines fine coarse)
    {x y : State}
    (hxy : coarse x ≠ coarse y) :
    fine x ≠ fine y := by
  intro hfine
  exact hxy (equality_preserved_by_postprocessing h hfine)

/-- Identity information refines a constant representation. -/
theorem identity_refines_constant
    {State : Type u} {UnitObs : Type v}
    (c : UnitObs) :
    Refines (fun x : State => x) (fun _ : State => c) := by
  exact ⟨fun _ => c, rfl⟩

/-- On Bool, constant information does not refine identity information. -/
theorem constant_not_refine_identity :
    ¬ Refines (fun _ : Bool => Unit.unit) (fun x : Bool => x) := by
  rintro ⟨post, hpost⟩
  have hfalse := congrFun hpost false
  have htrue := congrFun hpost true
  change false = post Unit.unit at hfalse
  change true = post Unit.unit at htrue
  exact Bool.false_eq_true_eq_False (hfalse.trans htrue.symm)

theorem strict_information_loss :
    Refines (fun x : Bool => x) (fun _ : Bool => Unit.unit) ∧
      ¬ Refines (fun _ : Bool => Unit.unit) (fun x : Bool => x) := by
  exact ⟨identity_refines_constant Unit.unit, constant_not_refine_identity⟩

end InformationOrder
end DistinctionSelfReference
