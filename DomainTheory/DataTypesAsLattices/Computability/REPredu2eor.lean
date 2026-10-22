/-ai
The disjunction of two recursively enumerable predicates on a primcodable type is recursively enumerable.

Merge the two partial functions and map the merged result to the unit by a constant computable function. A value in the image comes from one side of the merge, and assertion extracts that side’s predicate as a disjunct. Conversely, either disjunct makes the merged computation defined, so the unit lies in the image.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem REPred.or {α} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∨ q a := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  have hg : Computable₂ fun (_ : α) (_ : Unit) => () :=
    (Computable.const (α := α × Unit) ()).to₂
  refine Partrec.of_eq (hk.map hg) fun a => ?_
  ext
  constructor
  · intro hu
    rw [Part.mem_map_iff] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    have hx' := (H a).1 x hx
    have hpq : p a ∨ q a := by
      cases hx' with
      | inl h =>
        exact Or.inl (Part.mem_assert_iff.1 h).1
      | inr h =>
        exact Or.inr (Part.mem_assert_iff.1 h).1
    exact Part.mem_assert_iff.2 ⟨hpq, Part.mem_some_iff.2 hxu.symm⟩
  · intro hu
    have hpq : p a ∨ q a := (Part.mem_assert_iff.1 hu).1
    have hd : (k a).Dom := (H a).2.mpr <|
      hpq.imp (fun h => ⟨h, trivial⟩) (fun h => ⟨h, trivial⟩)
    rw [Part.mem_map_iff]
    exact ⟨(), ⟨hd, rfl⟩, (Part.mem_some_iff.1 (Part.mem_assert_iff.1 hu).2).symm⟩

end DomainTheory.DataTypesAsLattices
