/-ai
A bijection from α to β determines an order isomorphism of power sets by direct image, inverted by the direct image under the inverse bijection. The round trips are the image laws of an equivalence. Inclusion holds in one direction because a member of a direct image comes from a member of the source set, using injectivity, and in the other because the direct image of a subset lands in the direct image.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
import all Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numEquiv_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

variable {α β : Type*}

/-- A bijection `α ≃ β` induces an order-isomorphism `P α ≅ P β` of power-set domains, by direct
image. -/
def setCongr (e : α ≃ β) : Set α ≃o Set β where
  toFun S := e '' S
  invFun T := e.symm '' T
  left_inv := e.symm_image_image
  right_inv := e.symm.symm_image_image
  map_rel_iff' := by
    intro a b
    constructor
    · intro h x hx
      obtain ⟨y, hy, hey⟩ := h ⟨x, hx, rfl⟩
      rwa [e.injective hey] at hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨x, h hx, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise513
