module

public import Mathlib.Logic.Equiv.Nat

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_13
public import Mathlib.Algebra.Group.End

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise513
section

def numEquiv : ℕ × ℕ ≃ ℕ where
  toFun := numP
  invFun := unnum
  left_inv := unnum_numP
  right_inv := numP_unnum
end

section
@[simp] theorem numEquiv_apply (p : ℕ × ℕ) : numEquiv p = num p.1 p.2 := rfl
end

section
variable {α β : Type*}

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

def PN_orderIso_PNN : Set ℕ ≃o Set (ℕ × ℕ) := setCongr numEquiv.symm

def PN_orderIso_prod : Set ℕ ≃o Set ℕ × Set ℕ :=
  (setCongr Equiv.natSumNatEquivNat.symm).trans Set.sumEquiv

def PNN_orderIso_prod : Set (ℕ × ℕ) ≃o Set ℕ × Set ℕ :=
  PN_orderIso_PNN.symm.trans PN_orderIso_prod

end

end DomainTheory.NeighbourhoodSystems.Exercise513
end
