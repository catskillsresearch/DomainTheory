module

public import DomainTheory.DataTypesAsLattices.Lambda.curryFin
public import DomainTheory.DataTypesAsLattices.Lambda.curry2
public import DomainTheory.DataTypesAsLattices.Lambda.curry3
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_2_3

theorem unary {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∃ u, ∀ x, funOf u x = f x :=
  ⟨graph f, fun x => by rw [theorem_1_2.i hf]⟩

theorem binary {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2.app f hfx hfy⟩

theorem ternary {f : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) :
    ∃ u, ∀ x y z, funOf (funOf (funOf u x) y) z = f x y z :=
  ⟨curry3 f hf0 hf1 hf2, curry3.app f hf0 hf1 hf2⟩

end theorem_2_3

theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs :=
  ⟨curryFin f, curryFin.app hf⟩

end DomainTheory.DataTypesAsLattices
