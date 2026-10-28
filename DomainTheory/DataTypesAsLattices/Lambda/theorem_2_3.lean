module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.ScottContinuousFin
public import DomainTheory.DataTypesAsLattices.Lambda.curryFin
public import DomainTheory.DataTypesAsLattices.Lambda.nestApplyFin
public import DomainTheory.DataTypesAsLattices.Lambda.curry2
public import DomainTheory.DataTypesAsLattices.Lambda.curry3
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs :=
  ⟨curryFin f, curryFin.app hf⟩

theorem theorem_2_3.unary {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∃ u, ∀ x, funOf u x = f x :=
  ⟨graph f, fun x => by rw [theorem_1_2.i hf]⟩

theorem theorem_2_3.binary {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2.app f hfx hfy⟩

theorem theorem_2_3.ternary {f : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) :
    ∃ u, ∀ x y z, funOf (funOf (funOf u x) y) z = f x y z :=
  ⟨curry3 f hf0 hf1 hf2, curry3.app f hf0 hf1 hf2⟩

end DomainTheory.DataTypesAsLattices
