module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_18 {a : Pomega} (ha : Closure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x := by
  intro k hk
  have hx : x ⊆ funOf a x := by
    have := funOf.monotone_left ha.out.1 x
    rwa [Icomb.app] at this
  have haa : funOf a (funOf a x) ⊆ funOf a x := by
    simp [retract_app ha.out.2]
  exact hk (funOf a x) ⟨hx, haa⟩

namespace eq_5_18

theorem rev (a x : Pomega) :
    funOf a x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.2 (funOf.monotone_right a hy.1 hk)

theorem eq {a : Pomega} (ha : Closure a) (x : Pomega) :
    Vapply a x = funOf a x :=
  subset_antisymm (eq_5_18 ha x) (eq_5_18.rev a x)

end eq_5_18

end DomainTheory.DataTypesAsLattices
