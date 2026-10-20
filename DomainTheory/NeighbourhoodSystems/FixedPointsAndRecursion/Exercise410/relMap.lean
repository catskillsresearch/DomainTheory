/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** When `f(a) = a`, the restriction `f' : Dₐ → Dₐ`
(`f'(x) = f(x)`). The codomain condition uses `↑X ⊑ a ⟹ f(↑X) ⊑ f(a) = a`. -/
def relMap (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a) :
    ApproximableMap (relSystem a) (relSystem a) where
  rel X Y := a.mem X ∧ f.rel X Y
  rel_dom := fun h => h.1
  rel_cod := by
    rintro X Y ⟨haX, hXY⟩
    have hVX : V.mem X := a.sub haX
    have hpr : V.principal hVX ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haX hVZ hXZ
    have hmemfX : (f.toElementMap (V.principal hVX)).mem Y := (f.rel_iff_mem_principal hVX).mp hXY
    have hle : f.toElementMap (V.principal hVX) ≤ f.toElementMap a := f.toElementMap_mono hpr
    have : (f.toElementMap a).mem Y := hle Y hmemfX
    rw [ha] at this
    exact this
  master_rel := ⟨a.master_mem, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hXY⟩ ⟨_, hXY'⟩
    exact ⟨haX, f.inter_right hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hXY⟩ hX'X hYY' haX' haY'
    exact ⟨haX', f.mono hXY hX'X hYY' (a.sub haX') (a.sub haY')⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
