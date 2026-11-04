module

public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxPlus
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxTensor

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_5_4

theorem times {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxTensor a b) :=
  ⟨⟨Icomb_subset_boxTensor ha hb, boxTensor.isRetract ha.out.2 hb.out.2⟩⟩

theorem plus {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxPlus a b) :=
  ⟨⟨Icomb_subset_boxPlus ha hb, boxPlus.isRetract ha.out.2 hb.out.2⟩⟩

end theorem_5_4

theorem theorem_5_4 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxTensor a b) ∧ Closure (boxPlus a b) :=
  ⟨theorem_5_4.times ha hb, theorem_5_4.plus ha hb⟩

end DomainTheory.DataTypesAsLattices
