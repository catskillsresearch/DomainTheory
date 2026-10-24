module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_lft

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

/-- Left projection `lft u` (Scott 6.3). -/
def lftFinset (u : Finset (SumToken α β)) : Finset α :=
  Multiset.foldr lftInsert (∅ : Finset α) u.1

omit [DecidableEq β] in

theorem mem_lftFinset {u : Finset (SumToken α β)} {x : α} :
    x ∈ lftFinset u ↔ SumToken.left x ∈ u := by
  unfold lftFinset
  rw [mem_foldr_lft]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hx
    exact ⟨.left x, hx, rfl⟩

omit [DecidableEq β] in


theorem lftFinset.empty : lftFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (Finset.notMem_empty _ ((mem_lftFinset).1 hx))
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem lftFinset.funion (u v : Finset (SumToken α β)) :
    lftFinset (u ∪' v) = lftFinset u ∪' lftFinset v := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ u ∪' v := (mem_lftFinset).1 hx
    rcases mem_funion.mp this with h | h
    · exact mem_funion.mpr (Or.inl ((mem_lftFinset).2 h))
    · exact mem_funion.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact (mem_lftFinset).2 (mem_funion.mpr (Or.inl ((mem_lftFinset).1 h)))
    · exact (mem_lftFinset).2 (mem_funion.mpr (Or.inr ((mem_lftFinset).1 h)))

theorem lftFinset.insert_bot (u : Finset (SumToken α β)) :
    lftFinset (insert (.bot : SumToken α β) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert .bot u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

theorem lftFinset.insert_left (u : Finset (SumToken α β)) (x : α) :
    lftFinset (insert (.left x) u) = insert x (lftFinset u) := by
  ext y
  constructor
  · intro hy
    have : SumToken.left y ∈ insert (.left x) u := (mem_lftFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hy'
      exact Finset.mem_insert.mpr (Or.inl hy')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.left hy')))
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hy')))

theorem lftFinset.insert_right (u : Finset (SumToken α β)) (y : β) :
    lftFinset (insert (.right y) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert (.right y) u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

omit [DecidableEq β] in

theorem lftFinset.mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    lftFinset v ⊆ lftFinset u := by
  intro x hx
  exact (mem_lftFinset).2 (h ((mem_lftFinset).1 hx))

omit [DecidableEq β] in

theorem lftFinset.singleton_bot :
    lftFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ ({.bot} : Finset _) := (mem_lftFinset).1 hx
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

omit [DecidableEq β] in

theorem lftFinset.singleton_left (x : α) :
    lftFinset ({.left x} : Finset (SumToken α β)) = {x} := by
  ext y
  simp only [mem_lftFinset, Finset.mem_singleton]
  exact ⟨SumToken.left.inj, fun h => h ▸ rfl⟩

end InfoSys


end DomainTheory.InformationSystems
