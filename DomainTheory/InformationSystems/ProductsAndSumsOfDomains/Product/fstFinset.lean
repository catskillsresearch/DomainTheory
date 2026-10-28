module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_foldr_fst

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

def fstFinset (u : Finset (ProdToken A B)) : Finset α :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α)
    (u.filter (fun p => p.val.2 = B.bot)).1

theorem mem_fstFinset {u : Finset (ProdToken A B)} {x : α} :
    x ∈ fstFinset A B u ↔ ∃ p ∈ u, p.val.2 = B.bot ∧ p.val.1 = x := by
  unfold fstFinset
  rw [mem_foldr_fst]
  constructor
  · rintro ⟨p, hp, hx⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hx⟩
  · rintro ⟨p, hp, hbot, hx⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hx⟩

theorem fstFinset.empty : fstFinset A B (∅ : Finset (ProdToken A B)) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨_, hp, _, _⟩
    exact False.elim (Finset.notMem_empty _ hp)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem fstFinset.funion (u v : Finset (ProdToken A B)) :
    fstFinset A B (u ∪' v) = fstFinset A B u ∪' fstFinset A B v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hx'⟩
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hx'⟩

theorem fstFinset.insert_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 = B.bot) :
    fstFinset A B (insert p u) = insert p.val.1 (fstFinset A B u) := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hx'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · exact (mem_fstFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hx'.symm⟩
    · rcases (mem_fstFinset A B).1 hx' with ⟨q, hq, hbot, hxq⟩
      exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hxq⟩

theorem fstFinset.insert_not_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 ≠ B.bot) :
    fstFinset A B (insert p u) = fstFinset A B u := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hx'⟩

theorem fstFinset.mono {u v : Finset (ProdToken A B)} (h : v ⊆ u) :
    fstFinset A B v ⊆ fstFinset A B u := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  exact (mem_fstFinset A B).2 ⟨p, h hp, hbot, hx'⟩

theorem fstFinset.singleton_left (p : ProdToken A B) (hp : p.val.2 = B.bot) :
    fstFinset A B {p} = {p.val.1} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, fstFinset.insert_left A B ∅ p hp,
    fstFinset.empty]
  rfl

end InfoSys

end DomainTheory.InformationSystems
