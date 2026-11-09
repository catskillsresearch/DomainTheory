module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mkRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def liftRight (w : Finset β) : Finset (ProdToken A B) :=
  Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) w.1

namespace liftRight

theorem mem_foldr (s : Multiset β) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ y ∈ s, p = mkRight A B y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hy, _⟩
      exact False.elim (by cases hy)
  · intro y t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨z, hz, hp⟩)
      · exact ⟨y, Or.inl rfl, hp⟩
      · exact ⟨z, Or.inr hz, hp⟩
    · rintro ⟨z, hz, hp⟩
      rcases hz with rfl | hz
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, hp⟩

theorem mem {w : Finset β} {p : ProdToken A B} :
    p ∈ liftRight A B w ↔ ∃ y ∈ w, p = mkRight A B y := by
  unfold liftRight
  exact mem_foldr A B w.1 p

theorem fstFinset_eq (w : Finset β) :
    fstFinset A B (liftRight A B w) ⊆ ({A.bot} : Finset α) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  rcases (liftRight.mem A B).1 hp with ⟨y, _, hp'⟩
  subst hp'
  have : x = A.bot := hx'.symm
  exact Finset.mem_singleton.mpr this

theorem sndFinset_eq (w : Finset β) : sndFinset A B (liftRight A B w) = w := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases (liftRight.mem A B).1 hp with ⟨z, hz, hp'⟩
    subst hp'
    exact (show z = y from hy').symm ▸ hz
  · intro hy
    exact (mem_sndFinset A B).2
      ⟨mkRight A B y, (liftRight.mem A B).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

theorem con {w : Finset β} (hw : w ∈ B.Con) :
    ProdCon A B (liftRight A B w) := by
  refine ⟨?_, ?_⟩
  · exact A.con_subset (A.con_sing A.bot) (fstFinset_eq A B w)
  · rw [sndFinset_eq]
    exact hw

end liftRight

end InfoSys

end DomainTheory.InformationSystems
